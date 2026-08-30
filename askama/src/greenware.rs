//! Greenware mode — render-time template interpretation for debug builds.
//!
//! "Clay in dev, stone in prod." A template struct opting in with
//! `#[template(path = "...", greenware = true)]` renders through this
//! interpreter in debug builds when `STONEWARE_GREENWARE=1` is set: the
//! template source is re-read from disk on every render, so edits show up
//! without recompiling. Release builds compile the greenware hook out
//! entirely and always use the fired (compile-time) render path.
//!
//! # Parity rules (load-bearing)
//!
//! The interpreter walks **askama's own parser AST**, so dev and prod cannot
//! disagree about syntax. Where the interpreter does not support a construct
//! the fired renderer supports (macros, `extends`/blocks, `match`, method
//! calls, …), it fails **loudly at render time** naming the construct —
//! it never renders wrong output silently, and it never silently falls back
//! to the compiled render (a silent fallback is indistinguishable from a
//! broken reload).
//!
//! `{% if %}` conditions must evaluate to booleans (matching Rust's rules in
//! fired mode), and rendering `null` is an error (fired mode would not have
//! compiled an `Option` interpolation).
//!
//! # Known dev/prod divergences (documented, not silent)
//!
//! - Custom filters and method calls are unsupported (loud error).
//! - Config-level whitespace defaults (`askama.toml` `whitespace`) are not
//!   applied; explicit `{%- -%}` / `{%~ ~%}` markers are honored exactly.

use std::borrow::ToOwned;
use std::boxed::Box;
use std::collections::HashMap;
use std::error::Error as StdError;
use std::fmt;
use std::path::Path;
use std::string::{String, ToString};
use std::vec::Vec;
use std::{format, vec};

use parser::node::{Cond, Lit, Loop, Node, Whitespace, Ws};
use parser::{Ast, Expr, Num, PathOrIdentifier, Syntax, Target, WithSpan};
use serde_json::Value;

/// An error produced by the greenware interpreter.
///
/// Always loud, always names what failed. Surfaces to the caller as
/// [`crate::Error::Custom`].
#[derive(Debug)]
pub struct GreenwareError(pub String);

impl fmt::Display for GreenwareError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "greenware: {}", self.0)
    }
}

impl StdError for GreenwareError {}

fn err<T>(msg: impl Into<String>) -> Result<T, GreenwareError> {
    Err(GreenwareError(msg.into()))
}

/// The derive-generated hook. Returns `None` when greenware is inactive
/// (env `STONEWARE_GREENWARE` unset), so the compiled render runs.
///
/// Activation re-reads `abs_path` from disk, serializes the template struct
/// to a JSON context, and interprets. Any failure — unreadable source, parse
/// error, unsupported construct, missing field — is a loud `Err`.
pub fn try_render<T: serde::Serialize>(
    original_path: &str,
    abs_path: &str,
    escape_html: bool,
    tmpl: &T,
) -> Option<Result<String, crate::Error>> {
    if !env_active() {
        return None;
    }
    Some(render_greenware(original_path, abs_path, escape_html, tmpl))
}

fn env_active() -> bool {
    matches!(std::env::var("STONEWARE_GREENWARE"), Ok(v) if v == "1")
}

fn render_greenware<T: serde::Serialize>(
    original_path: &str,
    abs_path: &str,
    escape_html: bool,
    tmpl: &T,
) -> Result<String, crate::Error> {
    let inner = || -> Result<String, GreenwareError> {
        if let Ok(spec) = std::env::var("STONEWARE_TEMPLATE_SOURCE") {
            return err(format!(
                "STONEWARE_TEMPLATE_SOURCE='{spec}' is set, but greenware runtime reads \
                 only support the filesystem so far — unset it, or use the fired render"
            ));
        }
        let ctx = serde_json::to_value(tmpl)
            .map_err(|e| GreenwareError(format!("cannot serialize template context: {e}")))?;
        let read = |path: &str, relative_to: &str| -> Result<String, String> {
            // Includes are resolved relative to the including file's directory,
            // mirroring the compile-time resolution closely enough for dev use;
            // template roots are not consulted at runtime.
            let p = Path::new(relative_to)
                .parent()
                .map(|d| d.join(path))
                .unwrap_or_else(|| Path::new(path).to_path_buf());
            std::fs::read_to_string(&p).map_err(|e| format!("{}: {e}", p.display()))
        };
        let src = std::fs::read_to_string(abs_path).map_err(|e| {
            GreenwareError(format!(
                "cannot re-read template '{original_path}' from '{abs_path}': {e}"
            ))
        })?;
        render_str(&src, abs_path, &ctx, escape_html, &read, 0)
    };
    inner().map_err(|e| crate::Error::Custom(Box::new(e)))
}

/// Interpret template source against a JSON context. Public within the
/// crate for tests; `try_render` is the real entry point.
#[doc(hidden)]
pub fn render_str(
    src: &str,
    src_path: &str,
    ctx: &Value,
    escape_html: bool,
    read: &dyn Fn(&str, &str) -> Result<String, String>,
    depth: usize,
) -> Result<String, GreenwareError> {
    if depth > 16 {
        return err("include depth exceeded 16 — cyclic include?");
    }
    let mut source = src.to_owned();
    if source.ends_with('\n') {
        // The compile-time loader pops one trailing newline; match it.
        source.pop();
    }
    let syntax = Syntax::default();
    let ast = Ast::from_str(&source, None, &syntax)
        .map_err(|e| GreenwareError(format!("parse error in '{src_path}': {e}")))?;
    let mut r = Renderer {
        root: ctx,
        scopes: vec![HashMap::new()],
        out: String::new(),
        held_ws: String::new(),
        pending: Whitespace::Preserve,
        escape_html,
        read,
        src_path: src_path.to_owned(),
        depth,
    };
    let flow = r.render_nodes(ast.nodes())?;
    if !matches!(flow, Flow::Normal) {
        return err("break/continue outside of a loop");
    }
    r.flush_held(Whitespace::Preserve);
    Ok(r.out)
}

enum Flow {
    Normal,
    Break,
    Continue,
}

struct Renderer<'a> {
    root: &'a Value,
    scopes: Vec<HashMap<String, Value>>,
    out: String,
    /// Trailing whitespace not yet committed — the next tag's leading
    /// whitespace control decides its fate.
    held_ws: String,
    /// Whitespace control pending from the previous tag's trailing marker,
    /// applied to the next literal's leading whitespace.
    pending: Whitespace,
    escape_html: bool,
    read: &'a dyn Fn(&str, &str) -> Result<String, String>,
    src_path: String,
    depth: usize,
}

fn minimize(ws: &str) -> &'static str {
    if ws.contains('\n') { "\n" } else { " " }
}

impl Renderer<'_> {
    fn flush_held(&mut self, pre: Whitespace) {
        match pre {
            Whitespace::Preserve => {
                let held = std::mem::take(&mut self.held_ws);
                self.out.push_str(&held);
            }
            Whitespace::Suppress => self.held_ws.clear(),
            Whitespace::Minimize => {
                let held = std::mem::take(&mut self.held_ws);
                if !held.is_empty() {
                    self.out.push_str(minimize(&held));
                }
            }
        }
    }

    /// A tag boundary: `pre` is the tag's leading marker (decides held
    /// whitespace), the trailing marker becomes `pending` for what follows.
    fn tag_ws(&mut self, ws: Ws) {
        self.flush_held(ws.0.unwrap_or_default());
        self.pending = ws.1.unwrap_or_default();
    }

    fn emit_lit(&mut self, lit: &Lit<'_>) {
        let lws: &str = &lit.lws;
        let val: &str = &lit.val;
        let rws: &str = &lit.rws;
        let lws_owned: String = match self.pending {
            Whitespace::Preserve => lws.to_owned(),
            Whitespace::Suppress => String::new(),
            Whitespace::Minimize => {
                if lws.is_empty() {
                    String::new()
                } else {
                    minimize(lws).to_owned()
                }
            }
        };
        self.pending = Whitespace::Preserve;
        if val.is_empty() {
            // Whitespace-only literal: everything stays held.
            self.held_ws.push_str(&lws_owned);
            self.held_ws.push_str(rws);
        } else {
            let held = std::mem::take(&mut self.held_ws);
            self.out.push_str(&held);
            self.out.push_str(&lws_owned);
            self.out.push_str(val);
            self.held_ws.push_str(rws);
        }
    }

    fn emit_text(&mut self, text: &str) {
        let held = std::mem::take(&mut self.held_ws);
        self.out.push_str(&held);
        // Note: `pending` is NOT reset here -- a tag's trailing `-`/`~` marker
        // targets the whitespace that follows the tag in source, and that
        // whitespace arrives as the NEXT literal's leading segment, after
        // this tag's own output.
        self.out.push_str(text);
    }

    fn render_nodes(&mut self, nodes: &[Box<Node<'_>>]) -> Result<Flow, GreenwareError> {
        for node in nodes {
            match &**node {
                Node::Lit(lit) => self.emit_lit(lit),
                Node::Comment(c) => self.tag_ws(c.ws),
                Node::Raw(raw) => {
                    self.tag_ws(raw.ws1);
                    self.emit_lit(&raw.lit);
                    self.tag_ws(raw.ws2);
                }
                Node::Expr(ws, expr) => {
                    self.tag_ws(*ws);
                    let (value, safe) = self.eval(expr)?;
                    let text = self.stringify(&value, expr)?;
                    let rendered = if self.escape_html && !safe {
                        html_escape(&text)
                    } else {
                        text
                    };
                    self.emit_text(&rendered);
                }
                Node::Let(l) => {
                    self.tag_ws(l.ws);
                    let parser::node::LetValueOrBlock::Value(val) = &l.val else {
                        return err("`{% let x %}{% endlet %}` blocks are not supported in \
                                    greenware yet — use the fired render");
                    };
                    let (value, _) = self.eval(val)?;
                    self.bind_target(&l.var, value)?;
                }
                Node::If(i) => {
                    let mut taken = false;
                    for (idx, branch) in i.branches.iter().enumerate() {
                        if idx == 0 {
                            self.flush_held(branch.ws.0.unwrap_or_default());
                        }
                        if taken {
                            break;
                        }
                        if self.branch_taken(branch)? {
                            taken = true;
                            self.pending = branch.ws.1.unwrap_or_default();
                            self.scopes.push(HashMap::new());
                            let flow = self.render_nodes(&branch.nodes)?;
                            self.scopes.pop();
                            // The taken branch's output ends at the next
                            // branch tag (if any), else at `{% endif %}`.
                            let end_pre = i
                                .branches
                                .get(idx + 1)
                                .map(|b| b.ws.0.unwrap_or_default())
                                .unwrap_or_else(|| i.ws.0.unwrap_or_default());
                            self.flush_held(end_pre);
                            if !matches!(flow, Flow::Normal) {
                                self.pending = i.ws.1.unwrap_or_default();
                                return Ok(flow);
                            }
                        }
                    }
                    self.pending = i.ws.1.unwrap_or_default();
                }
                Node::Loop(l) => {
                    let flow = self.render_loop(l)?;
                    if let Flow::Break | Flow::Continue = flow {
                        return err("break/continue crossed a loop boundary — interpreter bug");
                    }
                }
                Node::Include(inc) => {
                    self.tag_ws(inc.ws);
                    let src = (self.read)(inc.path, &self.src_path).map_err(|e| {
                        GreenwareError(format!("include '{}' failed: {e}", inc.path))
                    })?;
                    let included_path = Path::new(&self.src_path)
                        .parent()
                        .map(|d| d.join(inc.path))
                        .unwrap_or_else(|| Path::new(inc.path).to_path_buf());
                    // Includes share the enclosing context (root only; fired
                    // includes see the caller's variables too, so pass locals
                    // by flattening the current scopes into the root).
                    let merged = self.merged_context();
                    let rendered = render_str(
                        &src,
                        &included_path.display().to_string(),
                        &merged,
                        self.escape_html,
                        self.read,
                        self.depth + 1,
                    )?;
                    self.emit_text(&rendered);
                }
                Node::Break(ws) => {
                    self.tag_ws(**ws);
                    return Ok(Flow::Break);
                }
                Node::Continue(ws) => {
                    self.tag_ws(**ws);
                    return Ok(Flow::Continue);
                }
                Node::Extends(_) => {
                    return err("`{% extends %}` is not supported in greenware yet — \
                                use the fired render for inheriting templates");
                }
                Node::BlockDef(_) => {
                    return err("`{% block %}` is not supported in greenware yet");
                }
                Node::Match(_) => return err("`{% match %}` is not supported in greenware yet"),
                Node::Macro(_) => return err("`{% macro %}` is not supported in greenware yet"),
                Node::Import(_) => return err("`{% import %}` is not supported in greenware yet"),
                Node::Call(_) => return err("`{% call %}` is not supported in greenware yet"),
                Node::FilterBlock(_) => {
                    return err("`{% filter %}` blocks are not supported in greenware yet");
                }
                Node::Compound(_) | Node::Declare(_) => {
                    return err("compound assignment / declarations are not supported in \
                                greenware yet");
                }
            }
        }
        Ok(Flow::Normal)
    }

    fn render_loop(&mut self, l: &Loop<'_>) -> Result<Flow, GreenwareError> {
        self.flush_held(l.ws1.0.unwrap_or_default());
        let (iter_val, _) = self.eval(&l.iter)?;
        let items: Vec<Value> = match iter_val {
            Value::Array(items) => items,
            other => {
                return err(format!(
                    "cannot iterate over {} in greenware (only arrays)",
                    type_name(&other)
                ));
            }
        };
        // Apply the loop condition filter first so loop.last/length are right.
        let mut kept = Vec::new();
        for item in items {
            let keep = match &l.cond {
                Some(cond) => {
                    self.scopes.push(HashMap::new());
                    self.bind_target(&l.var, item.clone())?;
                    let (v, _) = self.eval(cond)?;
                    self.scopes.pop();
                    as_bool(&v).ok_or_else(|| {
                        GreenwareError("loop `if` condition must be a bool".into())
                    })?
                }
                None => true,
            };
            if keep {
                kept.push(item);
            }
        }
        let n = kept.len();
        let boundary_pre = if l.else_nodes.is_empty() {
            l.ws3.0.unwrap_or_default()
        } else {
            l.ws2.0.unwrap_or_default()
        };
        if n == 0 && !l.else_nodes.is_empty() {
            self.pending = l.ws2.1.unwrap_or_default();
            self.scopes.push(HashMap::new());
            let flow = self.render_nodes(&l.else_nodes)?;
            self.scopes.pop();
            self.flush_held(l.ws3.0.unwrap_or_default());
            self.pending = l.ws3.1.unwrap_or_default();
            return match flow {
                Flow::Normal => Ok(Flow::Normal),
                other => Ok(other),
            };
        }
        'iterations: for (i, item) in kept.into_iter().enumerate() {
            self.pending = l.ws1.1.unwrap_or_default();
            self.scopes.push(HashMap::new());
            self.bind_target(&l.var, item)?;
            self.scopes.last_mut().unwrap().insert(
                "loop".to_owned(),
                serde_json::json!({
                    "index": i + 1,
                    "index0": i,
                    "first": i == 0,
                    "last": i + 1 == n,
                }),
            );
            let flow = self.render_nodes(&l.body)?;
            self.scopes.pop();
            self.flush_held(boundary_pre);
            match flow {
                Flow::Normal | Flow::Continue => {}
                Flow::Break => break 'iterations,
            }
        }
        self.pending = l.ws3.1.unwrap_or_default();
        Ok(Flow::Normal)
    }

    fn branch_taken(&mut self, branch: &Cond<'_>) -> Result<bool, GreenwareError> {
        let Some(cond) = &branch.cond else {
            return Ok(true); // {% else %}
        };
        match &cond.target {
            None => {
                let (v, _) = self.eval(&cond.expr)?;
                as_bool(&v).ok_or_else(|| {
                    GreenwareError(format!(
                        "`if` condition must be a bool, got {} — fired renders require \
                         booleans too",
                        type_name(&v)
                    ))
                })
            }
            Some(target) => {
                // if-let: support Some(name) / None over nullable JSON values.
                let (v, _) = self.eval(&cond.expr)?;
                match target {
                    Target::Tuple(t) => {
                        let (path, subs) = &**t;
                        let last = path.last().map(|c| *c.name).unwrap_or("");
                        if last == "Some" && subs.len() == 1 {
                            if v.is_null() {
                                return Ok(false);
                            }
                            if let Target::Name(name) = &subs[0] {
                                self.scopes
                                    .last_mut()
                                    .unwrap()
                                    .insert((**name).to_owned(), v);
                                return Ok(true);
                            }
                            err("only `Some(binding)` patterns are supported in greenware")
                        } else {
                            err(format!(
                                "unsupported if-let pattern '{last}(..)' in greenware"
                            ))
                        }
                    }
                    Target::Path(p) => {
                        let last = p.last().map(|c| *c.name).unwrap_or("");
                        match last {
                            "None" => Ok(v.is_null()),
                            _ => err(format!("unsupported if-let pattern '{last}' in greenware")),
                        }
                    }
                    _ => err("unsupported if-let pattern in greenware"),
                }
            }
        }
    }

    fn bind_target(&mut self, target: &Target<'_>, value: Value) -> Result<(), GreenwareError> {
        match target {
            Target::Name(name) => {
                self.scopes
                    .last_mut()
                    .unwrap()
                    .insert((**name).to_owned(), value);
                Ok(())
            }
            Target::Placeholder(_) => Ok(()),
            _ => err("only simple `name` bindings are supported in greenware"),
        }
    }

    fn merged_context(&self) -> Value {
        let mut base = self.root.clone();
        if let Value::Object(map) = &mut base {
            for scope in &self.scopes {
                for (k, v) in scope {
                    map.insert(k.clone(), v.clone());
                }
            }
        }
        base
    }

    fn lookup(&self, name: &str) -> Option<Value> {
        for scope in self.scopes.iter().rev() {
            if let Some(v) = scope.get(name) {
                return Some(v.clone());
            }
        }
        self.root.get(name).cloned()
    }

    /// Evaluate an expression. The bool is "safe" (exempt from escaping).
    fn eval(&mut self, expr: &Expr<'_>) -> Result<(Value, bool), GreenwareError> {
        match expr {
            Expr::BoolLit(b) => Ok((Value::Bool(*b), false)),
            Expr::StrLit(s) => Ok((Value::String(unescape_str(s.content)), false)),
            Expr::CharLit(c) => Ok((Value::String(c.content.to_owned()), false)),
            Expr::NumLit(_, num) => match num {
                Num::Int(digits, _) => {
                    let cleaned = digits.replace('_', "");
                    let n: i64 = cleaned.parse().map_err(|_| {
                        GreenwareError(format!("cannot parse integer literal '{digits}'"))
                    })?;
                    Ok((Value::from(n), false))
                }
                Num::Float(digits, _) => {
                    let cleaned = digits.replace('_', "");
                    let n: f64 = cleaned.parse().map_err(|_| {
                        GreenwareError(format!("cannot parse float literal '{digits}'"))
                    })?;
                    Ok((Value::from(n), false))
                }
            },
            Expr::Var(name) => match self.lookup(name) {
                Some(v) => Ok((v, false)),
                None => err(format!(
                    "variable '{name}' not found in template context — is the field \
                     present on the template struct (and Serialize-visible)?"
                )),
            },
            Expr::AssociatedItem(base, item) => {
                let (v, _) = self.eval(base)?;
                let name: &str = &item.name;
                match &v {
                    Value::Object(map) => match map.get(name) {
                        Some(inner) => Ok((inner.clone(), false)),
                        None => err(format!("field '{name}' not found on object")),
                    },
                    Value::Array(items) => match name.parse::<usize>() {
                        Ok(idx) => items.get(idx).cloned().map(|v| (v, false)).ok_or_else(|| {
                            GreenwareError(format!("tuple index {idx} out of bounds"))
                        }),
                        Err(_) => err(format!(
                            "cannot access '.{name}' on an array — method calls are not \
                             supported in greenware"
                        )),
                    },
                    other => err(format!(
                        "cannot access field '{name}' on {}",
                        type_name(other)
                    )),
                }
            }
            Expr::Index(base, idx) => {
                let (v, _) = self.eval(base)?;
                let (i, _) = self.eval(idx)?;
                match (&v, &i) {
                    (Value::Array(items), Value::Number(n)) => {
                        let idx = n.as_u64().ok_or_else(|| {
                            GreenwareError("array index must be a non-negative integer".into())
                        })? as usize;
                        items
                            .get(idx)
                            .cloned()
                            .map(|v| (v, false))
                            .ok_or_else(|| GreenwareError(format!("index {idx} out of bounds")))
                    }
                    (Value::Object(map), Value::String(key)) => map
                        .get(key)
                        .cloned()
                        .map(|v| (v, false))
                        .ok_or_else(|| GreenwareError(format!("key '{key}' not found"))),
                    _ => err("unsupported index operation in greenware"),
                }
            }
            Expr::Group(inner) => self.eval(inner),
            Expr::Unary(op, inner) => {
                let (v, _) = self.eval(inner)?;
                match (*op, &v) {
                    ("!", Value::Bool(b)) => Ok((Value::Bool(!b), false)),
                    ("-", Value::Number(n)) => {
                        if let Some(i) = n.as_i64() {
                            Ok((Value::from(-i), false))
                        } else if let Some(f) = n.as_f64() {
                            Ok((Value::from(-f), false))
                        } else {
                            err("cannot negate this number")
                        }
                    }
                    _ => err(format!("unsupported unary '{op}' on {}", type_name(&v))),
                }
            }
            Expr::BinOp(op) => self.eval_binop(op),
            Expr::Concat(parts) => {
                let mut s = String::new();
                for part in parts {
                    let (v, _) = self.eval(part)?;
                    s.push_str(&self.stringify(&v, part)?);
                }
                Ok((Value::String(s), false))
            }
            Expr::Array(items) => {
                let mut out = Vec::with_capacity(items.len());
                for item in items {
                    out.push(self.eval(item)?.0);
                }
                Ok((Value::Array(out), false))
            }
            Expr::Range(_) => err("ranges are not supported in greenware yet"),
            Expr::IsDefined(name) => Ok((Value::Bool(self.lookup(name).is_some()), false)),
            Expr::IsNotDefined(name) => Ok((Value::Bool(self.lookup(name).is_none()), false)),
            Expr::Filter(f) => self.eval_filter(f),
            Expr::Call(_) => err(
                "method/function calls are not supported in greenware — precompute the \
                 value as a field, or use the fired render",
            ),
            Expr::Path(_) => err("paths/constants are not supported in greenware"),
            other => err(format!(
                "unsupported expression in greenware: {}",
                expr_name(other)
            )),
        }
    }

    fn eval_binop(
        &mut self,
        op: &parser::expr::BinOp<'_>,
    ) -> Result<(Value, bool), GreenwareError> {
        // Short-circuit logic first.
        if op.op == "&&" || op.op == "||" {
            let (l, _) = self.eval(&op.lhs)?;
            let lb =
                as_bool(&l).ok_or_else(|| GreenwareError(format!("'{}' needs bools", op.op)))?;
            if (op.op == "&&" && !lb) || (op.op == "||" && lb) {
                return Ok((Value::Bool(lb), false));
            }
            let (r, _) = self.eval(&op.rhs)?;
            let rb =
                as_bool(&r).ok_or_else(|| GreenwareError(format!("'{}' needs bools", op.op)))?;
            return Ok((Value::Bool(rb), false));
        }
        let (l, _) = self.eval(&op.lhs)?;
        let (r, _) = self.eval(&op.rhs)?;
        let v = match op.op {
            "==" => Value::Bool(loose_eq(&l, &r)),
            "!=" => Value::Bool(!loose_eq(&l, &r)),
            "<" | "<=" | ">" | ">=" => {
                let ord = compare(&l, &r).ok_or_else(|| {
                    GreenwareError(format!(
                        "cannot compare {} with {}",
                        type_name(&l),
                        type_name(&r)
                    ))
                })?;
                Value::Bool(match op.op {
                    "<" => ord.is_lt(),
                    "<=" => ord.is_le(),
                    ">" => ord.is_gt(),
                    _ => ord.is_ge(),
                })
            }
            "+" | "-" | "*" | "/" | "%" => arithmetic(op.op, &l, &r)?,
            other => return err(format!("unsupported operator '{other}' in greenware")),
        };
        Ok((v, false))
    }

    fn eval_filter(
        &mut self,
        f: &parser::expr::Filter<'_>,
    ) -> Result<(Value, bool), GreenwareError> {
        let name = match &f.name {
            PathOrIdentifier::Identifier(id) => **id,
            PathOrIdentifier::Path(_) => {
                return err("path-qualified filters are not supported in greenware");
            }
        };
        let Some(recv) = f.arguments.first() else {
            return err(format!("filter '{name}' has no receiver"));
        };
        let (v, safe) = self.eval(recv)?;
        match name {
            "safe" => Ok((v, true)),
            "escape" | "e" => {
                let s = self.stringify(&v, recv)?;
                Ok((Value::String(html_escape(&s)), true))
            }
            "upper" | "uppercase" => {
                let s = self.stringify(&v, recv)?;
                Ok((Value::String(s.to_uppercase()), safe))
            }
            "lower" | "lowercase" => {
                let s = self.stringify(&v, recv)?;
                Ok((Value::String(s.to_lowercase()), safe))
            }
            "trim" => {
                let s = self.stringify(&v, recv)?;
                Ok((Value::String(s.trim().to_owned()), safe))
            }
            "capitalize" => {
                let s = self.stringify(&v, recv)?;
                let mut chars = s.chars();
                let cap = match chars.next() {
                    Some(c) => {
                        c.to_uppercase().collect::<String>() + &chars.as_str().to_lowercase()
                    }
                    None => String::new(),
                };
                Ok((Value::String(cap), safe))
            }
            "join" => {
                let sep = match f.arguments.get(1) {
                    Some(arg) => {
                        let (s, _) = self.eval(arg)?;
                        match s {
                            Value::String(s) => s,
                            other => {
                                return err(format!(
                                    "join separator must be a string, got {}",
                                    type_name(&other)
                                ));
                            }
                        }
                    }
                    None => String::new(),
                };
                let Value::Array(items) = &v else {
                    return err("join needs an array receiver");
                };
                let mut parts = Vec::with_capacity(items.len());
                for item in items {
                    parts.push(self.stringify(item, recv)?);
                }
                Ok((Value::String(parts.join(&sep)), safe))
            }
            other => err(format!(
                "filter '{other}' is not supported in greenware — supported: safe, escape, \
                 e, upper, lower, trim, capitalize, join"
            )),
        }
    }

    fn stringify(
        &self,
        v: &Value,
        _at: &WithSpan<Box<Expr<'_>>>,
    ) -> Result<String, GreenwareError> {
        match v {
            Value::String(s) => Ok(s.clone()),
            Value::Number(n) => Ok(n.to_string()),
            Value::Bool(b) => Ok(b.to_string()),
            Value::Null => err(
                "cannot render a null/None value — guard it with `{% if let Some(x) %}` \
                 (the fired render would not have compiled this either)",
            ),
            Value::Array(_) | Value::Object(_) => err(
                "cannot render an array/object directly — the fired render would not have \
                 compiled this either",
            ),
        }
    }
}

fn type_name(v: &Value) -> &'static str {
    match v {
        Value::Null => "null",
        Value::Bool(_) => "bool",
        Value::Number(_) => "number",
        Value::String(_) => "string",
        Value::Array(_) => "array",
        Value::Object(_) => "object",
    }
}

fn expr_name(e: &Expr<'_>) -> &'static str {
    match e {
        Expr::Tuple(_) => "tuple",
        Expr::Struct(_) => "struct literal",
        Expr::RustMacro(..) => "rust macro",
        Expr::Try(_) => "`?` operator",
        Expr::As(..) => "`as` cast",
        Expr::ArrayRepeat(..) => "array repeat",
        Expr::LetCond(_) => "let-condition",
        _ => "expression",
    }
}

fn as_bool(v: &Value) -> Option<bool> {
    match v {
        Value::Bool(b) => Some(*b),
        _ => None,
    }
}

fn loose_eq(l: &Value, r: &Value) -> bool {
    // Numeric equality across int/float representations (mirrors the fired
    // renderer, where 3 == 3.0 compiles to a numeric comparison).
    if let (Value::Number(a), Value::Number(b)) = (l, r) {
        return match (a.as_f64(), b.as_f64()) {
            (Some(x), Some(y)) => x == y,
            _ => a == b,
        };
    }
    l == r
}

fn compare(l: &Value, r: &Value) -> Option<std::cmp::Ordering> {
    match (l, r) {
        (Value::Number(a), Value::Number(b)) => a.as_f64()?.partial_cmp(&b.as_f64()?),
        (Value::String(a), Value::String(b)) => Some(a.cmp(b)),
        _ => None,
    }
}

fn arithmetic(op: &str, l: &Value, r: &Value) -> Result<Value, GreenwareError> {
    let (Value::Number(a), Value::Number(b)) = (l, r) else {
        return err(format!(
            "'{op}' needs numbers, got {} and {}",
            type_name(l),
            type_name(r)
        ));
    };
    if let (Some(x), Some(y)) = (a.as_i64(), b.as_i64()) {
        let v = match op {
            "+" => x.checked_add(y),
            "-" => x.checked_sub(y),
            "*" => x.checked_mul(y),
            "/" => x.checked_div(y),
            "%" => x.checked_rem(y),
            _ => None,
        };
        return match v {
            Some(v) => Ok(Value::from(v)),
            None => err(format!("integer arithmetic error in '{op}'")),
        };
    }
    let (Some(x), Some(y)) = (a.as_f64(), b.as_f64()) else {
        return err("unrepresentable numbers in arithmetic");
    };
    let v = match op {
        "+" => x + y,
        "-" => x - y,
        "*" => x * y,
        "/" => x / y,
        "%" => x % y,
        _ => unreachable!(),
    };
    Ok(Value::from(v))
}

fn html_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '<' => out.push_str("&#60;"),
            '>' => out.push_str("&#62;"),
            '&' => out.push_str("&#38;"),
            '"' => out.push_str("&#34;"),
            '\'' => out.push_str("&#39;"),
            c => out.push(c),
        }
    }
    out
}

/// Minimal string-literal unescaping for template string literals.
fn unescape_str(content: &str) -> String {
    let mut out = String::with_capacity(content.len());
    let mut chars = content.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some('r') => out.push('\r'),
            Some('\\') => out.push('\\'),
            Some('"') => out.push('"'),
            Some('\'') => out.push('\''),
            Some('0') => out.push('\0'),
            Some(other) => {
                out.push('\\');
                out.push(other);
            }
            None => out.push('\\'),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn no_include(_: &str, _: &str) -> Result<String, String> {
        Err("no includes in this test".into())
    }

    fn render(src: &str, ctx: Value) -> Result<String, GreenwareError> {
        render_str(src, "test.html", &ctx, true, &no_include, 0)
    }

    #[test]
    fn literals_and_interpolation() {
        let out = render(
            "Hello {{ name }}, you are {{ age }}.",
            serde_json::json!({"name": "Mark", "age": 40}),
        )
        .unwrap();
        assert_eq!(out, "Hello Mark, you are 40.");
    }

    #[test]
    fn html_escaping_default_and_safe() {
        let ctx = serde_json::json!({"x": "<b>&'\"</b>"});
        let out = render("{{ x }}", ctx.clone()).unwrap();
        assert_eq!(out, "&#60;b&#62;&#38;&#39;&#34;&#60;/b&#62;");
        let out = render("{{ x|safe }}", ctx).unwrap();
        assert_eq!(out, "<b>&'\"</b>");
    }

    #[test]
    fn no_escaping_for_txt_templates() {
        let out = render_str(
            "{{ x }}",
            "test.txt",
            &serde_json::json!({"x": "<b>"}),
            false,
            &no_include,
            0,
        )
        .unwrap();
        assert_eq!(out, "<b>");
    }

    #[test]
    fn field_access_and_tuple_index() {
        let ctx = serde_json::json!({"user": {"name": "Ada"}, "pair": ["a", "b"]});
        assert_eq!(render("{{ user.name }}", ctx.clone()).unwrap(), "Ada");
        assert_eq!(render("{{ pair.1 }}", ctx).unwrap(), "b");
    }

    #[test]
    fn if_elif_else_and_strict_bools() {
        let src = "{% if a %}A{% elif b %}B{% else %}C{% endif %}";
        let json = |a: bool, b: bool| serde_json::json!({"a": a, "b": b});
        assert_eq!(render(src, json(true, false)).unwrap(), "A");
        assert_eq!(render(src, json(false, true)).unwrap(), "B");
        assert_eq!(render(src, json(false, false)).unwrap(), "C");
        // Non-bool condition is a loud error, matching fired-mode rules.
        let err = render("{% if x %}y{% endif %}", serde_json::json!({"x": "s"})).unwrap_err();
        assert!(err.0.contains("must be a bool"), "got: {}", err.0);
    }

    #[test]
    fn if_let_some_and_none() {
        let src = "{% if let Some(n) = name %}hi {{ n }}{% else %}anon{% endif %}";
        assert_eq!(
            render(src, serde_json::json!({"name": "Vex"})).unwrap(),
            "hi Vex"
        );
        assert_eq!(
            render(src, serde_json::json!({"name": null})).unwrap(),
            "anon"
        );
    }

    #[test]
    fn for_loop_with_loop_vars_filter_else() {
        let src = "{% for x in items %}{{ loop.index }}:{{ x }}{% if !loop.last %},{% endif %}{% endfor %}";
        let out = render(src, serde_json::json!({"items": ["a", "b", "c"]})).unwrap();
        assert_eq!(out, "1:a,2:b,3:c");

        let src = "{% for n in nums if n > 1 %}{{ n }}{% endfor %}";
        let out = render(src, serde_json::json!({"nums": [1, 2, 3]})).unwrap();
        assert_eq!(out, "23");

        let src = "{% for x in items %}{{ x }}{% else %}empty{% endfor %}";
        let out = render(src, serde_json::json!({"items": []})).unwrap();
        assert_eq!(out, "empty");
    }

    #[test]
    fn break_and_continue() {
        let src = "{% for n in nums %}{% if n == 3 %}{% break %}{% endif %}{{ n }}{% endfor %}";
        assert_eq!(
            render(src, serde_json::json!({"nums": [1,2,3,4]})).unwrap(),
            "12"
        );
        let src = "{% for n in nums %}{% if n == 2 %}{% continue %}{% endif %}{{ n }}{% endfor %}";
        assert_eq!(
            render(src, serde_json::json!({"nums": [1,2,3]})).unwrap(),
            "13"
        );
    }

    #[test]
    fn let_bindings_and_arithmetic() {
        let src = "{% let total = a + b * 2 %}{{ total }}";
        assert_eq!(
            render(src, serde_json::json!({"a": 1, "b": 3})).unwrap(),
            "7"
        );
    }

    #[test]
    fn whitespace_control() {
        let ctx = serde_json::json!({"x": "v"});
        assert_eq!(render("a  {{- x -}}  b", ctx.clone()).unwrap(), "avb");
        assert_eq!(render("a  {{ x }}  b", ctx.clone()).unwrap(), "a  v  b");
        assert_eq!(render("a\n {{~ x ~}} \nb", ctx.clone()).unwrap(), "a\nv\nb");
        assert_eq!(
            render(
                "a {%- if t %} y {%- endif %}",
                serde_json::json!({"t": true})
            )
            .unwrap(),
            "a y"
        );
    }

    #[test]
    fn filters() {
        let ctx = serde_json::json!({"s": "  Mixed Case  ", "list": ["x", "y"]});
        assert_eq!(
            render("{{ s|trim|upper }}", ctx.clone()).unwrap(),
            "MIXED CASE"
        );
        assert_eq!(
            render("{{ s|trim|lower }}", ctx.clone()).unwrap(),
            "mixed case"
        );
        assert_eq!(
            render("{{ list|join(\", \") }}", ctx.clone()).unwrap(),
            "x, y"
        );
        let err = render("{{ s|nonsense }}", ctx).unwrap_err();
        assert!(err.0.contains("filter 'nonsense'"), "got: {}", err.0);
    }

    #[test]
    fn include_shares_context() {
        let read = |path: &str, _from: &str| -> Result<String, String> {
            match path {
                "part.html" => Ok("[{{ name }}]".to_owned()),
                other => Err(format!("unknown include '{other}'")),
            }
        };
        let out = render_str(
            "pre {% include \"part.html\" %} post",
            "test.html",
            &serde_json::json!({"name": "Vex"}),
            true,
            &read,
            0,
        )
        .unwrap();
        assert_eq!(out, "pre [Vex] post");
    }

    #[test]
    fn unsupported_constructs_fail_loudly() {
        let err = render("{% match x %}{% endmatch %}", serde_json::json!({})).unwrap_err();
        assert!(err.0.contains("match"), "got: {}", err.0);
        let err = render("{{ x.method() }}", serde_json::json!({"x": {}})).unwrap_err();
        assert!(err.0.contains("call"), "got: {}", err.0);
    }

    #[test]
    fn null_and_missing_are_loud() {
        let err = render("{{ x }}", serde_json::json!({"x": null})).unwrap_err();
        assert!(err.0.contains("null"), "got: {}", err.0);
        let err = render("{{ ghost }}", serde_json::json!({})).unwrap_err();
        assert!(err.0.contains("'ghost' not found"), "got: {}", err.0);
    }

    #[test]
    fn comparisons_and_logic() {
        let src = "{% if a > 1 && b == \"x\" %}yes{% else %}no{% endif %}";
        assert_eq!(
            render(src, serde_json::json!({"a": 2, "b": "x"})).unwrap(),
            "yes"
        );
        assert_eq!(
            render(src, serde_json::json!({"a": 1, "b": "x"})).unwrap(),
            "no"
        );
        // int/float numeric equality (the serde_json PartialEq trap).
        assert_eq!(
            render(
                "{% if n == 3 %}eq{% endif %}",
                serde_json::json!({"n": 3.0})
            )
            .unwrap(),
            "eq"
        );
    }

    #[test]
    fn defined_checks() {
        let src = "{% if x is defined %}has{% else %}no{% endif %}";
        assert_eq!(render(src, serde_json::json!({"x": 1})).unwrap(), "has");
        assert_eq!(render(src, serde_json::json!({})).unwrap(), "no");
    }
}
