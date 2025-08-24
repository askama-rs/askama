use core::fmt;
use std::path::Path;
use std::sync::Arc;

use parser::node::{BlockDef, Macro};
use parser::{Node, Parsed, Span, WithSpan};

use crate::config::Config;
use crate::spans::SourceSpan;
use crate::{CompileError, FileInfo, HashMap};

pub(crate) struct Heritage<'a, 'h> {
    pub(crate) root: &'h Context<'a>,
    pub(crate) blocks: BlockAncestry<'a, 'h>,
}

impl<'a, 'h> Heritage<'a, 'h> {
    pub(crate) fn new(
        mut root: &'h Context<'a>,
        contexts: &'a HashMap<&'a Arc<Path>, Context<'a>>,
    ) -> Self {
        let mut blocks: BlockAncestry<'a, 'h> = root
            .blocks
            .iter()
            .map(|(name, def)| (*name, vec![(root, *def)]))
            .collect();

        while let Some(path) = &root.extends {
            root = &contexts[path];
            for (name, def) in &root.blocks {
                blocks.entry(*name).or_default().push((root, def));
            }
        }

        Self { root, blocks }
    }
}

type BlockAncestry<'a, 'h> = HashMap<&'a str, Vec<(&'h Context<'a>, &'a BlockDef<'a>)>>;

#[derive(Clone)]
pub(crate) struct Context<'a> {
    pub(crate) nodes: &'a [Box<Node<'a>>],
    pub(crate) extends: Option<Arc<Path>>,
    pub(crate) blocks: HashMap<&'a str, &'a BlockDef<'a>>,
    pub(crate) macros: HashMap<&'a str, &'a Macro<'a>>,
    pub(crate) imports: HashMap<&'a str, Arc<Path>>,
    pub(crate) path: Option<&'a Path>,
    pub(crate) parsed: &'a Parsed,
    pub(crate) literal: SourceSpan,
    pub(crate) template_span: proc_macro2::Span,
}

impl<'a> Context<'a> {
    pub(crate) fn empty(parsed: &Parsed, template_span: proc_macro2::Span) -> Context<'_> {
        Context {
            nodes: &[],
            extends: None,
            blocks: HashMap::default(),
            macros: HashMap::default(),
            imports: HashMap::default(),
            path: None,
            parsed,
            literal: SourceSpan::empty(),
            template_span,
        }
    }

    pub(crate) fn new(
        config: &Config,
        path: &'a Path,
        parsed: &'a Parsed,
        literal: SourceSpan,
        template_span: proc_macro2::Span,
        called_blocks: &mut crate::CalledBlocks<'a>,
    ) -> Result<Self, CompileError> {
        let mut extends = None;
        let mut blocks: HashMap<&'a str, &'a WithSpan<BlockDef<'a>>> = HashMap::default();
        let mut macros = HashMap::default();
        let mut nested = vec![parsed.nodes()];
        let mut top = true;

        let mut imports = Vec::new();

        while let Some(nodes) = nested.pop() {
            for n in nodes {
                match &**n {
                    Node::Extends(e) => {
                        ensure_top(top, e.span(), path, parsed, "extends")?;
                        if extends.is_some() {
                            return Err(CompileError::new(
                                "multiple extend blocks found",
                                Some(FileInfo::of(e.span(), path, parsed)),
                            ));
                        }
                        extends = Some(e);
                    }
                    Node::Macro(m) => {
                        ensure_top(top, m.span(), path, parsed, "macro")?;
                        macros.insert(*m.name, &**m);
                    }
                    Node::Import(import) => {
                        ensure_top(top, import.span(), path, parsed, "import")?;
                        imports.push(import);
                    }
                    Node::BlockDef(b) => {
                        let current = Self::file_info_of_inner(b.span(), path, parsed);
                        // This checks if the same block is called in a file.
                        if let Some(prev) = blocks.get(&*b.name) {
                            let prev = Self::file_info_of_inner(prev.span(), path, parsed);
                            eprintln!(
                                "⚠️ {:#}: block `{}` was already called at `{:#}` so the previous one will be ignored",
                                current, &*b.name, prev,
                            );
                        } else if extends.is_none() {
                            called_blocks.check_if_already_called(*b.name, current);
                            called_blocks
                                .called_blocks
                                .entry(*b.name)
                                .or_default()
                                .push(current);
                        } else {
                            called_blocks.unprocessed.push((*b.name, current));
                        }
                        blocks.insert(*b.name, b);
                        nested.push(&b.nodes);
                    }
                    Node::If(i) => {
                        for cond in &i.branches {
                            nested.push(&cond.nodes);
                        }
                    }
                    Node::Loop(l) => {
                        nested.push(&l.body);
                        nested.push(&l.else_nodes);
                    }
                    Node::Match(m) => {
                        for arm in &m.arms {
                            nested.push(&arm.nodes);
                        }
                    }
                    _ => {}
                }
            }
            top = false;
        }

        let blocks = blocks
            .into_iter()
            .map(|(k, v)| (k, &**v))
            .collect::<HashMap<_, _>>();

        let mut ctx = Context {
            nodes: parsed.nodes(),
            extends: None,
            blocks,
            macros,
            imports: HashMap::default(),
            parsed,
            path: Some(path),
            literal,
            template_span,
        };
        if let Some(extends) = extends {
            ctx.extends = Some(config.find_template(
                extends.path,
                Some(path),
                Some(FileInfo::of(extends.span(), path, parsed)),
                Some(ctx.span_for_node(extends.span())),
            )?);
        }
        for import in imports {
            let path = config.find_template(
                import.path,
                Some(path),
                Some(FileInfo::of(import.span(), path, parsed)),
                Some(ctx.span_for_node(import.span())),
            )?;
            ctx.imports.insert(import.scope, path);
        }

        Ok(ctx)
    }

    pub(crate) fn generate_error(&self, msg: impl fmt::Display, node: Span) -> CompileError {
        let file_info = self.file_info_of(node);
        CompileError::new_with_span(msg, file_info, Some(self.span_for_node(node)))
    }

    pub(crate) fn span_for_node(&self, node: Span) -> proc_macro2::Span {
        if proc_macro::is_available()
            && let Some(range) = node.byte_range()
            && let Some(span) = self.literal.content_subspan(range)
        {
            span.resolved_at(self.template_span)
        } else {
            proc_macro2::Span::call_site()
        }
    }

    #[inline]
    fn file_info_of_inner(node: Span, path: &'a Path, parsed: &'a Parsed) -> FileInfo<'a> {
        FileInfo::of(node, path, parsed)
    }

    pub(crate) fn file_info_of(&self, node: Span) -> Option<FileInfo<'a>> {
        self.path
            .map(|path| Self::file_info_of_inner(node, path, self.parsed))
    }

    #[cfg(all(feature = "external-sources", feature = "nightly-spans"))]
    pub(crate) fn resolve_path(&self, path: &str) {
        self.literal.resolve_path(path);
    }
}

fn ensure_top(
    top: bool,
    node: Span,
    path: &Path,
    parsed: &Parsed,
    kind: &str,
) -> Result<(), CompileError> {
    if top {
        Ok(())
    } else {
        Err(CompileError::new(
            format!("`{kind}` blocks are not allowed below top level"),
            Some(FileInfo::of(node, path, parsed)),
        ))
    }
}
