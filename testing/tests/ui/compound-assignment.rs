// Comparison operators cannot be chained, so our parser must reject chained comparisons.

use askama::Template;

#[derive(Template)]
#[template(ext = "txt", source = "{% mut a %}")]
struct MutWithoutOperator1;

#[derive(Template)]
#[template(ext = "txt", source = "{% mut a b %}")]
struct MutWithoutOperator2;

#[derive(Template)]
#[template(ext = "txt", source = "{% mut += b %}")]
struct MutWithoutVariable;

#[derive(Template)]
#[template(ext = "txt", source = "{% mut a @= b %}")]
struct MutWithUnknownOperator;

#[derive(Template)]
#[template(ext = "txt", source = "{% let a += b %}")]
struct LetWithCompoundAssignment;

#[derive(Template)]
#[template(ext = "txt", source = "{% let mut a += b %}")]
struct LetMutWithCompoundAssignment;

#[derive(Template)]
#[template(ext = "txt", source = "{{ a += b }}")]
struct CompoundAssignmentInExpressionAdd;

#[derive(Template)]
#[template(ext = "txt", source = "{{ a |= b }}")]
struct CompoundAssignmentInExpressionOr;

#[derive(Template)]
#[template(ext = "txt", source = "{{ a ^= b }}")]
struct CompoundAssignmentInExpressionXor;

#[derive(Template)]
#[template(ext = "txt", source = "{{ a &= b }}")]
struct CompoundAssignmentInExpressionAnd;

fn main() {}
