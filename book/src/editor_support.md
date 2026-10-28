# Editor support

Askama doesn't ship editor integrations itself, but there are a few community projects.
They are maintained separately, so they might lag behind new template syntax.

* [tree-sitter-askama](https://github.com/lpnh/tree-sitter-askama) is a
  [tree-sitter](https://tree-sitter.github.io/) grammar for Askama templates,
  which editors with tree-sitter support can use for syntax highlighting.
* [Askama Template Support](https://plugins.jetbrains.com/plugin/16591-askama-template-support)
  adds basic support for Askama templates to IntelliJ-based IDEs.
* [djLint](https://djlint.com/) can lint and format Askama templates with its
  [`askama` profile](https://djlint.com/docs/languages/askama/).

If your editor has none of these, treating your templates as Jinja gets you most of the way,
since Askama's syntax is based on Jinja.
