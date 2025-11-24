#!/usr/bin/env python3

from io import StringIO
from os import PathLike
from pathlib import Path
from shutil import which
from subprocess import DEVNULL, run
from sys import stderr
from tempfile import TemporaryDirectory


SIDEBAR = r"""
    <nav id="sidebar" class="sidebar" aria-label="Table of contents">
        <div class="sidebar-scrollbox" style="display:flex; flex-direction:column">
            <div id="toc" style="flex:1">{{#toc}}{{/toc}}</div>
            <div id="ethical-ad-placement" class="ethical-sidebar" data-ea-publisher="readthedocs" data-ea-type="image"></div>
            <readthedocs-flyout></readthedocs-flyout>
        </div>
        <div id="sidebar-resize-handle" class="sidebar-resize-handle">
            <div class="sidebar-resize-indicator"></div>
        </div>
        <script>
            (function () {
                const active = document.querySelector(`#toc [href="${"{{path}}".replace(".md", ".html")}"]`);
                if (active) {
                    active.classList.add("active");
                }
            })();
            document.addEventListener("DOMContentLoaded", function insertStyle () {
                const elem = customElements.get("readthedocs-flyout");
                if (elem) {
                    elem.styles.insertRule(`
                        .container {
                            position: unset !important;
                            max-width: unset !important;
                            width: unset !important;
                            height: unset !important;
                            max-height: unset !important;
                        }
                    `);
                    elem.styles.insertRule(`
                        dl:has(#flyout-search-form) {
                            display: none !important;
                        }
                    `);
                } else {
                    setTimeout(insertStyle, 50);
                }
            });
        </script>
    </nav>
"""


def update_theme(target: PathLike) -> None:
    mdbook = which("mdbook")
    if not mdbook:
        raise Exception("mdbook not installed?")

    with TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        run([mdbook, "--version"], stdin=DEVNULL, cwd=tmp, timeout=5, check=True)
        run(
            [mdbook, "init", "--theme", "--force"],
            stdin=DEVNULL,
            stdout=DEVNULL,
            stderr=stderr,
            cwd=tmp,
            timeout=5,
            check=True,
        )
        with open(tmp / "theme" / "index.hbs", "rt") as f:
            input_f = StringIO(f.read())

    output_f = StringIO()

    state = "before-sidebar"
    for line in input_f:
        match state:
            case "before-sidebar" if '<nav id="mdbook-sidebar"' in line:
                line = SIDEBAR
                state = "in-sidebar"
            case "in-sidebar":
                if "</nav>" in line:
                    state = "after-sidebar"
                line = ""
        output_f.write(line)

    if state != "after-sidebar":
        raise Exception(f"state={state!r}")

    output_f.seek(0, 0)
    with open(target, "wt") as f:
        print(output_f.read(), end="", file=f)


if __name__ == "__main__":
    update_theme(Path(__file__).absolute().parent / "theme" / "index.hbs")
