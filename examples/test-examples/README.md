This folder contains tests that ensure that our example applications generate the expected
HTML code.

* Ensure that `uv` is installed: <https://docs.astral.sh/uv/#getting-started>,
* then compile all examples in debug mode,
* then execute:

    ```bash
    ./test.sh

    # OR

    uv sync && uv run pytest --verbose
    ```
