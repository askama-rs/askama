#!/bin/bash

set -euo pipefail

if ! which uv > /dev/null; then
    echo 'Please install `uv` first: <https://docs.astral.sh/uv/#getting-started>'
    exit 1
fi > /dev/stderr

cd "$(dirname "$0")"
uv sync
exec uv run pytest --verbose
