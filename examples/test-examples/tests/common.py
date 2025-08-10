from functools import wraps
from pathlib import Path
from signal import SIGINT

from pexpect.popen_spawn import PopenSpawn
from requests import Session


__all__ = ["with_server_and_session", "read"]


def with_server_and_session(name):
    def inner(fn):
        @wraps(fn)
        def wrapped(self):
            server = PopenSpawn(
                ["cargo", "+stable", "run"],
                timeout=30.0,
                cwd=Path(__file__).parent.parent.parent / f"{name}-app",
                encoding="UTF-8",
            )
            try:
                with Session() as session:
                    return fn(self, server, session)
            finally:
                server.sendeof()
                server.kill(SIGINT)
                server.wait()

        return wrapped

    return inner


def read(name):
    with open(Path(__file__).parent / "expected" / name) as f:
        return f.read()
