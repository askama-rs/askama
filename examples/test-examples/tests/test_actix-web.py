#!/usr/bin/env python3

from time import sleep
from unittest import main, TestCase

from pexpect.popen_spawn import PopenSpawn
from requests import Session

from .common import read, with_server_and_session


class TestActixWeb(TestCase):
    @with_server_and_session("actix-web")
    def test_actix_web(self, server: PopenSpawn, session: Session):
        server.expect("listening on: 127.0.0.1:8080", timeout=10.0)
        sleep(0.1)
        with session.get("http://127.0.0.1:8080/", allow_redirects=False) as resp:
            self.assertEqual(resp.status_code, 302)
            self.assertEqual(
                resp.headers.get("location"),
                "http://127.0.0.1:8080/en/index.html",
            )
        with session.get("http://127.0.0.1:8080/no/such/path.html") as resp:
            self.assertEqual(resp.status_code, 404)
            self.assertEqual(resp.text, read("actix-web/no_such_path.html"))
        with session.get("http://127.0.0.1:8080/en/index.html") as resp:
            self.assertEqual(resp.status_code, 200)
            self.assertEqual(resp.text, read("actix-web/en_index.html"))
        with session.get("http://127.0.0.1:8080/en/index.html?name=rinja") as resp:
            self.assertEqual(resp.status_code, 200)
            self.assertEqual(resp.text, read("actix-web/en_index-rinja.html"))
        with session.get("http://127.0.0.1:8080/en/greet-me.html") as resp:
            self.assertEqual(resp.status_code, 400)
            self.assertEqual(resp.text, read("actix-web/en_greet-me.html"))
        with session.get("http://127.0.0.1:8080/en/greet-me.html?name=rinja") as resp:
            self.assertEqual(resp.status_code, 200)
            self.assertEqual(resp.text, read("actix-web/en_greet-me-rinja.html"))


if __name__ == "__main__":
    main()
