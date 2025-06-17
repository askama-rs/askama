#!/usr/bin/env python3

from time import sleep
from unittest import main, TestCase

from pexpect.popen_spawn import PopenSpawn
from requests import Session

from .common import read, with_server_and_session


class TestWebApps(TestCase):
    @with_server_and_session("warp")
    def test_warp(self, server: PopenSpawn, session: Session):
        server.expect("on http://127.0.0.1:8080", timeout=10.0)
        sleep(0.1)
        with session.get("http://127.0.0.1:8080/", allow_redirects=False) as resp:
            self.assertEqual(resp.status_code, 302)
            self.assertEqual(resp.headers.get("location"), "/en/index.html")
        with session.get("http://127.0.0.1:8080/no/such/path.html") as resp:
            self.assertEqual(resp.status_code, 404)
            self.assertEqual(resp.text, read("404.html"))
        with session.get("http://127.0.0.1:8080/en/index.html") as resp:
            self.assertEqual(resp.status_code, 200)
            self.assertEqual(resp.text, read("en_index.html"))
        with session.get("http://127.0.0.1:8080/en/index.html?name=rinja") as resp:
            self.assertEqual(resp.status_code, 200)
            self.assertEqual(resp.text, read("en_index-rinja.html"))
        with session.get("http://127.0.0.1:8080/en/greet-me.html") as resp:
            self.assertEqual(resp.status_code, 404)
            self.assertEqual(resp.text, read("404.html"))
        with session.get("http://127.0.0.1:8080/en/greet-me.html?name=rinja") as resp:
            self.assertEqual(resp.status_code, 200)
            self.assertEqual(resp.text, read("en_greet-me-rinja.html"))


if __name__ == "__main__":
    main()
