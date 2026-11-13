#!/usr/bin/env python3
"""Build dist/majority-trees.html: the whole site in one self-contained file.

Usage (from the site folder):

    python3 -B tools/build_standalone.py

The stylesheet and every script are inlined, so the file can be uploaded to
any web host or opened directly from disk. Standard library only.
"""
import argparse
import hashlib
import re
from pathlib import Path

SITE = Path(__file__).resolve().parent.parent
SCRIPTS = ("assets/tree-model.js", "assets/circuit-input.js", "assets/tree-draw.js", "assets/app.js", "assets/compiler.js")


def inline_script(code):
    # Never let the inlined code close the surrounding <script> element.
    return "<script>\n" + code.replace("</", "<\\/") + "\n</script>"


# For the claude.ai artifact viewer: it supplies <html>, <head> and <body>, and
# its sandbox blocks downloads, so the download and share controls are hidden.
ARTIFACT_CSS = ".g-downloads, .cx-download-block, #cx-share-btn, #cx-share { display: none !important; }"


def artifact_body(html):
    head = re.search(r"<head>(.*)</head>", html, re.S).group(1)
    body = re.search(r"<body>(.*)</body>", html, re.S).group(1)
    title = re.search(r"<title>.*?</title>", head, re.S).group(0)
    scripts = re.findall(r"<script>.*?</script>", head, re.S)
    style = re.search(r"<style>.*?</style>", head, re.S).group(0)
    return "\n".join([title] + scripts + [style, "<style>" + ARTIFACT_CSS + "</style>", body])


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--artifact", help="also write a body-only version for the claude.ai artifact viewer")
    args = ap.parse_args()
    html = (SITE / "index.html").read_text(encoding="utf-8")
    css = (SITE / "assets" / "style.css").read_text(encoding="utf-8")
    replacements = [('<link rel="stylesheet" href="assets/style.css">', "<style>\n" + css + "\n</style>")]
    for rel in SCRIPTS:
        replacements.append((f'<script src="{rel}"></script>', inline_script((SITE / rel).read_text(encoding="utf-8"))))
    for old, new in replacements:
        if html.count(old) != 1:
            raise SystemExit(f"expected exactly one occurrence of {old!r} in index.html")
        html = html.replace(old, new)
    leftovers = re.findall(r'(?:src|href)="assets/', html)
    if leftovers:
        raise SystemExit(f"unresolved local references: {leftovers}")
    out = SITE / "dist" / "majority-trees.html"
    out.parent.mkdir(exist_ok=True)
    out.write_text(html, encoding="utf-8")
    digest = hashlib.sha256(html.encode("utf-8")).hexdigest()
    print(f"{out.relative_to(SITE)}  {len(html.encode('utf-8'))} bytes  sha256 {digest}")
    if args.artifact:
        Path(args.artifact).write_text(artifact_body(html), encoding="utf-8")
        print(f"artifact body: {args.artifact}")


if __name__ == "__main__":
    main()
