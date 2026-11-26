#!/usr/bin/env python3
"""A1: add `use alloc::List;` to every Memobits source that uses List<..>.

Handles .mb files, Memobits sources embedded in Rust string literals (the
import is prepended on the first line, so line numbers stay the same) and
fenced ```memobits/```mb/``` blocks in Markdown that mention `List<`.

Usage: migrate_alloc_list.py [--check] PATH...   (prints literals it skipped)
"""
import re, sys, os

IMPORT = "use alloc::List;"
USES = re.compile(r"\bList<")
ITEM = re.compile(r"\s*(pub\s|fn\s|type\s|use\s|interface\s|extend\s|test\s+fn|extern\s|//)")
CHAR = re.compile(r"'(\\.[^']*|[^'\\])'")
skipped = []
changed = 0


def rust_literals(src):
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if src.startswith("//", i):
            j = src.find("\n", i); i = n if j < 0 else j
        elif src.startswith("/*", i):
            j = src.find("*/", i + 2); i = n if j < 0 else j + 2
        elif c == "r" and re.match(r'r#*"', src[i:i + 10]) and (i == 0 or not (src[i-1].isalnum() or src[i-1] == "_")):
            m = re.match(r'r(#*)"', src[i:])
            hashes = m.group(1)
            start = i + m.end()
            end = src.find('"' + hashes, start)
            yield start, end
            i = end + 1 + len(hashes)
        elif c == '"':
            j = i + 1
            while src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            yield i + 1, j
            i = j + 1
        elif c == "'":
            m = CHAR.match(src, i)
            i = m.end() if m else i + 1
        else:
            i += 1


def rust(path, check):
    global changed
    src = open(path).read()
    out, last = [], 0
    for s, e in rust_literals(src):
        body = src[s:e]
        if not USES.search(body) or IMPORT in body:
            continue
        stripped = body.lstrip()
        if ITEM.match(body):
            ws = len(body) - len(stripped)
            out.append(src[last:s + ws]); out.append(IMPORT + " "); last = s + ws
            changed += 1
        else:
            line = src.count("\n", 0, s) + 1
            skipped.append(f"{path}:{line}: {body.strip()[:70]!r}")
    out.append(src[last:])
    new = "".join(out)
    if new != src and not check:
        open(path, "w").write(new)


def mb(path, check):
    global changed
    src = open(path).read()
    if not USES.search(src) or IMPORT in src:
        return
    # place after the leading comment block / existing use lines
    lines = src.split("\n")
    idx = 0
    while idx < len(lines) and (lines[idx].startswith("//") or lines[idx].strip() == ""):
        idx += 1
    while idx < len(lines) and lines[idx].startswith("use "):
        idx += 1
    if idx and lines[idx - 1].strip() == "":
        pass
    lines.insert(idx, IMPORT)
    changed += 1
    if not check:
        open(path, "w").write("\n".join(lines))


def main():
    check = "--check" in sys.argv
    for root in [a for a in sys.argv[1:] if not a.startswith("--")]:
        files = [root] if os.path.isfile(root) else [os.path.join(d, f) for d, _, fs in os.walk(root) for f in fs]
        for f in sorted(files):
            if f.endswith(".rs"):
                rust(f, check)
            elif f.endswith(".mb"):
                mb(f, check)
    print(f"{changed} sources {'would change' if check else 'changed'}", file=sys.stderr)
    for s in skipped:
        print("SKIPPED", s)


main()
