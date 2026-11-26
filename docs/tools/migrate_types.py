#!/usr/bin/env python3
"""Memobits built-in type spelling migration (S1).

Rewrites old built-in type spellings to the new ones, token-aware:

  Bool -> bool          Char -> char          Array<..> -> array<..>
  Option<X> -> X?       (parenthesized when X is `borrow ..`, `share ..`, or has a top-level `!`)
  Result<T, E> -> T ! E (parenthesized where needed, e.g. before `?`)
  Bytes<N> -> array<u8, N>
  Attempt<..> is left untouched (but its arguments are rewritten).

Handles: .mb files, Memobits sources embedded in Rust files (raw and normal
string literals that look like Memobits programs), and fenced code blocks
(and optionally inline code spans) in Markdown. Strings and comments of the
Memobits program are never changed (comments only with --comments, and then
only inside backtick spans).

Usage:
  migrate_types.py [--check] [--exclude SUBSTR] [--inline] [--comments] [--report-skipped] PATH...
  --check            dry run: print a unified diff, change nothing
  --inline           Markdown: also rewrite `inline code` spans
  --comments         .mb: rewrite `backtick` spans inside // comments
  --report-skipped   Rust: list string literals with old spellings that were
                     not recognized as Memobits sources
Prints a per-kind count summary to stderr.
"""
import argparse, difflib, os, re, sys
from collections import Counter

COUNTS = Counter()
WARN = []

WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
NUM = re.compile(r"[0-9][A-Za-z0-9_]*")
PUNCT2 = ("::", "->", "=>", "==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=", "/=", ":=", "..")


class Tok:
    __slots__ = ("kind", "s", "e", "text")

    def __init__(self, kind, s, e, text):
        self.kind, self.s, self.e, self.text = kind, s, e, text


def tokenize(src):
    toks, i, n = [], 0, len(src)
    while i < n:
        c = src[i]
        if c.isspace():
            j = i
            while j < n and src[j].isspace():
                j += 1
            toks.append(Tok("ws", i, j, src[i:j])); i = j
        elif src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            toks.append(Tok("comment", i, j, src[i:j])); i = j
        elif src.startswith("/*", i):
            j = src.find("*/", i + 2)
            j = n if j < 0 else j + 2
            toks.append(Tok("comment", i, j, src[i:j])); i = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
            toks.append(Tok("string", i, j, src[i:j])); i = j
        elif c == "'":
            m = re.compile(r"'(\\.[^']*|[^'\\])'").match(src, i)
            if m:
                toks.append(Tok("char", i, m.end(), m.group())); i = m.end()
            else:
                toks.append(Tok("p", i, i + 1, c)); i += 1
        elif WORD.match(src, i):
            m = WORD.match(src, i)
            toks.append(Tok("word", i, m.end(), m.group())); i = m.end()
        elif NUM.match(src, i):
            m = NUM.match(src, i)
            toks.append(Tok("num", i, m.end(), m.group())); i = m.end()
        else:
            two = src[i:i + 2]
            if two in PUNCT2:
                toks.append(Tok("p", i, i + 2, two)); i += 2
            else:
                toks.append(Tok("p", i, i + 1, c)); i += 1
    return toks


OPEN, CLOSE = "([{", ")]}"


def top_level_bang(text):
    depth = 0
    for t in tokenize(text):
        if t.kind != "p":
            continue
        if t.text in ("(", "[", "{", "<"):
            depth += 1
        elif t.text in (")", "]", "}", ">"):
            depth -= 1
        elif t.text == "!" and depth == 0:
            return True
    return False


def starts_with_access(text):
    return re.match(r"\s*(borrow|share)\b", text) is not None


def collapse(text):
    return re.sub(r"\s+", " ", text).strip()


class Rewriter:
    def __init__(self, src, name, comments=False):
        self.src, self.name, self.comments = src, name, comments
        self.toks = tokenize(src)
        self.enum_variant_slots = self._mark_enum_variants()

    def _sig(self, i, step):
        i += step
        while 0 <= i < len(self.toks) and self.toks[i].kind in ("ws", "comment"):
            i += step
        return i if 0 <= i < len(self.toks) else None

    def _mark_enum_variants(self):
        """Indexes of words that are enum variant names in a declaration."""
        marked, toks = set(), self.toks
        stack = []  # (is_enum_decl, depth_tag)
        for i, t in enumerate(toks):
            if t.kind != "p":
                continue
            if t.text == "[":
                p = self._sig(i, -1)
                is_enum = False
                if p is not None and toks[p].kind == "word" and toks[p].text == "enum":
                    is_enum = True
                elif p is not None:
                    # `type Name [` or `type Name<..> [`
                    q = p
                    if toks[q].text == ">":
                        d = 0
                        while q is not None:
                            if toks[q].text == ">":
                                d += 1
                            elif toks[q].text == "<":
                                d -= 1
                                if d == 0:
                                    break
                            q = self._sig(q, -1)
                        q = self._sig(q, -1) if q is not None else None
                    if q is not None and toks[q].kind == "word":
                        r = self._sig(q, -1)
                        if r is not None and toks[r].text in ("type", "pub"):
                            is_enum = toks[r].text == "type" or True
                            if toks[r].text == "pub":
                                is_enum = False
                        # `pub type Name [`
                        if r is not None and toks[r].text == "type":
                            is_enum = True
                stack.append(("[", is_enum))
                if is_enum:
                    n = self._sig(i, 1)
                    if n is not None and toks[n].kind == "word":
                        marked.add(n)
            elif t.text in ("(", "{"):
                stack.append((t.text, False))
            elif t.text in ("]", ")", "}"):
                if stack:
                    stack.pop()
            elif t.text == "," and stack and stack[-1][1]:
                n = self._sig(i, 1)
                if n is not None and toks[n].kind == "word":
                    marked.add(n)
        return marked

    def match_close(self, i):
        """Index of the `>` matching the `<` at i, or None."""
        depth, k, toks = 0, i, self.toks
        while k < len(toks):
            t = toks[k]
            if t.kind == "p":
                if t.text == "<":
                    depth += 1
                elif t.text == ">":
                    depth -= 1
                    if depth == 0:
                        return k
                elif t.text == ";":
                    return None
                elif t.text == "{":
                    # allow Rust format placeholders such as `{ty}` inside generics
                    d, m = 0, k
                    while m < len(toks):
                        if toks[m].text == "{":
                            d += 1
                        elif toks[m].text == "}":
                            d -= 1
                            if d == 0:
                                break
                        elif toks[m].text == ";":
                            return None
                        m += 1
                    if m >= len(toks):
                        return None
                    k = m
                elif t.text == "}":
                    return None
            k += 1
        return None

    def split_args(self, lo, hi):
        """Top-level comma split of token range [lo, hi); returns list of (lo, hi)."""
        parts, depth, start = [], 0, lo
        for k in range(lo, hi):
            t = self.toks[k]
            if t.kind == "p":
                if t.text in ("(", "[", "{", "<"):
                    depth += 1
                elif t.text in (")", "]", "}", ">"):
                    depth -= 1
                elif t.text == "," and depth == 0:
                    parts.append((start, k)); start = k + 1
        parts.append((start, hi))
        return parts

    def range_text(self, lo, hi):
        """Rewritten text of token range [lo, hi)."""
        out, base = [], self.toks[lo].s if lo < hi else 0
        edits = self.edits(lo, hi)
        pos = base
        for s, e, text in edits:
            out.append(self.src[pos:s]); out.append(text); pos = e
        end = self.toks[hi - 1].e if lo < hi else base
        out.append(self.src[pos:end])
        return "".join(out)

    def edits(self, lo=0, hi=None):
        hi = len(self.toks) if hi is None else hi
        toks, edits, i = self.toks, [], lo
        while i < hi:
            t = toks[i]
            if t.kind == "comment" and self.comments and t.text.startswith("//"):
                new = re.sub(r"`([^`\n]+)`", lambda m: "`" + rewrite_snippet(m.group(1)) + "`", t.text)
                if new != t.text:
                    edits.append((t.s, t.e, new))
                i += 1; continue
            if t.kind != "word":
                i += 1; continue
            prev = self._sig(i, -1)
            if prev is not None and prev >= lo and toks[prev].text in (".", "::", "type", "enum"):
                i += 1; continue
            if i in self.enum_variant_slots:
                i += 1; continue
            nxt = self._sig(i, 1)
            nxt_text = toks[nxt].text if nxt is not None and nxt < hi else None
            if t.text in ("Bool", "Char") and nxt_text != "::":
                new = t.text.lower()
                COUNTS[t.text] += 1
                edits.append((t.s, t.e, new)); i += 1; continue
            if t.text in ("Array", "Bytes", "Option", "Result") and nxt_text == "<" and nxt == i + 1:
                close = self.match_close(nxt)
                if close is None or close >= hi:
                    WARN.append(f"{self.name}: unmatched generic after {t.text} at offset {t.s}")
                    i += 1; continue
                inner = list(range(nxt + 1, close))
                if any(toks[k].kind == "comment" for k in inner):
                    WARN.append(f"{self.name}: comment inside {t.text}<..> at offset {t.s}; left alone")
                    i += 1; continue
                args = [collapse(self.range_text(a, b)) if a < b else "" for a, b in self.split_args(nxt + 1, close)]
                new = self.compose(t.text, args, t.s)
                if new is None:
                    i += 1; continue
                end = toks[close].e
                nn = self._sig(close, 1)
                if t.text == "Result" and nn is not None and nn < hi and toks[nn].text == "?":
                    new = "(" + new + ")"
                COUNTS[t.text] += 1
                edits.append((t.s, end, new)); i = close + 1; continue
            i += 1
        return edits

    def compose(self, head, args, offset):
        if head == "Array":
            if len(args) != 2:
                WARN.append(f"{self.name}: Array with {len(args)} args at {offset}"); return None
            return f"array<{args[0]}, {args[1]}>"
        if head == "Bytes":
            if len(args) != 1:
                WARN.append(f"{self.name}: Bytes with {len(args)} args at {offset}"); return None
            return f"array<u8, {args[0]}>"
        if head == "Option":
            if len(args) != 1:
                WARN.append(f"{self.name}: Option with {len(args)} args at {offset}"); return None
            x = args[0]
            if starts_with_access(x) or top_level_bang(x):
                x = f"({x})"
            return x + "?"
        if head == "Result":
            if len(args) != 2:
                WARN.append(f"{self.name}: Result with {len(args)} args at {offset}"); return None
            t, e = args
            if starts_with_access(t) or starts_with_access(e):
                # `T ! borrow E` has no defined spelling; leave for manual handling
                WARN.append(f"{self.name}: Result with a borrow/share argument at {offset}; left unchanged")
                return None
            if top_level_bang(t):
                t = f"({t})"
            if top_level_bang(e):
                e = f"({e})"
            return f"{t} ! {e}"


def rewrite_snippet(text):
    r = Rewriter(text, "<snippet>")
    pos, out = 0, []
    for s, e, new in r.edits():
        out.append(text[pos:s]); out.append(new); pos = e
    out.append(text[pos:])
    return "".join(out)


def rewrite_mb(src, name, comments=False):
    return rewrite_snippet_named(src, name, comments)


def rewrite_snippet_named(src, name, comments):
    r = Rewriter(src, name, comments)
    pos, out = 0, []
    for s, e, new in r.edits():
        out.append(src[pos:s]); out.append(new); pos = e
    out.append(src[pos:])
    return "".join(out)


OLD = re.compile(r"\b(Option|Result|Array|Bytes)\s*<|\b(Bool|Char)\b")
LOOKS_MB = re.compile(
    r"(^|[\s;{}\"])fn\s+[A-Za-z_{][\w{}]*\s*[<(]"
    r"|(^|[\s;{}])(pub\s+)?type\s+[A-Z{]\w*"
    r"|(^|\s)use\s+self::"
    r"|(^|[\s;{}])(let|var)\s+[A-Za-z_]\w*\s*(:=|:\s*[A-Za-z(\[{])"
)


def looks_like_memobits(text):
    return LOOKS_MB.search(text) is not None


# ---------------- Rust embedding ----------------

def unescape(raw):
    """Unescape a normal Rust string body; returns (text, rawpos list len(text)+1)."""
    out, pos, i, n = [], [], 0, len(raw)
    while i < n:
        c = raw[i]
        if c != "\\":
            out.append(c); pos.append(i); i += 1; continue
        d = raw[i + 1] if i + 1 < n else ""
        simple = {"n": "\n", "t": "\t", "r": "\r", "0": "\0", "\\": "\\", '"': '"', "'": "'"}
        if d in simple:
            out.append(simple[d]); pos.append(i); i += 2
        elif d == "\n" or d == "\r":
            j = i + 1
            while j < n and raw[j] in " \t\r\n":
                j += 1
            i = j
        elif d == "u":
            m = re.compile(r"\\u\{([0-9a-fA-F_]+)\}").match(raw, i)
            if not m:
                return None
            out.append(chr(int(m.group(1).replace("_", ""), 16))); pos.append(i); i = m.end()
        elif d == "x":
            m = re.compile(r"\\x([0-7][0-9a-fA-F])").match(raw, i)
            if not m:
                return None
            out.append(chr(int(m.group(1), 16))); pos.append(i); i = m.end()
        else:
            return None
    pos.append(n)
    return "".join(out), pos


def rust_literals(src):
    """Yield (kind, body_start, body_end) for string literals outside comments."""
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if src.startswith("//", i):
            j = src.find("\n", i); i = n if j < 0 else j
        elif src.startswith("/*", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if src.startswith("/*", i): depth += 1; i += 2
                elif src.startswith("*/", i): depth -= 1; i += 2
                else: i += 1
        elif c == "r" or (c == "b" and src[i + 1:i + 2] == "r"):
            m = re.compile(r"b?r(#*)\"").match(src, i)
            prev_ok = i == 0 or not (src[i - 1].isalnum() or src[i - 1] == "_")
            if m and prev_ok:
                close = '"' + m.group(1)
                j = src.find(close, m.end())
                yield ("raw", m.end(), j)
                i = j + len(close)
            else:
                i += 1
        elif c == '"':
            prev_b = i > 0 and src[i - 1] == "b" and (i < 2 or not src[i - 2].isalnum())
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            if not prev_b:
                yield ("normal", i + 1, j)
            i = j + 1
        elif c == "'":
            m = re.compile(r"'(\\u\{[0-9a-fA-F]+\}|\\x[0-9a-fA-F]{2}|\\.|[^'\\])'").match(src, i)
            i = m.end() if m else i + 1
        else:
            i += 1


def rewrite_rust(src, name, report_skipped=False, comments=False):
    out, pos, changed = [], 0, 0
    for kind, s, e in rust_literals(src):
        body = src[s:e]
        if kind == "raw":
            text, mapping = body, None
        else:
            u = unescape(body)
            if u is None:
                if OLD.search(body):
                    WARN.append(f"{name}: literal with unsupported escapes near offset {s}")
                continue
            text, mapping = u
        if not OLD.search(text):
            continue
        if not looks_like_memobits(text):
            if report_skipped:
                WARN.append(f"{name}: skipped non-source literal at offset {s}: {text[:70]!r}")
            continue
        r = Rewriter(text, name, comments)
        for ts, te, new in r.edits():
            rs, re_ = (ts, te) if mapping is None else (mapping[ts], mapping[te])
            out.append(src[pos:s + rs]); out.append(new); pos = s + re_
            changed += 1
    out.append(src[pos:])
    return "".join(out)


# ---------------- Markdown ----------------

def rewrite_md(src, name, inline=False):
    lines, out, i = src.split("\n"), [], 0
    while i < len(lines):
        ln = lines[i]
        m = re.match(r"^(\s*)```(\w*)\s*$", ln)
        if m:
            lang = m.group(2)
            j = i + 1
            while j < len(lines) and not re.match(r"^\s*```\s*$", lines[j]):
                j += 1
            block = "\n".join(lines[i + 1:j])
            if lang in ("mb", "memobits") or (lang == "" and looks_like_memobits(block)):
                block = rewrite_snippet_named(block, name, False)
            out.append(ln)
            out.extend(block.split("\n") if j > i + 1 else [])
            if j < len(lines):
                out.append(lines[j])
            i = j + 1
            continue
        if inline:
            ln = re.sub(r"`([^`\n]+)`", lambda mm: "`" + rewrite_snippet_named(mm.group(1), name, False) + "`", ln)
        out.append(ln); i += 1
    return "\n".join(out)


def process(path, args):
    src = open(path, encoding="utf-8").read()
    if path.endswith(".mb"):
        new = rewrite_snippet_named(src, path, args.comments)
    elif path.endswith(".rs"):
        new = rewrite_rust(src, path, args.report_skipped, False)
    elif path.endswith(".md"):
        new = rewrite_md(src, path, args.inline)
    else:
        return False
    if new == src:
        return False
    if args.check:
        sys.stdout.writelines(difflib.unified_diff(src.splitlines(True), new.splitlines(True), "a/" + path, "b/" + path))
    else:
        open(path, "w", encoding="utf-8").write(new)
    return True


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--inline", action="store_true")
    ap.add_argument("--comments", action="store_true")
    ap.add_argument("--exclude", action="append", default=[], help="path substring to skip (repeatable)")
    ap.add_argument("--report-skipped", action="store_true")
    args = ap.parse_args()
    files = []
    for p in args.paths:
        if os.path.isdir(p):
            for root, dirs, fs in os.walk(p):
                dirs[:] = [d for d in dirs if d not in ("target", ".git", "legacy")]
                files += [os.path.join(root, f) for f in sorted(fs)]
        else:
            files.append(p)
    files = [f for f in files if not any(x in f for x in args.exclude)]
    changed = [f for f in files if process(f, args)]
    print(f"{'would change' if args.check else 'changed'} {len(changed)} file(s): {dict(COUNTS)}", file=sys.stderr)
    for f in changed:
        print("  " + f, file=sys.stderr)
    for w in WARN:
        print("WARN " + w, file=sys.stderr)


if __name__ == "__main__":
    main()
