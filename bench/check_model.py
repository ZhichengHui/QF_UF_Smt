#!/usr/bin/env python3
"""Check a model of an SMT-LIB QF_UF instance with z3.

Usage: check_model.py INSTANCE MODEL Z3

MODEL is the solver's output after `sat`: the `(get-model)` response, a list of define-fun. The
instance is rebuilt with the model in place of its declarations of functions and constants: its
sort declarations, then the abstract values of the model (`(as @S_k S)`) as pairwise distinct new
constants, then the model, then the rest of the instance (define-fun, assert) and check-sat. The
model is good when z3 answers `sat`; a declared symbol missing from the model makes z3 fail.
Exit 0 for a good model, 1 otherwise.
"""
import re
import subprocess
import sys


def commands(text):
    """The top-level s-expressions of an SMT-LIB script, as text."""
    out, depth, start, i, n = [], 0, None, 0, len(text)
    while i < n:
        c = text[i]
        if c == ";":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if c in "|\"":
            j = text.index(c, i + 1)
            while c == "\"" and text[j + 1:j + 2] == "\"":  # "" inside a string
                j = text.index(c, j + 2)
            i = j + 1
            continue
        if c == "(":
            if depth == 0:
                start = i
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                out.append(text[start:i + 1])
        i += 1
    return out


def head(cmd):
    m = re.match(r"\(\s*([^\s()]+)", cmd)
    return m.group(1) if m else ""


def main():
    instance, model, z3 = sys.argv[1], sys.argv[2], sys.argv[3]
    cmds = commands(open(instance).read())
    model_text = open(model).read().strip()
    if not (model_text.startswith("(") and model_text.endswith(")")):
        print("no model")
        return 1
    abstract = r"\(as @([^\s()]+?)_(\d+) ([^\s()]+)\)"
    values = sorted(set(re.findall(abstract, model_text)))
    defs = commands(re.sub(abstract, r"abs_\1_\2", model_text)[1:-1])
    lines = [c for c in cmds if head(c) in ("set-logic", "declare-sort", "define-sort")]
    for s in sorted({v[2] for v in values}):
        names = ["abs_%s_%s" % (v[0], v[1]) for v in values if v[2] == s]
        lines += ["(declare-const %s %s)" % (x, s) for x in names]
        if len(names) > 1:
            lines.append("(assert (distinct %s))" % " ".join(names))
    lines += defs
    lines += [c for c in cmds if head(c) in ("define-fun", "assert")]
    lines.append("(check-sat)")
    r = subprocess.run([z3, "-in"], input="\n".join(lines), capture_output=True, text=True)
    if r.stdout.strip() == "sat":
        return 0
    print((r.stdout + r.stderr).strip()[:500])
    return 1


sys.exit(main())
