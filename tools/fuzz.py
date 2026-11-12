#!/usr/bin/env python3
"""Differential test of qfuf against z3 on random small QF_UF problems.

Usage: fuzz.py QFUF Z3 N [SEED]

For each random problem: both solvers must agree on sat/unsat, and for sat the model printed by
qfuf must satisfy the problem: z3 checks the assertions with the model's define-fun in place of
the declarations, the abstract values (as @U_k U) being distinct new constants. The solver
enumerates every assignment of its atoms, so the problems are small; a problem qfuf does not
finish within the time limit counts as a timeout, not a failure.
"""
import random
import re
import subprocess
import sys

TIMEOUT = 20


class Gen:
    def __init__(self):
        self.sorts = ["U"] + (["V"] if random.random() < 0.3 else [])
        self.consts = []  # (name, sort)
        self.funs = []  # (name, [arg sorts], result sort)
        self.decls = []
        self.defs = []
        for s in self.sorts:
            for i in range(random.randint(1, 3)):
                self.declare("%s%d" % (s.lower(), i), [], s)
        self.declare("f", ["U"], "U")
        if random.random() < 0.5:
            self.declare("g", ["U", "U"], "U")
        self.declare("p", ["U"], "Bool")
        if random.random() < 0.5:
            self.declare("q", [], "Bool")
        if random.random() < 0.3:
            self.declare("h", ["U", "Bool"], "U")
        if "V" in self.sorts and random.random() < 0.5:
            self.declare("k", ["V"], "U")
        if random.random() < 0.3:
            self.defs.append("(define-fun dd ((x U) (y U)) Bool (or (= x y) (p x)))")
            self.funs.append(("dd", ["U", "U"], "Bool"))

    def declare(self, n, args, s):
        if args:
            self.decls.append("(declare-fun %s (%s) %s)" % (n, " ".join(args), s))
            self.funs.append((n, args, s))
        else:
            self.decls.append("(declare-const %s %s)" % (n, s))
            self.consts.append((n, s))

    def term(self, s, d):
        if s == "Bool":
            return self.form(d)
        cs = [n for n, cs_ in self.consts if cs_ == s]
        fs = [f for f in self.funs if f[2] == s]
        if d == 0 or not fs or random.random() < 0.4:
            return random.choice(cs) if cs else "(f %s)" % self.term("U", 0)
        if random.random() < 0.15:
            return "(ite %s %s %s)" % (self.form(d - 1), self.term(s, d - 1), self.term(s, d - 1))
        n, args, _ = random.choice(fs)
        return "(%s %s)" % (n, " ".join(self.term(a, d - 1) for a in args))

    def form(self, d):
        r = random.random()
        if d == 0 or r < 0.3:
            r2 = random.random()
            ps = [f for f in self.funs if f[2] == "Bool"] + [(n, [], s) for n, s in self.consts if s == "Bool"]
            if r2 < 0.5 or not ps:
                s = random.choice(self.sorts)
                return "(= %s %s)" % (self.term(s, min(d, 1)), self.term(s, min(d, 1)))
            n, args, _ = random.choice(ps)
            return n if not args else "(%s %s)" % (n, " ".join(self.term(a, min(d, 1)) for a in args))
        if r < 0.45:
            return "(not %s)" % self.form(d - 1)
        if r < 0.75:
            op = random.choice(["and", "or", "xor", "=>", "="])
            k = 2 if op == "=" or random.random() < 0.7 else 3
            return "(%s %s)" % (op, " ".join(self.form(d - 1) for _ in range(k)))
        if r < 0.85:
            s = random.choice(self.sorts)
            return "(distinct %s)" % " ".join(self.term(s, 1) for _ in range(random.randint(2, 3)))
        if r < 0.92:
            return "(ite %s %s %s)" % (self.form(d - 1), self.form(d - 1), self.form(d - 1))
        return "(let ((z %s)) (and z %s))" % (self.form(d - 1), self.form(d - 1))

    def script(self):
        asserts = ["(assert %s)" % self.form(2) for _ in range(random.randint(1, 2))]
        head = ["(set-logic QF_UF)"] + ["(declare-sort %s 0)" % s for s in self.sorts]
        return head, self.decls, self.defs, asserts


def run(cmd, text, timeout=None):
    return subprocess.run(cmd, input=text, capture_output=True, text=True, timeout=timeout).stdout


def model_check(z3, head, defs, asserts, model):
    """Whether the model (get-model text) satisfies the assertions, according to z3."""
    values = sorted(set(re.findall(r"\(as @(\w+?)_(\d+) (\w+)\)", model)))
    body = re.sub(r"\(as @(\w+?)_(\d+) (\w+)\)", r"abs_\1_\2", model)
    lines = list(head)
    for s in sorted({v[2] for v in values}):
        names = ["abs_%s_%s" % (v[0], v[1]) for v in values if v[2] == s]
        lines += ["(declare-const %s %s)" % (n, s) for n in names]
        if len(names) > 1:
            lines.append("(assert (distinct %s))" % " ".join(names))
    lines += [l.strip() for l in body.strip()[1:-1].strip().splitlines() if l.strip()]
    lines += defs + asserts + ["(check-sat)"]
    return run([z3, "-in"], "\n".join(lines)).strip() == "sat"


def main():
    qfuf, z3, n = sys.argv[1], sys.argv[2], int(sys.argv[3])
    random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 0)
    stats = {"sat": 0, "unsat": 0, "timeout": 0}
    for i in range(n):
        head, decls, defs, asserts = Gen().script()
        text = "\n".join(head + decls + defs + asserts + ["(check-sat)", "(get-model)"])
        expected = run([z3, "-in"], "\n".join(head + decls + defs + asserts + ["(check-sat)"])).strip()
        try:
            out = run([qfuf], text, timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            stats["timeout"] += 1
            continue
        answer, _, model = out.partition("\n")
        if answer != expected:
            print("MISMATCH qfuf=%r z3=%r\n%s\n%s" % (answer, expected, text, out))
            sys.exit(1)
        if answer == "sat" and not model_check(z3, head, defs, asserts, model):
            print("BAD MODEL\n%s\n%s" % (text, out))
            sys.exit(1)
        stats[answer] += 1
    print("ok: %d problems, %d sat, %d unsat, %d timeouts" % (n, stats["sat"], stats["unsat"], stats["timeout"]))


main()
