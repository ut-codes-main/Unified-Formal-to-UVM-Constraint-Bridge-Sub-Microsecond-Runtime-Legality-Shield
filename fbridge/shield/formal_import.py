from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

import z3

from ..ir.ast import FALSE, TRUE, Binary, Concat, Const, Expr, Func, Ite, Slice, Unary, Var, conj

BIT_NAME = re.compile(r"^(.*?)\[(\d+)\]$")


class FormalImportError(Exception):
    pass


@dataclass
class FormalFacts:
    source: str
    fmt: str
    invariants: list[Expr] = field(default_factory=list)
    widths: dict[str, int] = field(default_factory=dict)
    names: list[str] = field(default_factory=list)

    def expr(self) -> Expr:
        return conj(self.invariants)


def _bit(name: str) -> tuple[str, int | None]:
    m = BIT_NAME.match(name)
    if m:
        return m.group(1), int(m.group(2))
    return name, None


@dataclass
class Aig:
    maxvar: int
    inputs: list[int] = field(default_factory=list)
    latches: list[tuple[int, int, int]] = field(default_factory=list)
    outputs: list[int] = field(default_factory=list)
    bads: list[int] = field(default_factory=list)
    constraints: list[int] = field(default_factory=list)
    ands: dict[int, tuple[int, int]] = field(default_factory=dict)
    symbols: dict[tuple[str, int], str] = field(default_factory=dict)


def parse_aiger(data: bytes) -> Aig:
    pos = 0

    def line() -> str:
        nonlocal pos
        end = data.index(b"\n", pos) if b"\n" in data[pos:] else len(data)
        s = data[pos:end].decode()
        pos = end + 1
        return s.strip()

    header = line().split()
    if header[0] not in ("aag", "aig"):
        raise FormalImportError("not an AIGER file")
    nums = [int(x) for x in header[1:]] + [0] * 4
    M, I, L, O, A, B, C = nums[:7]
    aig = Aig(M)
    binary = header[0] == "aig"
    if binary:
        aig.inputs = [2 * (i + 1) for i in range(I)]
    else:
        aig.inputs = [int(line()) for _ in range(I)]
    for i in range(L):
        parts = [int(x) for x in line().split()]
        if binary:
            lit, nxt = 2 * (I + i + 1), parts[0]
            init = parts[1] if len(parts) > 1 else 0
        else:
            lit, nxt = parts[0], parts[1]
            init = parts[2] if len(parts) > 2 else 0
        aig.latches.append((lit, nxt, init))
    aig.outputs = [int(line()) for _ in range(O)]
    aig.bads = [int(line()) for _ in range(B)]
    aig.constraints = [int(line()) for _ in range(C)]
    if binary:
        for i in range(A):
            lhs = 2 * (I + L + i + 1)
            d0 = _varint(data, pos)
            pos = d0[1]
            d1 = _varint(data, pos)
            pos = d1[1]
            r0 = lhs - d0[0]
            aig.ands[lhs] = (r0, r0 - d1[0])
    else:
        for _ in range(A):
            lhs, r0, r1 = (int(x) for x in line().split())
            aig.ands[lhs] = (r0, r1)
    while pos < len(data):
        s = line()
        if not s or s.startswith("c"):
            break
        m = re.match(r"^([ilobcjf])(\d+)\s+(.*)$", s)
        if m:
            aig.symbols[(m.group(1), int(m.group(2)))] = m.group(3)
    return aig


def _varint(data: bytes, pos: int) -> tuple[int, int]:
    x, shift = 0, 0
    while True:
        b = data[pos]
        pos += 1
        x |= (b & 0x7F) << shift
        if not b & 0x80:
            return x, pos
        shift += 7


def aig_to_facts(aig: Aig, source: str, output_names: list[str] | None = None) -> FormalFacts:
    facts = FormalFacts(source, "aiger")
    leaf: dict[int, Expr] = {}
    widths: dict[str, int] = {}

    def name_leaf(kind: str, idx: int, lit: int):
        nm = aig.symbols.get((kind, idx), f"{kind}{idx}")
        base, bit = _bit(nm)
        if bit is None:
            leaf[lit] = Var(base)
            widths[base] = max(widths.get(base, 1), 1)
        else:
            leaf[lit] = Slice(Var(base), bit, bit)
            widths[base] = max(widths.get(base, 1), bit + 1)

    for i, lit in enumerate(aig.inputs):
        name_leaf("i", i, lit)
    for i, (lit, _, _) in enumerate(aig.latches):
        name_leaf("l", i, lit)
    memo: dict[int, Expr] = {0: FALSE, 1: TRUE}

    def lit_expr(l: int) -> Expr:
        if l in memo:
            return memo[l]
        if l & 1:
            r = Unary("!", lit_expr(l ^ 1))
        elif l in leaf:
            r = leaf[l]
        elif l in aig.ands:
            a, b = aig.ands[l]
            r = Binary("&&", lit_expr(a), lit_expr(b))
        else:
            raise FormalImportError(f"undefined AIGER literal {l}")
        memo[l] = r
        return r

    stack_limit_guard(aig)
    picks = []
    for i, lit in enumerate(aig.outputs):
        nm = aig.symbols.get(("o", i), f"o{i}")
        if output_names is None or nm in output_names:
            picks.append(lit_expr(lit))
    for lit in aig.bads:
        picks.append(Unary("!", lit_expr(lit)))
    for lit in aig.constraints:
        picks.append(lit_expr(lit))
    if not picks:
        raise FormalImportError(f"{source}: no invariant output selected")
    facts.invariants = picks
    facts.widths = widths
    facts.names = sorted(widths)
    return facts


def stack_limit_guard(aig: Aig) -> None:
    import sys
    need = 4 * len(aig.ands) + 1000
    if sys.getrecursionlimit() < need:
        sys.setrecursionlimit(need)


def load_aiger(path: str | Path, outputs: list[str] | None = None) -> FormalFacts:
    p = Path(path)
    return aig_to_facts(parse_aiger(p.read_bytes()), str(p), outputs)


BTOR_BIN = {
    "and": "&", "or": "|", "xor": "^", "xnor": "~^", "add": "+", "sub": "-", "mul": "*", "udiv": "/", "urem": "%",
    "eq": "==", "neq": "!=", "ult": "<", "ulte": "<=", "ugt": ">", "ugte": ">=", "sll": "<<", "srl": ">>",
    "implies": "->", "iff": "<->",
}
BTOR_SIGNED = {"slt": "<", "slte": "<=", "sgt": ">", "sgte": ">=", "sdiv": "/", "srem": "%", "sra": ">>>"}


def load_btor2(path: str | Path | None = None, text: str | None = None) -> FormalFacts:
    src = str(path or "<text>")
    if text is None:
        text = Path(path).read_text()
    sorts: dict[int, int] = {}
    nodes: dict[int, Expr] = {}
    width: dict[int, int] = {}
    facts = FormalFacts(src, "btor2")

    def arg(tok: str) -> Expr:
        i = int(tok)
        e = nodes[abs(i)]
        if i < 0:
            return Unary("~", e) if width[abs(i)] > 1 else Unary("!", e)
        return e

    def argw(tok: str) -> int:
        return width[abs(int(tok))]

    for raw in text.splitlines():
        s = raw.split(";")[0].strip()
        if not s:
            continue
        t = s.split()
        nid, op = int(t[0]), t[1]
        if op == "sort":
            if t[2] != "bitvec":
                raise FormalImportError(f"{src}: array sorts are not supported")
            sorts[nid] = int(t[3])
            continue
        if op in ("input", "state"):
            w = sorts[int(t[2])]
            name = t[3] if len(t) > 3 else f"{op}{nid}"
            nodes[nid], width[nid] = Var(name), w
            facts.widths[name] = w
            continue
        if op in ("init", "next", "fair", "justice"):
            continue
        if op in ("bad", "constraint", "output"):
            e = arg(t[2])
            facts.invariants.append(Unary("!", e) if op == "bad" else e)
            continue
        w = sorts[int(t[2])]
        a = t[3:]
        if op in ("const", "constd", "consth"):
            base = {"const": 2, "constd": 10, "consth": 16}[op]
            e = Const(int(a[0], base) & ((1 << w) - 1), w, False)
        elif op in ("zero", "one", "ones"):
            e = Const({"zero": 0, "one": 1, "ones": (1 << w) - 1}[op], w, False)
        elif op == "not":
            e = Unary("~", arg(a[0]))
        elif op == "neg":
            e = Unary("-", arg(a[0]))
        elif op in ("redor", "redand", "redxor"):
            e = Unary({"redor": "|r", "redand": "&r", "redxor": "^r"}[op], arg(a[0]))
        elif op in ("nand", "nor"):
            e = Unary("~", Binary("&" if op == "nand" else "|", arg(a[0]), arg(a[1])))
        elif op in BTOR_BIN:
            e = Binary(BTOR_BIN[op], arg(a[0]), arg(a[1]))
        elif op in BTOR_SIGNED:
            e = Binary(BTOR_SIGNED[op], Func("$signed", (arg(a[0]),)), Func("$signed", (arg(a[1]),)))
            if op in ("sdiv", "srem", "sra"):
                e = Func("$unsigned", (e,))
        elif op == "concat":
            e = Concat((arg(a[0]), arg(a[1])))
        elif op == "slice":
            e = Slice(arg(a[0]), int(a[1]), int(a[2]))
        elif op == "uext":
            k = int(a[1])
            e = Concat((Const(0, k, False), arg(a[0]))) if k else arg(a[0])
        elif op == "sext":
            k = int(a[1])
            src_w = argw(a[0])
            x = arg(a[0])
            e = Concat(tuple([Slice(x, src_w - 1, src_w - 1)] * k) + (x,)) if k else x
        elif op == "ite":
            e = Ite(arg(a[0]), arg(a[1]), arg(a[2]))
        else:
            raise FormalImportError(f"{src}: unsupported BTOR2 operator '{op}'")
        nodes[nid], width[nid] = e, w
    if not facts.invariants:
        raise FormalImportError(f"{src}: no bad/constraint/output lines found")
    facts.names = sorted(facts.widths)
    return facts


def z3_to_expr(e: z3.ExprRef, widths: dict[str, int], memo: dict | None = None) -> Expr:
    memo = {} if memo is None else memo
    key = e.get_id()
    if key in memo:
        return memo[key]
    k = e.decl().kind() if z3.is_app(e) else None
    ch = [z3_to_expr(c, widths, memo) for c in e.children()] if z3.is_app(e) else []

    def fold(op):
        out = ch[0]
        for c in ch[1:]:
            out = Binary(op, out, c)
        return out

    def signed(op):
        return Binary(op, Func("$signed", (ch[0],)), Func("$signed", (ch[1],)))

    if z3.is_true(e):
        r = TRUE
    elif z3.is_false(e):
        r = FALSE
    elif z3.is_bv_value(e):
        r = Const(e.as_long(), e.size(), False)
    elif z3.is_const(e) and k == z3.Z3_OP_UNINTERPRETED:
        name = e.decl().name()
        widths[name] = e.size() if z3.is_bv(e) else 1
        r = Var(name)
    elif k == z3.Z3_OP_AND:
        r = fold("&&")
    elif k == z3.Z3_OP_OR:
        r = fold("||")
    elif k == z3.Z3_OP_NOT:
        r = Unary("!", ch[0])
    elif k == z3.Z3_OP_IMPLIES:
        r = Binary("->", ch[0], ch[1])
    elif k == z3.Z3_OP_XOR:
        r = Binary("!=", ch[0], ch[1])
    elif k == z3.Z3_OP_EQ:
        r = Binary("==", ch[0], ch[1])
    elif k == z3.Z3_OP_DISTINCT:
        r = conj([Binary("!=", ch[i], ch[j]) for i in range(len(ch)) for j in range(i + 1, len(ch))])
    elif k == z3.Z3_OP_ITE:
        r = Ite(ch[0], ch[1], ch[2])
    elif k in (z3.Z3_OP_BADD, z3.Z3_OP_BSUB, z3.Z3_OP_BMUL, z3.Z3_OP_BAND, z3.Z3_OP_BOR, z3.Z3_OP_BXOR):
        r = fold({z3.Z3_OP_BADD: "+", z3.Z3_OP_BSUB: "-", z3.Z3_OP_BMUL: "*", z3.Z3_OP_BAND: "&", z3.Z3_OP_BOR: "|", z3.Z3_OP_BXOR: "^"}[k])
    elif k in (z3.Z3_OP_BUDIV, z3.Z3_OP_BUDIV_I):
        r = Binary("/", ch[0], ch[1])
    elif k in (z3.Z3_OP_BUREM, z3.Z3_OP_BUREM_I):
        r = Binary("%", ch[0], ch[1])
    elif k in (z3.Z3_OP_BSDIV, z3.Z3_OP_BSDIV_I):
        r = Func("$unsigned", (signed("/"),))
    elif k in (z3.Z3_OP_BSREM, z3.Z3_OP_BSREM_I):
        r = Func("$unsigned", (signed("%"),))
    elif k in (z3.Z3_OP_BSMOD, z3.Z3_OP_BSMOD_I):
        w = e.size()
        rem = Func("$unsigned", (signed("%"),))
        flip = Binary("&&", Binary("!=", rem, Const(0, w, False)),
                      Binary("!=", Slice(rem, w - 1, w - 1), Slice(ch[1], w - 1, w - 1)))
        r = Ite(flip, Binary("+", rem, ch[1]), rem)
    elif k == z3.Z3_OP_BNEG:
        r = Unary("-", ch[0])
    elif k == z3.Z3_OP_BNOT:
        r = Unary("~", ch[0])
    elif k in (z3.Z3_OP_BNAND, z3.Z3_OP_BNOR):
        r = Unary("~", fold("&" if k == z3.Z3_OP_BNAND else "|"))
    elif k == z3.Z3_OP_BXNOR:
        r = fold("~^")
    elif k in (z3.Z3_OP_ULEQ, z3.Z3_OP_UGEQ, z3.Z3_OP_ULT, z3.Z3_OP_UGT):
        r = Binary({z3.Z3_OP_ULEQ: "<=", z3.Z3_OP_UGEQ: ">=", z3.Z3_OP_ULT: "<", z3.Z3_OP_UGT: ">"}[k], ch[0], ch[1])
    elif k in (z3.Z3_OP_SLEQ, z3.Z3_OP_SGEQ, z3.Z3_OP_SLT, z3.Z3_OP_SGT):
        r = signed({z3.Z3_OP_SLEQ: "<=", z3.Z3_OP_SGEQ: ">=", z3.Z3_OP_SLT: "<", z3.Z3_OP_SGT: ">"}[k])
    elif k == z3.Z3_OP_CONCAT:
        r = Concat(tuple(ch))
    elif k == z3.Z3_OP_EXTRACT:
        hi, lo = e.params()
        r = Slice(ch[0], hi, lo)
    elif k == z3.Z3_OP_ZERO_EXT:
        n = e.params()[0]
        r = Concat((Const(0, n, False), ch[0])) if n else ch[0]
    elif k == z3.Z3_OP_SIGN_EXT:
        n = e.params()[0]
        w = e.children()[0].size()
        r = Concat(tuple([Slice(ch[0], w - 1, w - 1)] * n) + (ch[0],)) if n else ch[0]
    elif k in (z3.Z3_OP_BSHL, z3.Z3_OP_BLSHR):
        r = Binary("<<" if k == z3.Z3_OP_BSHL else ">>", ch[0], ch[1])
    elif k == z3.Z3_OP_BASHR:
        r = Func("$unsigned", (Binary(">>>", Func("$signed", (ch[0],)), ch[1]),))
    else:
        raise FormalImportError(f"unsupported SMT operator {e.decl().name()}")
    memo[key] = r
    return r


def load_smt2(path: str | Path | None = None, text: str | None = None) -> FormalFacts:
    src = str(path or "<text>")
    if text is None:
        text = Path(path).read_text()
    facts = FormalFacts(src, "smt2")
    memo: dict = {}
    for a in z3.parse_smt2_string(text):
        facts.invariants.append(z3_to_expr(a, facts.widths, memo))
    if not facts.invariants:
        raise FormalImportError(f"{src}: no assertions found")
    facts.names = sorted(facts.widths)
    return facts


def load_facts(fmt: str, path: str | Path, **kw) -> FormalFacts:
    fmt = fmt.lower()
    if fmt in ("aiger", "aag", "aig"):
        return load_aiger(path, kw.get("outputs"))
    if fmt in ("btor", "btor2"):
        return load_btor2(path)
    if fmt in ("smt2", "smt", "smtlib"):
        return load_smt2(path)
    raise FormalImportError(f"unknown invariant format '{fmt}'")
