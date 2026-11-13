from __future__ import annotations

import re
from dataclasses import dataclass

from ..ir.semantics import Backend, Lowerer
from .compile import ACTION_BASE, CompiledShield


def c_ident(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_]", "_", name)


def _mask(w: int) -> int:
    return (1 << w) - 1


def _hex(v: int) -> str:
    return f"0x{v:X}ULL"


class CBackend(Backend):
    def __init__(self, var_map: dict[str, tuple[str, int]]):
        self.var_map = var_map

    @staticmethod
    def _chk(w: int) -> None:
        if w > 64:
            raise ValueError("C codegen supports expressions up to 64 bits")

    def const(self, v, w):
        self._chk(w)
        return _hex(v & _mask(w))

    def var(self, name, t, w):
        if t != 0:
            raise ValueError("temporal operators are not supported in shield next-state functions")
        word, lsb = self.var_map[name]
        return f"(({word} >> {lsb}) & {_hex(_mask(w))})"

    def ext(self, x, wf, wt, signed):
        self._chk(wt)
        if not signed:
            return x
        m = 1 << (wf - 1)
        return f"((({x}) ^ {_hex(m)}) - {_hex(m)}) & {_hex(_mask(wt))})"

    def extract(self, x, hi, lo, w):
        return f"((({x}) >> {lo}) & {_hex(_mask(hi - lo + 1))})"

    def concat(self, parts):
        out, shift = [], 0
        for x, w in reversed(parts):
            out.append(f"(({x}) << {shift})" if shift else f"({x})")
            shift += w
        self._chk(shift)
        return "(" + " | ".join(out) + ")"

    def arith(self, op, x, y, w, signed):
        m = _hex(_mask(w))
        if op in "+-*":
            return f"((({x}) {op} ({y})) & {m})"
        if signed:
            fn = "fb_sdiv" if op == "/" else "fb_srem"
            return f"{fn}({x}, {y}, {w})"
        return f"fb_udiv({x}, {y}, {w})" if op == "/" else f"fb_urem({x}, {y})"

    def bitop(self, op, x, y, w):
        if op == "~^":
            return f"(~(({x}) ^ ({y})) & {_hex(_mask(w))})"
        return f"(({x}) {op} ({y}))"

    def bnot(self, x, w):
        return f"(~({x}) & {_hex(_mask(w))})"

    def neg(self, x, w):
        return f"((0ULL - ({x})) & {_hex(_mask(w))})"

    def shift(self, op, x, y, w, signed):
        if op == "<<":
            return f"fb_shl({x}, {y}, {w})"
        if op == ">>":
            return f"fb_lshr({x}, {y}, {w})"
        return f"fb_ashr({x}, {y}, {w})"

    def cmp(self, op, x, y, w, signed):
        if signed and op not in ("==", "!="):
            return f"(fb_sx({x}, {w}) {op} fb_sx({y}, {w}))"
        return f"(({x}) {op} ({y}))"

    def b_not(self, a):
        return f"(!{a})"

    def b_and(self, xs):
        xs = list(xs)
        return "(" + " && ".join(xs) + ")" if xs else "1"

    def b_or(self, xs):
        xs = list(xs)
        return "(" + " || ".join(xs) + ")" if xs else "0"

    def b_iff(self, a, b):
        return f"((!{a}) == (!{b}))"

    def b_true(self):
        return "1"

    def b_false(self):
        return "0"

    def ite(self, c, x, y, w):
        return f"({c} ? ({x}) : ({y}))"

    def to_bool(self, x, w):
        return f"(({x}) != 0)"

    def from_bool(self, b):
        return f"((shield_u64)({b}))"

    def popcount(self, x, w, wo):
        return f"fb_popcount({x})"


PRELUDE = r"""
static inline long long fb_sx(shield_u64 x, unsigned w) {
  shield_u64 m = 1ULL << (w - 1);
  return (long long)((x ^ m) - m);
}
static inline shield_u64 fb_mask(unsigned w) { return w >= 64 ? ~0ULL : ((1ULL << w) - 1ULL); }
static inline shield_u64 fb_udiv(shield_u64 x, shield_u64 y, unsigned w) { return y ? x / y : fb_mask(w); }
static inline shield_u64 fb_urem(shield_u64 x, shield_u64 y) { return y ? x % y : x; }
static inline shield_u64 fb_sdiv(shield_u64 x, shield_u64 y, unsigned w) {
  long long a = fb_sx(x, w), b = fb_sx(y, w);
  if (b == 0) return a >= 0 ? fb_mask(w) : 1ULL;
  if (b == -1) return (0ULL - x) & fb_mask(w);
  return ((shield_u64)(a / b)) & fb_mask(w);
}
static inline shield_u64 fb_srem(shield_u64 x, shield_u64 y, unsigned w) {
  long long a = fb_sx(x, w), b = fb_sx(y, w);
  if (b == 0) return x;
  if (b == -1) return 0ULL;
  return ((shield_u64)(a % b)) & fb_mask(w);
}
static inline shield_u64 fb_shl(shield_u64 x, shield_u64 y, unsigned w) { return y >= w ? 0ULL : (x << y) & fb_mask(w); }
static inline shield_u64 fb_lshr(shield_u64 x, shield_u64 y, unsigned w) { return y >= w ? 0ULL : x >> y; }
static inline shield_u64 fb_ashr(shield_u64 x, shield_u64 y, unsigned w) {
  long long v = fb_sx(x, w);
  return ((shield_u64)(v >> (y >= w ? w - 1 : y))) & fb_mask(w);
}
static inline shield_u64 fb_popcount(shield_u64 x) {
  x = x - ((x >> 1) & 0x5555555555555555ULL);
  x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
  x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
  return (x * 0x0101010101010101ULL) >> 56;
}
""".strip("\n")


@dataclass
class CSource:
    header: str
    source: str
    prefix: str
    header_name: str
    source_name: str


def _array(name: str, ctype: str, values, per_line: int = 16) -> str:
    vals = [str(v) for v in values]
    rows = [", ".join(vals[i:i + per_line]) for i in range(0, len(vals), per_line)]
    body = ",\n  ".join(rows) if rows else "0"
    return f"static const {ctype} {name}[{max(1, len(vals))}] = {{\n  {body}\n}};"


def _pack_node(lv, n: int) -> int:
    lo, hi = lv.child[n]
    return (lv.var[n] << 56) | (hi << 24) | lo


def _idx_type(n: int) -> str:
    return "uint16_t" if n < 65536 else "uint32_t"


def _compact_expr(rel: list[int], word: str) -> str:
    runs = []
    for j, p in enumerate(rel):
        if runs and runs[-1][1] + runs[-1][2] == p and runs[-1][0] + runs[-1][2] == j:
            runs[-1][2] += 1
        else:
            runs.append([j, p, 1])
    terms = []
    for j, p, n in runs:
        t = f"(({word} >> {p}) & {_hex(_mask(n))})" if p else f"({word} & {_hex(_mask(n))})"
        terms.append(f"({t} << {j})" if j else t)
    return "(unsigned)(" + " | ".join(terms) + ")" if terms else "0u"


def generate_c(comp: CompiledShield, prefix: str | None = None, header_name: str = "sv_legality_shield.h",
               source_name: str = "sv_legality_shield.c", aliases: bool = True) -> CSource:
    spec = comp.spec
    P = c_ident(prefix or spec.name)
    PU = P.upper()
    lv = comp.table
    rt = comp.rule_table
    nsb, nab = spec.state_bits, spec.action_bits
    K = len(comp.classes)
    it = _idx_type(len(lv.var))
    rit = _idx_type(len(rt.var))
    node_class = comp.node_class()
    root = lv.index[comp.legal]
    reach_root = lv.index[comp.reach]
    class_nodes = [0] + [lv.index[c.node] for c in comp.classes]
    nrules = min(len(comp.rule_names), 63)

    offsets, off = {}, 0
    for f in comp.fields:
        offsets[f.name] = off
        off += f.mask_words
    mask_words = max(1, off)

    h = [
        f"#ifndef {PU}_SHIELD_H",
        f"#define {PU}_SHIELD_H",
        "",
        "#ifdef __cplusplus",
        'extern "C" {',
        "#endif",
        "",
        "typedef unsigned long long shield_u64;",
        "",
        f"#define {PU}_STATE_BITS {nsb}",
        f"#define {PU}_ACTION_BITS {nab}",
        f"#define {PU}_NUM_CLASSES {K}",
        f"#define {PU}_NUM_RULES {nrules}",
        f"#define {PU}_MASK_WORDS {mask_words}",
        f"#define {PU}_LEGAL 1",
        f"#define {PU}_REPAIRED 0",
        f"#define {PU}_NO_LEGAL_ACTION (-1)",
        f"#define {PU}_FIXED_FIELD_CONFLICT (-2)",
        f"#define {PU}_EXPLAIN_UNREACHABLE (1ULL << 63)",
        "",
    ]
    for f in spec.state:
        h.append(f"#define {PU}_S_{c_ident(f.name).upper()}_LSB {f.lsb}")
        h.append(f"#define {PU}_S_{c_ident(f.name).upper()}_WIDTH {f.width}")
    for f in comp.fields:
        n = c_ident(f.name).upper()
        h.append(f"#define {PU}_A_{n}_LSB {f.lsb}")
        h.append(f"#define {PU}_A_{n}_WIDTH {f.width}")
        h.append(f"#define {PU}_MASK_OFF_{n} {offsets[f.name]}")
        h.append(f"#define {PU}_MASK_LEN_{n} {f.mask_words}")
    for f in spec.state + spec.action:
        for name, v in f.enum:
            h.append(f"#define {PU}_{c_ident(f.name).upper()}_{c_ident(name).upper()} {v}")
    envs = [t for t in spec.transitions if t.kind == "env"]
    for i, t in enumerate(envs):
        h.append(f"#define {PU}_ENV_{c_ident(t.name).upper()} {i}")
    h += [
        "",
        f"int {P}_is_action_legal(shield_u64 state_hash, shield_u64 candidate_tx);",
        f"int {P}_is_state_reachable(shield_u64 state_hash);",
        f"int {P}_class_of(shield_u64 state_hash);",
        f"int {P}_project_or_mask_action(shield_u64 state_hash, shield_u64 candidate_tx, shield_u64 *repaired_tx, shield_u64 *field_masks);",
        f"int {P}_field_intervals(shield_u64 state_hash, int field_id, shield_u64 *lo, shield_u64 *hi, int max_intervals);",
        f"shield_u64 {P}_class_bitmap_word(int class_id, int word);",
        f"shield_u64 {P}_explain(shield_u64 state_hash, shield_u64 candidate_tx);",
        f"shield_u64 {P}_step_action(shield_u64 state_hash, shield_u64 tx);",
        f"shield_u64 {P}_step_env(shield_u64 state_hash, int env_id);",
        f"int {P}_num_env(void);",
        f"const char *{P}_env_name(int env_id);",
        f"const char *{P}_rule_name(int rule_id);",
    ]
    if aliases:
        h += [
            "",
            f"#ifndef {PU}_NO_ALIASES",
            f"#define SHIELD_STATE_BITS {PU}_STATE_BITS",
            f"#define SHIELD_ACTION_BITS {PU}_ACTION_BITS",
            f"#define SHIELD_MASK_WORDS {PU}_MASK_WORDS",
            "int is_action_legal(shield_u64 state_hash, shield_u64 candidate_tx);",
            "int project_or_mask_action(shield_u64 state_hash, shield_u64 candidate_tx, shield_u64 *repaired_tx, shield_u64 *field_masks);",
            "#endif",
        ]
    h += ["", "#ifdef __cplusplus", "}", "#endif", "", f"#endif", ""]

    s = [f'#include "{header_name}"', "#include <stdint.h>", "", PRELUDE, ""]
    s.append(f"#define NSB {nsb}")
    s.append(f"#define NAB {nab}")
    s.append(f"#define DEPTH {lv.depth}")
    s.append(f"#define SDEPTH {comp.state_depth}")
    s.append(f"#define ADEPTH {comp.action_depth}")
    s.append(f"#define RDEPTH {comp.reach_depth}")
    s.append(f"#define XDEPTH {rt.depth}")
    s.append(f"#define ROOT {root}u")
    s.append(f"#define REACH_ROOT {reach_root}u")
    s.append("")
    if max(len(lv.var), len(rt.var)) >= (1 << 24):
        raise ValueError("shield BDD exceeds 16M nodes")
    s.append(_array("fb_node", "shield_u64", [_hex(_pack_node(lv, n)) for n in range(len(lv.var))], 4))
    s.append(_array("fb_class_node", it, class_nodes))
    nc_list = [0] * len(lv.var)
    for n, k in node_class.items():
        nc_list[n] = k
    s.append(_array("fb_node_class", "uint16_t", nc_list))
    s.append(_array("fb_rnode", "shield_u64", [_hex(_pack_node(rt, n)) for n in range(len(rt.var))], 4))
    s.append(_array("fb_rule_root", rit, [rt.index[comp.rules[n]] for n in comp.rule_names[:nrules]]))
    names = ", ".join(f'"{n}"' for n in comp.rule_names[:nrules]) or '""'
    s.append(f"static const char *const fb_rule_names[{max(1, nrules)}] = {{ {names} }};")
    env_names = ", ".join(f'"{t.name}"' for t in envs) or '""'
    s.append(f"static const char *const fb_env_names[{max(1, len(envs))}] = {{ {env_names} }};")
    imm = 0
    for f in comp.fields:
        if not f.mutable:
            imm |= _mask(f.width) << f.lsb
    s.append(f"static const shield_u64 fb_immutable = {_hex(imm)};")
    s.append("")

    narrow = [f for f in comp.fields if f.narrow]
    wide = [f for f in comp.fields if not f.narrow]
    for f in narrow:
        rows = [0] * f.mask_words
        vals = list(rows)
        for c in comp.classes:
            m = c.masks[f.name]
            vals += [(m >> (64 * w)) & ((1 << 64) - 1) for w in range(f.mask_words)]
        s.append(_array(f"fb_mask_{c_ident(f.name)}", "shield_u64", [_hex(v) for v in vals], 4))
    for f in wide:
        cap = max([len(c.intervals[f.name]) for c in comp.classes] + [1])
        lo, hi, cnt = [1] * cap, [0] * cap, [0]
        for c in comp.classes:
            ivs = c.intervals[f.name]
            cnt.append(len(ivs))
            lo += [a for a, _ in ivs] + [1] * (cap - len(ivs))
            hi += [b for _, b in ivs] + [0] * (cap - len(ivs))
        fn = c_ident(f.name)
        s.append(f"#define FB_IVCAP_{fn.upper()} {cap}")
        s.append(_array(f"fb_ivlo_{fn}", "shield_u64", [_hex(v) for v in lo], 4))
        s.append(_array(f"fb_ivhi_{fn}", "shield_u64", [_hex(v) for v in hi], 4))
        s.append(_array(f"fb_ivn_{fn}", "uint8_t", cnt))
    s.append("")

    table_mode = comp.bitmaps is not None
    if table_mode:
        nrel = len(comp.relevant_action_bits)
        words = max(1, (1 << nrel) // 64)
        s.append(f"#define NREL {nrel}")
        s.append(f"#define BM_WORDS {words}")
        s.append(_array("fb_class_of_state", "uint16_t", comp.class_of_state))
        bm = [0] * words
        for b in comp.bitmaps:
            bm += [(b >> (64 * w)) & ((1 << 64) - 1) for w in range(words)]
        s.append(_array("fb_bitmap", "shield_u64", [_hex(v) for v in bm], 4))
        s.append("")
        s.append(f"static inline unsigned fb_compact(shield_u64 tx) {{ return {_compact_expr(comp.relevant_action_bits, 'tx')}; }}")
        s.append("")

    ok_s = "1u" if nsb >= 64 else "(unsigned)((state_hash >> NSB) == 0)"
    ok_a = "1u" if nab >= 64 else "(unsigned)((candidate_tx >> NAB) == 0)"
    s.append(r"""
#define FB_POS(e) ((unsigned)((e) >> 56))
#define FB_CHILD(e, b) ((unsigned)(((e) >> (24u * (b))) & 0xFFFFFFu))

static inline unsigned fb_walk_tab(const shield_u64 *tab, unsigned n, shield_u64 s, shield_u64 tx, int steps) {
  shield_u64 w[2];
  w[0] = s;
  w[1] = tx;
  for (int i = 0; i < steps; ++i) {
    shield_u64 e = tab[n];
    unsigned p = FB_POS(e);
    n = FB_CHILD(e, (unsigned)((w[p >> 6] >> (p & 63u)) & 1u));
  }
  return n;
}

static inline unsigned fb_walk(unsigned n, shield_u64 s, shield_u64 tx, int steps) {
  return fb_walk_tab(fb_node, n, s, tx, steps);
}

static inline unsigned fb_state_phase(shield_u64 s) {
  unsigned n = ROOT;
  for (int i = 0; i < SDEPTH; ++i) {
    shield_u64 e = fb_node[n];
    unsigned p = FB_POS(e);
    unsigned nn = FB_CHILD(e, (unsigned)((s >> (p & 63u)) & 1u));
    n = p < 64u ? nn : n;
  }
  return n;
}
""".strip("\n"))
    s.append("")
    if table_mode:
        s.append(f"static inline unsigned fb_class_index(shield_u64 state_hash) {{ return {ok_s} ? fb_class_of_state[state_hash & {_hex(_mask(nsb))}] : 0u; }}")
    else:
        s.append(f"static inline unsigned fb_class_index(shield_u64 state_hash) {{ unsigned ok = {ok_s}; return ok * fb_node_class[fb_state_phase(state_hash)]; }}")
    s.append("")
    s.append(f"int {P}_is_action_legal(shield_u64 state_hash, shield_u64 candidate_tx) {{")
    s.append(f"  unsigned ok = {ok_s} & {ok_a};")
    if table_mode:
        s.append(f"  unsigned k = fb_class_of_state[state_hash & {_hex(_mask(nsb))}];")
        s.append("  unsigned idx = fb_compact(candidate_tx);")
        s.append("  return (int)(ok & (unsigned)((fb_bitmap[k * BM_WORDS + (idx >> 6)] >> (idx & 63u)) & 1u));")
    else:
        s.append("  return (int)(ok & (unsigned)(fb_walk(ROOT, state_hash, candidate_tx, DEPTH) == 1u));")
    s.append("}")
    s.append("")
    s.append(f"int {P}_is_state_reachable(shield_u64 state_hash) {{")
    s.append(f"  return (int)({ok_s} & (unsigned)(fb_walk(REACH_ROOT, state_hash, 0, RDEPTH) == 1u));")
    s.append("}")
    s.append("")
    s.append(f"int {P}_class_of(shield_u64 state_hash) {{ return (int)fb_class_index(state_hash); }}")
    s.append("")
    s.append(f"static void fb_fill_masks(unsigned k, shield_u64 *m) {{")
    for f in narrow:
        fn = c_ident(f.name)
        for w in range(f.mask_words):
            s.append(f"  m[{offsets[f.name] + w}] = fb_mask_{fn}[k * {f.mask_words} + {w}];")
    for f in wide:
        fn = c_ident(f.name)
        cap = f"FB_IVCAP_{fn.upper()}"
        s.append(f"  m[{offsets[f.name]}] = fb_ivlo_{fn}[k * {cap}];")
        s.append(f"  {{ shield_u64 hi = 0; for (int i = 0; i < {cap}; ++i) {{ shield_u64 v = fb_ivhi_{fn}[k * {cap} + i]; hi = (i < fb_ivn_{fn}[k] && v > hi) ? v : hi; }} m[{offsets[f.name] + 1}] = fb_ivn_{fn}[k] ? hi : 0; }}")
    if not comp.fields:
        s.append("  (void)k; (void)m;")
    s.append("}")
    s.append("")
    s.append(f"int {P}_project_or_mask_action(shield_u64 state_hash, shield_u64 candidate_tx, shield_u64 *repaired_tx, shield_u64 *field_masks) {{")
    s.append("  unsigned k = fb_class_index(state_hash);")
    s.append("  if (field_masks) fb_fill_masks(k, field_masks);")
    s.append("  if (k == 0u) { if (repaired_tx) *repaired_tx = candidate_tx; return -1; }")
    s.append(f"  shield_u64 tx = candidate_tx & {_hex(_mask(nab))};")
    s.append("  shield_u64 out = tx;")
    s.append("  unsigned conflict = 0u;")
    s.append("  unsigned n = fb_class_node[k];")
    s.append("  for (int i = 0; i < ADEPTH; ++i) {")
    s.append("    shield_u64 e = fb_node[n];")
    s.append("    unsigned p = (FB_POS(e) - 64u) & 63u;")
    s.append("    unsigned b = (unsigned)((out >> p) & 1u);")
    s.append("    unsigned dead = (unsigned)(FB_CHILD(e, b) == 0u);")
    s.append("    conflict |= dead & (unsigned)((fb_immutable >> p) & 1u);")
    s.append("    out ^= (shield_u64)dead << p;")
    s.append("    n = FB_CHILD(e, b ^ dead);")
    s.append("  }")
    s.append("  if (repaired_tx) *repaired_tx = out;")
    s.append("  if (out == candidate_tx) return 1;")
    s.append("  return conflict ? -2 : 0;")
    s.append("}")
    s.append("")
    s.append(f"int {P}_field_intervals(shield_u64 state_hash, int field_id, shield_u64 *lo, shield_u64 *hi, int max_intervals) {{")
    s.append("  unsigned k = fb_class_index(state_hash);")
    s.append("  int n = 0;")
    s.append("  switch (field_id) {")
    for i, f in enumerate(comp.fields):
        fn = c_ident(f.name)
        s.append(f"  case {i}:")
        if f.narrow:
            s.append(f"    for (int v = 0; v < {1 << f.width} && n < max_intervals; ++v) {{")
            s.append(f"      if (!((fb_mask_{fn}[k * {f.mask_words} + (v >> 6)] >> (v & 63)) & 1u)) continue;")
            s.append("      if (n > 0 && hi[n - 1] + 1 == (shield_u64)v) { hi[n - 1] = (shield_u64)v; continue; }")
            s.append("      lo[n] = hi[n] = (shield_u64)v; ++n;")
            s.append("    }")
        else:
            cap = f"FB_IVCAP_{fn.upper()}"
            s.append(f"    for (int j = 0; j < fb_ivn_{fn}[k] && n < max_intervals; ++j, ++n) {{ lo[n] = fb_ivlo_{fn}[k * {cap} + j]; hi[n] = fb_ivhi_{fn}[k * {cap} + j]; }}")
        s.append("    break;")
    s.append("  default: break;")
    s.append("  }")
    s.append("  return n;")
    s.append("}")
    s.append("")
    s.append(f"shield_u64 {P}_class_bitmap_word(int class_id, int word) {{")
    if table_mode:
        s.append(f"  if (class_id < 0 || class_id > {K} || word < 0 || word >= BM_WORDS) return 0;")
        s.append("  return fb_bitmap[class_id * BM_WORDS + word];")
    else:
        s.append("  (void)class_id; (void)word;")
        s.append("  return 0;")
    s.append("}")
    s.append("")
    s.append(f"shield_u64 {P}_explain(shield_u64 state_hash, shield_u64 candidate_tx) {{")
    s.append("  shield_u64 out = 0;")
    s.append(f"  for (int r = 0; r < {nrules}; ++r) {{")
    s.append("    unsigned n = fb_walk_tab(fb_rnode, fb_rule_root[r], state_hash, candidate_tx, XDEPTH);")
    s.append("    out |= (shield_u64)(n == 0u) << r;")
    s.append("  }")
    s.append(f"  if (!{P}_is_state_reachable(state_hash)) out |= 1ULL << 63;")
    s.append("  return out;")
    s.append("}")
    s.append("")
    s += _step_functions(comp, P)
    s += [
        f"int {P}_num_env(void) {{ return {len(envs)}; }}",
        f"const char *{P}_env_name(int env_id) {{ return (env_id >= 0 && env_id < {len(envs)}) ? fb_env_names[env_id] : \"\"; }}",
        f"const char *{P}_rule_name(int rule_id) {{ return (rule_id >= 0 && rule_id < {nrules}) ? fb_rule_names[rule_id] : \"\"; }}",
    ]
    if aliases:
        s += [
            "",
            f"#ifndef {PU}_NO_ALIASES",
            f"int is_action_legal(shield_u64 state_hash, shield_u64 candidate_tx) {{ return {P}_is_action_legal(state_hash, candidate_tx); }}",
            "int project_or_mask_action(shield_u64 state_hash, shield_u64 candidate_tx, shield_u64 *repaired_tx, shield_u64 *field_masks) {",
            f"  return {P}_project_or_mask_action(state_hash, candidate_tx, repaired_tx, field_masks);",
            "}",
            "#endif",
        ]
    return CSource("\n".join(h), "\n".join(s) + "\n", P, header_name, source_name)


def _step_functions(comp: CompiledShield, P: str) -> list[str]:
    spec = comp.spec
    vm = {f.name: ("s", f.lsb) for f in spec.state}
    vm.update({f.name: ("tx", f.lsb) for f in spec.action})
    schema = spec.schema()

    def lower():
        return Lowerer(schema, CBackend(vm))

    def pack(nxt: dict) -> str:
        parts = []
        keep = 0
        for f in spec.state:
            if f.name in nxt:
                lw = lower()
                w, sg = lw.selfdet(nxt[f.name])
                v = lw.bv(nxt[f.name], 0, w, sg)
                parts.append(f"((({v}) & {_hex(_mask(f.width))}) << {f.lsb})")
            else:
                keep |= _mask(f.width) << f.lsb
        parts.append(f"(s & {_hex(keep)})")
        return " | ".join(parts)

    out = [f"shield_u64 {P}_step_action(shield_u64 s, shield_u64 tx) {{"]
    for t in spec.transitions:
        if t.kind != "action":
            continue
        out.append(f"  if ({lower().bool(t.when, 0)}) return {pack(t.next)};")
    out += ["  (void)tx;", "  return s;", "}", ""]
    out.append(f"shield_u64 {P}_step_env(shield_u64 s, int env_id) {{")
    out.append("  shield_u64 tx = 0;")
    out.append("  (void)tx;")
    out.append("  switch (env_id) {")
    for i, t in enumerate(t for t in spec.transitions if t.kind == "env"):
        out.append(f"  case {i}: return ({lower().bool(t.when, 0)}) ? ({pack(t.next)}) : s;")
    out += ["  default: return s;", "  }", "}", ""]
    return out
