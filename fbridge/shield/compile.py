from __future__ import annotations

from dataclasses import dataclass, field

from ..bdd import BDD, FALSE, TRUE, BddBackend, Levelized, VarBlock, levelize
from ..ir.ast import Binary, Const, Inside, Next, Rule, Var
from ..ir.semantics import Lowerer
from .inputs import ShieldSpec

STATE_BASE = 0
ACTION_BASE = 64
NARROW_MAX = 8
MAX_INTERVALS = 16


@dataclass
class FieldInfo:
    name: str
    lsb: int
    width: int
    mutable: bool = True

    @property
    def narrow(self) -> bool:
        return self.width <= NARROW_MAX

    @property
    def mask_words(self) -> int:
        return max(1, (1 << self.width) // 64) if self.narrow else 2


@dataclass
class ClassInfo:
    node: int
    states: int = 0
    action_count: int = 0
    masks: dict[str, int] = field(default_factory=dict)
    intervals: dict[str, list[tuple[int, int]]] = field(default_factory=dict)
    approx: dict[str, bool] = field(default_factory=dict)


@dataclass
class CompiledShield:
    spec: ShieldSpec
    bdd: BDD
    legal: int
    reach: int
    rules: dict[str, int]
    pos: dict[int, int]
    state_vars: list[int]
    action_vars: list[int]
    classes: list[ClassInfo]
    table: Levelized
    rule_table: Levelized
    rule_names: list[str]
    reach_depth: int
    state_depth: int
    action_depth: int
    fields: list[FieldInfo]
    reach_iterations: int
    reach_converged: bool
    reachable_states: int
    stats: dict = field(default_factory=dict)
    warnings: list[str] = field(default_factory=list)
    class_of_state: list[int] | None = None
    relevant_action_bits: list[int] = field(default_factory=list)
    bitmaps: list[int] | None = None

    @property
    def mode(self) -> str:
        return "table" if self.bitmaps is not None else "bdd"

    def node_class(self) -> dict[int, int]:
        return {self.table.index[c.node]: i + 1 for i, c in enumerate(self.classes)}


class ShieldCompiler:
    def __init__(self, spec: ShieldSpec, immutable: set[str] | None = None):
        self.spec = spec
        self.immutable = immutable or set()
        self.bdd = BDD()
        self.blocks: dict[tuple[str, int], VarBlock] = {}
        self.pos: dict[int, int] = {}
        self.cur_vars: list[int] = []
        self.next_vars: list[int] = []
        self.action_vars: list[int] = []
        for f in spec.state:
            cur, nxt = [], []
            for bit in reversed(range(f.width)):
                c = self.bdd.add_var(f"{f.name}[{bit}]")
                n = self.bdd.add_var(f"{f.name}'[{bit}]")
                cur.append(c)
                nxt.append(n)
                self.pos[c] = STATE_BASE + f.lsb + bit
            self.blocks[(f.name, 0)] = VarBlock(f.name, f.width, cur, 0)
            self.blocks[(f.name, 1)] = VarBlock(f.name, f.width, nxt, 1)
            self.cur_vars += cur
            self.next_vars += nxt
        for f in sorted(spec.action, key=lambda f: (f.priority, f.lsb)):
            vs = []
            for bit in reversed(range(f.width)):
                v = self.bdd.add_var(f"{f.name}[{bit}]")
                vs.append(v)
                self.pos[v] = ACTION_BASE + f.lsb + bit
            self.blocks[(f.name, 0)] = VarBlock(f.name, f.width, vs, 0)
            self.action_vars += vs
        self.schema = spec.schema()
        self.lw = Lowerer(self.schema, BddBackend(self.bdd, self.blocks))

    def expr_bdd(self, e) -> int:
        return self.lw.bool(e, 0)

    def domain_rules(self) -> list[Rule]:
        out = []
        for f in self.spec.state + self.spec.action:
            if f.enum and len(f.enum) < (1 << f.width):
                items = tuple(Const(v, f.width, False) for _, v in f.enum)
                kind = "domain"
                out.append(Rule(f"domain_{f.name}", Inside(Var(f.name), items), kind))
        return out

    def _frame(self, assigned: dict) -> int:
        eqs = []
        for f in self.spec.state:
            rhs = assigned.get(f.name, Var(f.name))
            eqs.append(self.expr_bdd(Binary("==", Next(Var(f.name), 1), rhs)))
        return self.bdd.and_all(eqs)

    def reachability(self, legal_sa: int, inv: int, domain_s: int) -> tuple[int, int, bool]:
        m = self.bdd
        t_act = FALSE
        t_env = FALSE
        for t in self.spec.transitions:
            rel = m.AND(self.expr_bdd(t.when), self._frame(t.next))
            if t.kind == "env":
                t_env = m.OR(t_env, rel)
            else:
                t_act = m.OR(t_act, rel)
        t_act = m.exists(m.AND(legal_sa, t_act), self.action_vars)
        trans = m.OR(t_act, t_env)
        rename = dict(zip(self.next_vars, self.cur_vars))
        reach = m.and_all([self.expr_bdd(self.spec.init), inv, domain_s])
        if reach == FALSE:
            return FALSE, 0, True
        for it in range(1, self.spec.reach_bound + 1):
            img = m.rename(m.exists(m.AND(reach, trans), self.cur_vars), rename)
            nxt = m.AND(m.OR(reach, img), inv)
            if nxt == reach:
                return reach, it, True
            reach = nxt
        return m.AND(inv, domain_s), self.spec.reach_bound, False

    def compile(self) -> CompiledShield:
        m = self.bdd
        spec = self.spec
        warnings = list(spec.warnings)
        rules: dict[str, int] = {}
        for r in self.domain_rules() + spec.legal:
            rules[r.name] = self.expr_bdd(r.body())
        domain_s = m.and_all(v for k, v in rules.items() if k.startswith("domain_") and k[7:] in {f.name for f in spec.state})
        legal_sa = m.and_all(rules.values())
        inv = m.and_all(self.expr_bdd(i.expr) for i in spec.invariants)
        if spec.transitions:
            reach, iters, converged = self.reachability(legal_sa, inv, domain_s)
            if not converged:
                warnings.append(f"reachability did not converge in {spec.reach_bound} steps; using invariant over-approximation")
        else:
            reach, iters, converged = m.AND(inv, domain_s), 0, True
        legal = m.AND(reach, legal_sa)
        n_state = len(self.cur_vars)
        reachable = m.satcount(reach, self.cur_vars) if reach != FALSE else 0
        boundary = self._boundary(legal)
        fields = [FieldInfo(f.name, f.lsb, f.width, f.name not in self.immutable) for f in spec.action]
        classes = [ClassInfo(n) for n in boundary]
        for c in classes:
            c.action_count = m.satcount(c.node, self.action_vars) if c.node != TRUE else 1 << len(self.action_vars)
            self._field_summaries(c, fields)
        all_roots = [legal] + list(rules.values())
        table = levelize(m, [legal, reach] + [c.node for c in classes], self.pos, ACTION_BASE)
        rule_names = list(rules)
        rule_table = levelize(m, [rules[k] for k in rule_names], self.pos, ACTION_BASE)
        state_depth = m.depth(legal, stop=min(self.action_vars) if self.action_vars else None)
        action_depth = max([m.depth(c.node) for c in classes] + [0])
        comp = CompiledShield(
            spec, m, legal, reach, rules, dict(self.pos), list(self.cur_vars), list(self.action_vars), classes, table,
            rule_table, rule_names, m.depth(reach), state_depth, action_depth, fields, iters, converged, reachable,
            warnings=warnings,
        )
        comp.stats = {
            "bdd_nodes": len(m.nodes(all_roots)),
            "legal_nodes": m.size(legal),
            "table_nodes": len(table.var),
            "classes": len(classes),
            "state_bits": spec.state_bits,
            "action_bits": spec.action_bits,
            "reachable_states": reachable,
            "state_space": 1 << n_state,
            "legal_pairs": m.satcount(legal, self.cur_vars + self.action_vars),
            "depth": table.depth,
            "state_depth": state_depth,
            "action_depth": action_depth,
            "reach_iterations": iters,
        }
        self._table_mode(comp)
        return comp

    def _boundary(self, legal: int) -> list[int]:
        m = self.bdd
        first_action = min(self.action_vars) if self.action_vars else 1 << 30
        out, seen, stack = [], set(), [legal]
        while stack:
            n = stack.pop()
            if n in seen:
                continue
            seen.add(n)
            if n == FALSE:
                continue
            if n == TRUE or m.var_of[n] >= first_action:
                out.append(n)
                continue
            stack += [m.lo[n], m.hi[n]]
        return sorted(out)

    def _field_vars(self, f: FieldInfo) -> list[int]:
        return list(self.blocks[(f.name, 0)].vars)

    def _field_summaries(self, c: ClassInfo, fields: list[FieldInfo]) -> None:
        m = self.bdd
        for f in fields:
            fv = self._field_vars(f)
            others = [v for v in self.action_vars if v not in set(fv)]
            proj = m.exists(c.node, others)
            if f.narrow:
                c.masks[f.name] = bitmap_of(m, proj, list(reversed(fv)))
            else:
                ivs, approx = intervals_of(m, proj, fv, f.width)
                c.intervals[f.name] = ivs
                c.approx[f.name] = approx

    def _table_mode(self, comp: CompiledShield, max_state_bits: int = 16, max_action_bits: int = 16) -> None:
        m = self.bdd
        support = set()
        for c in comp.classes:
            if c.node > TRUE:
                support |= m.support(c.node)
        rel = sorted(self.pos[v] - ACTION_BASE for v in support)
        comp.relevant_action_bits = rel
        if self.spec.state_bits > max_state_bits or len(rel) > max_action_bits:
            return
        nc = comp.node_class()
        cos = []
        lv = comp.table
        root = lv.index[comp.legal]
        for s in range(1 << self.spec.state_bits):
            n = root
            for _ in range(comp.state_depth):
                p = lv.var[n]
                if n > 1 and p < ACTION_BASE:
                    n = lv.child[n][(s >> p) & 1]
            cos.append(0 if n == 0 else nc[n])
        comp.class_of_state = cos
        var_of_bit = {self.pos[v] - ACTION_BASE: v for v in self.action_vars}
        order = [var_of_bit[b] for b in rel]
        comp.bitmaps = [bitmap_of(m, c.node, order) for c in comp.classes]


def _pattern(j: int, nbits: int) -> int:
    period = 1 << (j + 1)
    half = 1 << j
    p = ((1 << half) - 1) << half
    length = period
    total = 1 << nbits
    while length < total:
        p |= p << length
        length <<= 1
    return p


def bitmap_of(m: BDD, root: int, order: list[int]) -> int:
    # Bit i of the result is set iff assigning order[j] := bit j of i satisfies root.
    nbits = len(order)
    full = (1 << (1 << nbits)) - 1
    masks = {v: _pattern(j, nbits) for j, v in enumerate(order)}
    memo: dict[int, int] = {}

    def go(n: int) -> int:
        if n == FALSE:
            return 0
        if n == TRUE:
            return full
        r = memo.get(n)
        if r is None:
            mk = masks[m.var_of[n]]
            r = (go(m.hi[n]) & mk) | (go(m.lo[n]) & ~mk & full)
            memo[n] = r
        return r
    return go(root)


def intervals_of(m: BDD, root: int, msb_first_vars: list[int], width: int, cap: int = MAX_INTERVALS) -> tuple[list[tuple[int, int]], bool]:
    out: list[list[int]] = []
    level = {v: i for i, v in enumerate(msb_first_vars)}

    def emit(lo: int, hi: int) -> bool:
        if out and out[-1][1] + 1 == lo:
            out[-1][1] = hi
        else:
            out.append([lo, hi])
        return len(out) <= cap

    def go(n: int, i: int, prefix: int) -> bool:
        if n == FALSE:
            return True
        rem = width - i
        if n == TRUE:
            return emit(prefix << rem, (prefix << rem) + (1 << rem) - 1)
        lv = level[m.var_of[n]]
        if lv == i:
            return go(m.lo[n], i + 1, prefix << 1) and go(m.hi[n], i + 1, (prefix << 1) | 1)
        return go(n, i + 1, prefix << 1) and go(n, i + 1, (prefix << 1) | 1)

    complete = go(root, 0, 0)
    if not complete or len(out) > cap:
        if not out:
            return [], True
        lo = out[0][0]
        hi = _max_value(m, root, msb_first_vars, width)
        return [(lo, hi)], True
    return [tuple(x) for x in out], False


def _max_value(m: BDD, root: int, msb_first_vars: list[int], width: int) -> int:
    level = {v: i for i, v in enumerate(msb_first_vars)}
    val, n, i = 0, root, 0
    while i < width:
        if n > TRUE and level[m.var_of[n]] == i:
            if m.hi[n] != FALSE:
                val |= 1 << (width - 1 - i)
                n = m.hi[n]
            else:
                n = m.lo[n]
        else:
            val |= 1 << (width - 1 - i)
        i += 1
    return val


def compile_shield(spec: ShieldSpec, immutable: set[str] | None = None) -> CompiledShield:
    return ShieldCompiler(spec, immutable).compile()
