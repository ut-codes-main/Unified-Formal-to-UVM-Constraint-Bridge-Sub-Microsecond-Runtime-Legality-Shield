from __future__ import annotations

from ..ir.evaluate import evaluate, holds
from .compile import ACTION_BASE, CompiledShield

LEGAL, REPAIRED, NO_LEGAL_ACTION, FIXED_FIELD_CONFLICT = 1, 0, -1, -2
UNREACHABLE_BIT = 63


class ShieldModel:
    def __init__(self, comp: CompiledShield):
        self.c = comp
        self.spec = comp.spec
        self.sb = comp.spec.state_bits
        self.ab = comp.spec.action_bits
        self.lv = comp.table
        self.root = self.lv.index[comp.legal]
        self.node_class = comp.node_class()
        self.class_nodes = [0] + [self.lv.index[c.node] for c in comp.classes]
        self.rel = comp.relevant_action_bits
        self.immutable = 0
        for f in comp.fields:
            if not f.mutable:
                self.immutable |= ((1 << f.width) - 1) << f.lsb
        self.schema = comp.spec.schema()

    def _bit(self, p: int, s: int, tx: int) -> int:
        return ((tx >> (p - ACTION_BASE)) & 1) if p >= ACTION_BASE else ((s >> p) & 1)

    def well_formed(self, s: int, tx: int) -> bool:
        return (s >> self.sb) == 0 and (tx >> self.ab) == 0

    def boundary_node(self, s: int) -> int:
        if self.c.class_of_state is not None:
            return self.class_nodes[self.c.class_of_state[s]]
        n = self.root
        for _ in range(self.c.state_depth):
            p = self.lv.var[n]
            if p < ACTION_BASE:
                n = self.lv.child[n][(s >> p) & 1]
        return n

    def class_of(self, s: int) -> int:
        if (s >> self.sb) != 0:
            return 0
        n = self.boundary_node(s)
        return 0 if n == 0 else self.node_class[n]

    def is_action_legal(self, s: int, tx: int) -> bool:
        if not self.well_formed(s, tx):
            return False
        if self.c.bitmaps is not None:
            k = self.c.class_of_state[s]
            if k == 0:
                return False
            idx = 0
            for j, b in enumerate(self.rel):
                idx |= ((tx >> b) & 1) << j
            return bool((self.c.bitmaps[k - 1] >> idx) & 1)
        n = self.root
        for _ in range(self.lv.depth):
            n = self.lv.child[n][self._bit(self.lv.var[n], s, tx)]
        return n == 1

    def project_or_mask_action(self, s: int, tx: int) -> tuple[int, int, dict[str, object]]:
        k = self.class_of(s)
        masks = self.field_masks(k)
        if k == 0:
            return NO_LEGAL_ACTION, tx, masks
        orig = tx
        tx &= (1 << self.ab) - 1
        n = self.class_nodes[k]
        out, conflict = tx, False
        for _ in range(self.c.action_depth):
            p = self.lv.var[n] - ACTION_BASE
            b = (out >> p) & 1
            dead = self.lv.child[n][b] == 0
            if dead:
                if (self.immutable >> p) & 1:
                    conflict = True
                out ^= 1 << p
                b ^= 1
            n = self.lv.child[n][b]
        if out == orig:
            return LEGAL, out, masks
        return (FIXED_FIELD_CONFLICT if conflict else REPAIRED), out, masks

    def field_masks(self, k: int) -> dict[str, object]:
        out = {}
        for f in self.c.fields:
            if k == 0:
                out[f.name] = 0 if f.narrow else (1, 0)
                continue
            cl = self.c.classes[k - 1]
            if f.narrow:
                out[f.name] = cl.masks[f.name]
            else:
                ivs = cl.intervals[f.name]
                out[f.name] = (ivs[0][0], max(h for _, h in ivs)) if ivs else (1, 0)
        return out

    def _walk(self, lv, n: int, steps: int, s: int, tx: int) -> int:
        for _ in range(steps):
            n = lv.child[n][self._bit(lv.var[n], s, tx)]
        return n

    def is_state_reachable(self, s: int) -> bool:
        if (s >> self.sb) != 0:
            return False
        return self._walk(self.lv, self.lv.index[self.c.reach], self.c.reach_depth, s, 0) == 1

    def explain(self, s: int, tx: int) -> int:
        out = 0
        lv = self.c.rule_table
        for i, name in enumerate(self.c.rule_names[:UNREACHABLE_BIT]):
            if self._walk(lv, lv.index[self.c.rules[name]], lv.depth, s, tx) == 0:
                out |= 1 << i
        if not self.is_state_reachable(s):
            out |= 1 << UNREACHABLE_BIT
        return out

    def step_action(self, s: int, tx: int) -> int:
        env = {**self.spec.unpack(s, "state"), **self.spec.unpack(tx, "action")}
        for t in self.spec.transitions:
            if t.kind != "action":
                continue
            if holds(t.when, self.schema, env):
                nxt = dict(self.spec.unpack(s, "state"))
                for k, e in t.next.items():
                    nxt[k] = evaluate(e, self.schema, env) & ((1 << self.spec.field(k).width) - 1)
                return self.spec.pack(nxt, "state")
        return s

    def env_transitions(self) -> list[str]:
        return [t.name for t in self.spec.transitions if t.kind == "env"]

    def step_env(self, s: int, env_id: int) -> int:
        envs = [t for t in self.spec.transitions if t.kind == "env"]
        if not 0 <= env_id < len(envs):
            return s
        t = envs[env_id]
        env = self.spec.unpack(s, "state")
        if not holds(t.when, self.schema, env):
            return s
        nxt = dict(env)
        for k, e in t.next.items():
            nxt[k] = evaluate(e, self.schema, env) & ((1 << self.spec.field(k).width) - 1)
        return self.spec.pack(nxt, "state")
