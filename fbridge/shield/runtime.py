from __future__ import annotations

from pathlib import Path

from ..ir.evaluate import holds
from .build import build_shared
from .compile import CompiledShield
from .emit import write_artifacts

CDEF = """
typedef unsigned long long shield_u64;
int {P}_is_action_legal(shield_u64, shield_u64);
int {P}_is_state_reachable(shield_u64);
int {P}_class_of(shield_u64);
int {P}_project_or_mask_action(shield_u64, shield_u64, shield_u64 *, shield_u64 *);
shield_u64 {P}_explain(shield_u64, shield_u64);
shield_u64 {P}_step_action(shield_u64, shield_u64);
shield_u64 {P}_step_env(shield_u64, int);
int {P}_num_env(void);
"""


def initial_states(comp: CompiledShield, limit: int = 64) -> list[int]:
    spec = comp.spec
    out = []
    if spec.state_bits <= 20:
        sch = spec.schema()
        for s in range(1 << spec.state_bits):
            if holds(spec.init, sch, spec.unpack(s, "state")) and comp.bdd.eval(comp.reach, lambda v: _bit(comp, v, s)):
                out.append(s)
                if len(out) >= limit:
                    break
        return out
    a = comp.bdd.pick(comp.reach)
    return [sum(1 << comp.pos[v] for v, b in (a or {}).items() if b and v in comp.pos)]


def _bit(comp: CompiledShield, v: int, s: int) -> int:
    p = comp.pos.get(v)
    return 0 if p is None or p >= 64 else (s >> p) & 1


class ShieldRuntime:
    def __init__(self, comp: CompiledShield, build_dir: str | Path):
        from cffi import FFI
        art = write_artifacts(comp, build_dir)
        self.path = build_shared([art.paths["c"]], Path(build_dir) / "sv_legality_shield")
        self.prefix = art.c.prefix
        self.ffi = FFI()
        self.ffi.cdef(CDEF.replace("{P}", self.prefix))
        self.lib = self.ffi.dlopen(str(self.path))
        self.comp = comp
        self.mask_words = sum(f.mask_words for f in comp.fields) or 1
        self._rep = self.ffi.new("shield_u64 *")
        self._masks = self.ffi.new(f"shield_u64[{self.mask_words}]")
        p = self.prefix
        self.is_action_legal = getattr(self.lib, f"{p}_is_action_legal")
        self.is_state_reachable = getattr(self.lib, f"{p}_is_state_reachable")
        self.class_of = getattr(self.lib, f"{p}_class_of")
        self.explain = getattr(self.lib, f"{p}_explain")
        self.step_action = getattr(self.lib, f"{p}_step_action")
        self.step_env = getattr(self.lib, f"{p}_step_env")
        self.num_env = getattr(self.lib, f"{p}_num_env")()
        self._project = getattr(self.lib, f"{p}_project_or_mask_action")

    def project(self, state: int, tx: int) -> tuple[int, int]:
        st = self._project(state, tx, self._rep, self._masks)
        return st, self._rep[0]

    def masks(self) -> list[int]:
        return list(self._masks)
