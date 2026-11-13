from __future__ import annotations

import argparse
import json
import random
import struct
import subprocess
import sys
from pathlib import Path

from .build import build_exe
from .compile import ACTION_BASE, CompiledShield, compile_shield
from .emit import write_artifacts
from .inputs import load_shield_spec

HARNESS = Path(__file__).with_name("harness") / "shield_bench.c"


def _word(comp: CompiledShield, assign: dict[int, int], base: int) -> int:
    w = 0
    for v, b in assign.items():
        p = comp.pos.get(v)
        if p is None:
            continue
        if base == 0 and p < ACTION_BASE and b:
            w |= 1 << p
        if base == ACTION_BASE and p >= ACTION_BASE and b:
            w |= 1 << (p - ACTION_BASE)
    return w


def make_samples(comp: CompiledShield, n: int = 4096, legal_ratio: float = 0.5, seed: int = 1) -> list[tuple[int, int]]:
    rng = random.Random(seed)
    m = comp.bdd
    amask = (1 << comp.spec.action_bits) - 1
    out = []
    for _ in range(n):
        if comp.legal != 0 and rng.random() < legal_ratio:
            a = m.sample(comp.legal, comp.state_vars + comp.action_vars, rng)
            out.append((_word(comp, a, 0), _word(comp, a, ACTION_BASE)))
            continue
        a = m.sample(comp.reach, comp.state_vars, rng) if comp.reach != 0 else {}
        out.append((_word(comp, a, 0), rng.getrandbits(64) & amask))
    return out


def run_bench(comp: CompiledShield, out_dir: Path, rounds: int = 200000, samples: int = 4096) -> dict:
    out_dir.mkdir(parents=True, exist_ok=True)
    art = write_artifacts(comp, out_dir)
    exe = build_exe([HARNESS, art.paths["c"]], out_dir / "shield_bench", [out_dir])
    data = out_dir / "samples.bin"
    data.write_bytes(b"".join(struct.pack("<QQ", s, t) for s, t in make_samples(comp, samples)))
    r = subprocess.run([str(exe), str(data), str(rounds)], capture_output=True, text=True, check=True)
    res = json.loads(r.stdout)
    res["shield"] = comp.spec.name
    res["mode"] = comp.mode
    res["stats"] = comp.stats
    (out_dir / "bench.json").write_text(json.dumps(res, indent=2))
    return res


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="shield_bench", description="Compile a shield and measure C evaluator latency")
    p.add_argument("spec")
    p.add_argument("--out", default="build/bench")
    p.add_argument("--rounds", type=int, default=200000)
    p.add_argument("--budget-ns", type=float, default=1000.0)
    a = p.parse_args(argv)
    comp = compile_shield(load_shield_spec(a.spec))
    res = run_bench(comp, Path(a.out), a.rounds)
    for k in ("is_action_legal", "project_or_mask_action"):
        r = res[k]
        print(f"{k:24s} mean {r['mean_ns']:7.1f} ns  p50 {r['p50_ns']:7.1f} ns  p99 {r['p99_ns']:7.1f} ns  p99.9 {r['p999_ns']:7.1f} ns  max(single) {r['max_single_ns']:8.1f} ns")
    worst = max(res[k]["p99_ns"] for k in ("is_action_legal", "project_or_mask_action"))
    print(f"mode={res['mode']} budget={a.budget_ns:.0f} ns  p99 worst={worst:.1f} ns  {'PASS' if worst < a.budget_ns else 'FAIL'}")
    return 0 if worst < a.budget_ns else 1


if __name__ == "__main__":
    sys.exit(main())
