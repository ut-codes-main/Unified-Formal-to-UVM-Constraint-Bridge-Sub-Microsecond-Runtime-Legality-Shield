from __future__ import annotations

import argparse
import json
import random
import sys
import time
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from fbridge.shield.compile import compile_shield  # noqa: E402
from fbridge.shield.inputs import load_shield_spec  # noqa: E402
from fbridge.shield.runtime import ShieldRuntime, initial_states  # noqa: E402


def run(rt: ShieldRuntime, steps: int, shielded: bool, seed: int, idle: float = 0.3) -> dict:
    spec = rt.comp.spec
    rng = random.Random(seed)
    s = initial_states(rt.comp)[0]
    illegal, repaired, issued = 0, 0, 0
    visited, ops, violated = set(), Counter(), Counter()
    names = rt.comp.rule_names
    t0 = time.perf_counter()
    for _ in range(steps):
        visited.add(s)
        if rt.class_of(s) and rng.random() >= idle:
            tx = rng.getrandbits(spec.action_bits)
            if shielded:
                st, tx = rt.project(s, tx)
                repaired += st == 0
            if rt.is_action_legal(s, tx):
                issued += 1
                ops[spec.unpack(tx, "action")["op"]] += 1
                s = rt.step_action(s, tx)
            else:
                illegal += 1
                ex = rt.explain(s, tx)
                for i, n in enumerate(names):
                    if (ex >> i) & 1:
                        violated[n] += 1
        if rng.random() < 0.6:
            s = rt.step_env(s, rng.randrange(rt.num_env))
    dt = time.perf_counter() - t0
    op_names = {v: k for k, v in dict(spec.field("op").enum).items()}
    return {
        "shielded": shielded,
        "steps": steps,
        "issued": issued,
        "illegal": illegal,
        "repaired": repaired,
        "illegal_rate": illegal / max(1, issued + illegal),
        "states_visited": len(visited),
        "formally_unreachable_visits": [spec.unpack(x, "state") for x in sorted(visited) if not rt.is_state_reachable(x)],
        "ops": {op_names.get(k, k): v for k, v in sorted(ops.items())},
        "top_violations": dict(violated.most_common(5)),
        "wall_us_per_step": dt * 1e6 / steps,
    }


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description="Random protocol agent with and without the compiled legality shield")
    p.add_argument("--steps", type=int, default=20000)
    p.add_argument("--seed", type=int, default=7)
    p.add_argument("--idle", type=float, default=0.3, help="probability that the agent stays idle in a cycle")
    p.add_argument("--out", default=str(ROOT / "build" / "mesi_fuzz"))
    a = p.parse_args(argv)
    comp = compile_shield(load_shield_spec(Path(__file__).with_name("shield.yaml")))
    rt = ShieldRuntime(comp, a.out)
    results = [run(rt, a.steps, False, a.seed, a.idle), run(rt, a.steps, True, a.seed, a.idle)]
    for r in results:
        tag = "shielded  " if r["shielded"] else "unshielded"
        print(f"{tag} issued={r['issued']:6d} illegal={r['illegal']:6d} ({r['illegal_rate']:.1%}) repaired={r['repaired']:6d} "
              f"states={r['states_visited']:3d} ops={r['ops']}")
        if r["top_violations"]:
            print(f"           most violated: {r['top_violations']}")
        for st in r["formally_unreachable_visits"]:
            print(f"           model mismatch: tracker reached formally unreachable state {st}")
    Path(a.out).mkdir(parents=True, exist_ok=True)
    (Path(a.out) / "fuzz_results.json").write_text(json.dumps(results, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
