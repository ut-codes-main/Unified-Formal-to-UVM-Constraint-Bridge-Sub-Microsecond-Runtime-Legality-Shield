from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from fbridge.shield.bench import run_bench  # noqa: E402
from fbridge.shield.compile import compile_shield  # noqa: E402
from fbridge.shield.inputs import load_shield_spec  # noqa: E402


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description="Benchmark every example shield")
    p.add_argument("--out", default=str(ROOT / "build" / "bench"))
    p.add_argument("--rounds", type=int, default=200000)
    p.add_argument("--budget-ns", type=float, default=1000.0)
    a = p.parse_args(argv)
    results, ok = {}, True
    for spec_path in sorted((ROOT / "examples").glob("*/shield.yaml")):
        comp = compile_shield(load_shield_spec(spec_path))
        res = run_bench(comp, Path(a.out) / spec_path.parent.name, a.rounds)
        results[spec_path.parent.name] = res
        for k in ("is_action_legal", "project_or_mask_action"):
            r = res[k]
            flag = "ok" if r["p99_ns"] < a.budget_ns else "OVER BUDGET"
            ok &= r["p99_ns"] < a.budget_ns
            print(f"{spec_path.parent.name:16s} {res['mode']:5s} {k:24s} p50 {r['p50_ns']:7.1f} ns  p99 {r['p99_ns']:7.1f} ns  {flag}")
    Path(a.out).mkdir(parents=True, exist_ok=True)
    (Path(a.out) / "summary.json").write_text(json.dumps(results, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
