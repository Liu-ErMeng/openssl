#!/usr/bin/env python3
"""Generate Lean proofs from the saved numerical Pratt certificate."""
import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def generate():
    certificate = json.loads((HERE / "primality-certificate.json").read_text())
    out = ["-- Numerical certificate source: " + certificate['source'],
           "-- Rechecked by Lean 4.19.0; no upstream proof code is imported.",
           "import P384.Pratt", "", "set_option autoImplicit false",
           "set_option maxRecDepth 32768", "set_option maxHeartbeats 8000000",
           "set_option exponentiation.threshold 2048", "", "namespace P384", "namespace Certificate", ""]
    small = {int(n) for n in certificate['small']}
    for n in sorted(small):
        out.append(f"theorem prime_{n} : Nat.Prime {n} := by norm_num")
    for node in certificate['nodes']:
        n, witness, bits = [int(node[key]) for key in ('p', 'witness', 'bits')]
        factors = [int(f) for f in node['factors']]
        fs = "[" + ", ".join(map(str, factors)) + "]"
        out.extend(["", f"theorem prime_{n} : Nat.Prime {n} := by",
                    f"  refine Pratt.prime_of_certificate {n} {witness} {bits} {fs}",
                    "    (by decide) (by decide) ?_ (by decide) (by decide)",
                    "    (by unfold List.Forall; decide)", "  intro f hf",
                    "  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf",
                    "  rcases hf with " + " | ".join("rfl" for _ in factors)])
        out.extend(f"  · exact prime_{f}" for f in factors)
    root = int(certificate['root'])
    out.extend(["", "end Certificate", "", "theorem p_prime : p.Prime := by",
                f"  have hp : p = {root} := by decide", "  rw [hp]",
                f"  exact Certificate.prime_{root}", "", "end P384", ""])
    return "\n".join(out)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    target = HERE / "P384/Prime.lean"
    content = generate()
    if args.check:
        if target.read_text() != content:
            raise SystemExit("Primality certificate/model mismatch")
        print("Primality certificate and Lean proof match")
    else:
        target.write_text(content)


if __name__ == "__main__":
    main()
