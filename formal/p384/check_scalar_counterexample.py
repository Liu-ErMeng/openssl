#!/usr/bin/env python3
"""Regress scalar cancellation followed by a negative Booth digit."""
from pathlib import Path
import tempfile

from check_scalar_c import G, P, Felem, Point, Scalar, Table17, add, compile_scalar, mul, project, unproject


def run(lib):
    minus_g = G[0], -G[1] % P
    cases = [
        ((32, 16), (minus_g, G), None),
        ((16,), (minus_g,), 32),
        ((0, 16), (None, G), None),
        ((32, 32), (minus_g, G), None),
    ]
    checks = 0
    for values, points, gs in cases:
        for mixed in (0, 1):
            tables = (Table17 * len(points))()
            for table, point in zip(tables, points):
                lib.test_precompute(table, project(point))
            if mixed:
                scratch = (Felem * (17 * len(points) + 1))()
                lib.make_points_affine(17 * len(points), tables, scratch)
                for table, point in zip(tables, points):
                    for j in range(1, 17):
                        if point is None:
                            assert unproject(table[j]) is None
                        else:
                            assert bytes(table[j]) == bytes(project(mul(j, point)))
            expected = None if gs is None else mul(gs, G)
            for value, point in zip(values, points):
                expected = add(expected, mul(value, point))
            scalars = (Scalar * len(values))(*[Scalar.from_buffer_copy(n.to_bytes(48, "little")) for n in values])
            generator = None if gs is None else Scalar.from_buffer_copy(gs.to_bytes(48, "little"))
            raw, contracted, encoded = Point(), Point(), (Scalar * 3)()
            lib.test_batch(raw, scalars, len(points), generator, mixed, tables)
            lib.test_finalize(encoded, contracted, raw)
            x, y, z = (int.from_bytes(bytes(bs), "little") for bs in encoded)
            actual = None
            if z % P:
                zi = pow(z, -1, P)
                actual = x*zi**2 % P, y*zi**3 % P
            assert actual == expected, f"serialized scalar result: mixed={mixed}, scalars={values}, generator={gs}"
            assert unproject(raw) == expected
            assert all(v < 2**56 for coord in raw for v in coord[:6])
            assert all(coord[6] <= 2**48 for coord in raw)
            assert all(v < P for v in (x, y, z))
            checks += 1
    print(f"Scalar cancellation regressions: {checks}; UBSan enabled")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="p384-scalar-counterexample-") as tmp:
        run(compile_scalar(Path(tmp)))
