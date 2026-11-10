#!/usr/bin/env python3
import unittest

from generate import SOURCE, body
from generate_contract import generate


class ContractExtraction(unittest.TestCase):
    def setUp(self):
        self.source = SOURCE.read_text()
        self.fragment = body(self.source, "felem_contract")

    def reject(self, old, new):
        self.assertIn(old, self.source)
        with self.assertRaises((ValueError, SyntaxError, KeyError)):
            generate(self.source.replace(old, new, 1))

    def test_unknown_write(self):
        with self.assertRaises(ValueError):
            generate(self.source.replace(self.fragment, self.fragment + "out[0] = 0;"))

    def test_early_return(self):
        with self.assertRaises(ValueError):
            generate(self.source.replace(self.fragment, "if (in[0] == 0) return;" + self.fragment))

    def test_input_copy_size(self):
        self.reject("memcpy(tmp, in, sizeof(felem));", "memcpy(tmp, in, sizeof(limb));")

    def test_output_copy_size(self):
        self.reject("memcpy(out, tmp, sizeof(felem));", "memcpy(out, tmp, sizeof(limb));")

    def test_signed_type(self):
        self.reject("int64_t tmp[NLIMBS], cond[5], a;", "uint64_t tmp[NLIMBS], cond[5], a;")

    def test_loop_bound(self):
        self.reject("for (i = 0; i < 5; i++)", "for (i = 0; i < 4; i++)")

    def test_limb_width(self):
        self.reject("typedef uint64_t limb;", "typedef uint32_t limb;")

    def test_limb_count(self):
        self.reject("#define NLIMBS 7", "#define NLIMBS 8")

    def test_undefined_shift(self):
        self.reject("a = (in[6] >> 48);", "a = (in[6] >> 64);")

    def test_inconsistent_carry(self):
        self.reject("tmp[2] += tmp[1] >> 56;", "tmp[2] += tmp[1] >> 55;")

    def test_mask_change_changes_model(self):
        changed = self.source.replace("tmp[2] &= ~a | 0x0000000001ffff;",
                                      "tmp[2] &= ~a | 0x0000000000ffff;")
        self.assertNotEqual(generate(changed), generate(self.source))


if __name__ == "__main__":
    unittest.main()
