#!/usr/bin/env python3
"""Extract the supported arithmetic fragment; reject unsupported expressions."""
import argparse
import ast
import hashlib
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent.parent / "crypto/ec/ecp_nistp384.c"
LIMIT = 2**128 - 2**125


def body(source, name):
    match = re.search(r"\b" + re.escape(name) + r"\([^;{}]*\)\s*\{", source)
    if not match:
        raise ValueError(f"Function missing: {name}")
    start = match.end()
    depth, end = 1, start
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    return source[start:end - 1]


def expression(text):
    text = re.sub(r"\((?:uint128_t|widelimb|limb)\)", "", text)
    text = re.sub(r"\b(in|in1|in2|inx2|acc)\[(\d+)\]", r"\1_\2", text)
    return ast.parse(" ".join(text.split()), mode="eval").body


def translate(node, names):
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return str(node.value)
    if isinstance(node, ast.Name):
        return names[node.id]
    if isinstance(node, ast.BinOp):
        left, right = translate(node.left, names), translate(node.right, names)
        if isinstance(node.op, ast.BitAnd):
            mask = ast.literal_eval(node.right)
            if mask < 0 or (mask + 1) & mask:
                raise ValueError("Only low-bit masks are supported")
            return f"({left} % {mask + 1})"
        if isinstance(node.op, (ast.LShift, ast.RShift)):
            shift = ast.literal_eval(node.right)
            return f"({left} {'*' if isinstance(node.op, ast.LShift) else '/'} {2**shift})"
        op = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}[type(node.op)]
        return f"({left} {op} {right})"
    raise ValueError(f"Unsupported expression: {ast.dump(node)}")


def interval(node, ranges):
    if isinstance(node, ast.Constant):
        return node.value, node.value
    if isinstance(node, ast.Name):
        return ranges[node.id]
    a, b = interval(node.left, ranges), interval(node.right, ranges)
    if isinstance(node.op, ast.Add):
        return a[0] + b[0], a[1] + b[1]
    if isinstance(node.op, ast.Sub):
        return a[0] - b[1], a[1] - b[0]
    if isinstance(node.op, ast.Mult):
        values = [x*y for x in a for y in b]
        return min(values), max(values)
    if isinstance(node.op, ast.LShift):
        return a[0] << b[0], a[1] << b[0]
    if isinstance(node.op, ast.RShift):
        return a[0] >> b[0], a[1] >> b[0]
    if isinstance(node.op, ast.BitAnd):
        return 0, b[0]
    raise ValueError(ast.dump(node))


def vector(values):
    return "![" + ", ".join(values) + "]"


def reduction_fragment(source):
    fragment = body(source, "felem_reduce_ref")
    constant = r"\s*static const widelimb\s+\w+\s*=[^;]+;"
    step = r"\s*(?:acc\[[0-8]\]|temp)\s*(?:\+=|-=|&=|=)\s*[^;]+;"
    pos = 0
    while match := re.compile(constant).match(fragment, pos):
        pos = match.end()
    constants = fragment[:pos]
    if not constants.strip():
        raise ValueError("Missing reduction constants")
    for pattern in (
        r"\s*widelimb\s+temp\s*,\s*acc\[9\]\s*;",
        r"\s*unsigned int\s+i\s*;",
        r"\s*memcpy\(acc,\s*in,\s*sizeof\(widelimb\)\s*\*\s*9\);",
    ):
        match = re.compile(pattern).match(fragment, pos)
        if match is None:
            raise ValueError("Unmodeled reduction declarations or input copy")
        pos = match.end()
    start = pos
    while match := re.compile(step).match(fragment, pos):
        pos = match.end()
    steps = fragment[start:pos]
    tail = (
        r"\s*for\s*\(i\s*=\s*0;\s*i\s*<\s*NLIMBS;\s*i\+\+\)"
        r"\s*out\[i\]\s*=\s*acc\[i\];\s*"
    )
    if not steps.strip() or re.fullmatch(tail, fragment[pos:]) is None:
        raise ValueError("felem_reduce_ref contains unmodeled C statements")
    if re.search(r"\b(?:limb|uint64_t|int64_t)\b", constants):
        raise ValueError("Unexpected constant width in felem_reduce_ref")
    if re.search(r"\b(?:limb|widelimb|uint\w*|int\w*)\b", steps):
        raise ValueError("Unmodeled cast in felem_reduce_ref")
    return fragment


def product_assignments(source, name):
    fragment = body(source, name)
    pos = 0
    if name == "felem_square_ref":
        prefix = re.match(r"\s*felem\s+inx2;\s*felem_scalar\(inx2,\s*in,\s*2\);", fragment)
        if prefix is None:
            raise ValueError("Unmodeled square input doubling")
        pos = prefix.end()
        scalar = body(source, "felem_scalar")
        if re.fullmatch(
            r"\s*unsigned int\s+i;\s*for\s*\(i\s*=\s*0;\s*i\s*<\s*NLIMBS;\s*i\+\+\)"
            r"\s*out\[i\]\s*=\s*in\[i\]\s*\*\s*scalar;\s*", scalar
        ) is None:
            raise ValueError("Unmodeled felem_scalar dependency")
        term = r"\(\(uint128_t\)in\[[0-6]\]\)\s*\*\s*(?:in|inx2)\[[0-6]\]"
    else:
        term = r"\(\(uint128_t\)in1\[[0-6]\]\)\s*\*\s*in2\[[0-6]\]"
    assignments = []
    statement = re.compile(r"\s*out\[(\d+)\]\s*=\s*([^;]+);")
    for i in range(13):
        match = statement.match(fragment, pos)
        if match is None or int(match[1]) != i:
            raise ValueError(f"Unmodeled assignment in {name}")
        value = match[2]
        if re.fullmatch(rf"\s*{term}(?:\s*\+\s*{term})*\s*", value) is None:
            raise ValueError(f"Unmodeled widening or arithmetic in {name}")
        assignments.append((str(i), value))
        pos = match.end()
    if fragment[pos:].strip():
        raise ValueError(f"Unmodeled trailing statements in {name}")
    return assignments


def generate_products(source):
    source = re.sub(r"/\*.*?\*/", "", source, flags=re.S)
    out = ["-- Generated by generate.py from the C multiplication and square.",
           "import P384.GeneratedMachine", "", "set_option autoImplicit false", "", "namespace P384", ""]
    for c_name, lean_name, args in (
        ("felem_mul_ref", "machineMul", "(a b : LimbWords)"),
        ("felem_square_ref", "machineSquare", "(a : LimbWords)"),
    ):
        names = {f"in_{i}": f"((a {i}).setWidth 128)" for i in range(7)}
        names.update({f"inx2_{i}": f"((a {i} * 2).setWidth 128)" for i in range(7)})
        for c_arg, lean_arg in (("in1", "a"), ("in2", "b")):
            names.update({f"{c_arg}_{i}": f"(({lean_arg} {i}).setWidth 128)" for i in range(7)})
        out.append(f"def {lean_name} {args} : WideWords :=")
        out.append("  ![")
        for i, value in product_assignments(source, c_name):
            out.append("    " + word_expression(expression(value), names) + ("," if int(i) < 12 else "]"))
        out.append("")
    out.extend(["end P384", ""])
    return "\n".join(out)


def validate_wrappers(source):
    wrappers = {
        "felem_assign": r"\s*memcpy\(out,\s*in,\s*sizeof\(felem\)\);\s*",
        "felem_square_reduce_ref": (
            r"\s*widefelem\s+tmp;\s*felem_square_ref\(tmp,\s*in\);"
            r"\s*felem_reduce_ref\(out,\s*tmp\);\s*"
        ),
        "felem_mul_reduce_ref": (
            r"\s*widefelem\s+tmp;\s*felem_mul_ref\(tmp,\s*in1,\s*in2\);"
            r"\s*felem_reduce_ref\(out,\s*tmp\);\s*"
        ),
    }
    for name, grammar in wrappers.items():
        if re.fullmatch(grammar, body(source, name)) is None:
            raise ValueError(f"Unmodeled wrapper: {name}")


def generate_zero(source):
    source = re.sub(r"/\*.*?\*/", "", source, flags=re.S)
    fragment = body(source, "felem_is_zero")
    masks = re.findall(r"in\[(\d+)\]\s*\^\s*(0x[0-9a-fA-F]+)", fragment)
    if [int(i) for i, _ in masks] != list(range(7)):
        raise ValueError("Unmodeled zero-test constants")
    expected = (
        "limb zero, p384; zero = " + " | ".join(f"in[{i}]" for i in range(7)) + ";"
        "zero = ((int64_t)(zero)-1) >> 63; p384 = "
        + " | ".join(f"(in[{i}] ^ {value})" for i, value in masks)
        + "; p384 = ((int64_t)(p384)-1) >> 63; return (zero | p384);"
    )
    compact = lambda value: re.sub(r"\s+", "", value)
    if compact(fragment) != compact(expected):
        raise ValueError("felem_is_zero contains unmodeled C statements")
    if compact(body(source, "felem_is_zero_int")) != "return(int)(felem_is_zero(in)&((limb)1));":
        raise ValueError("Unmodeled zero-test integer wrapper")
    out = ["-- Generated by generate.py from felem_is_zero and felem_is_zero_int.",
           "import P384.GeneratedMachine", "import P384.Words", "", "set_option autoImplicit false", "",
           "namespace P384", "", "def zeroPrimeLimbs : Felem :=",
           "  " + vector([str(int(value, 16)) for _, value in masks]), "",
           "def zeroPrimeWords : LimbWords := fun i => BitVec.ofInt 64 (zeroPrimeLimbs i)", "",
           "def limbOr (a : LimbWords) : BitVec 64 :=",
           "  " + " ||| ".join(f"a {i}" for i in range(7)), "",
           "def xorPrime (a : LimbWords) : LimbWords := fun i => a i ^^^ zeroPrimeWords i", "",
           "def machineIsZero (a : LimbWords) : BitVec 64 :=",
           "  zeroMask (limbOr a) ||| zeroMask (limbOr (xorPrime a))", "",
           "def machineIsZeroInt (a : LimbWords) : ℕ := (machineIsZero a &&& 1).toNat", "",
           "end P384", ""]
    return "\n".join(out)


def inversion_calls(source):
    fragment = body(source, "felem_inv")
    prefix = re.match(
        r"\s*felem\s+ftmp,\s*ftmp2,\s*ftmp3,\s*ftmp4,\s*ftmp5,\s*ftmp6;"
        r"\s*unsigned int\s+i\s*=\s*0;", fragment
    )
    if prefix is None:
        raise ValueError("Unmodeled inverse declarations")
    pos = prefix.end()
    initialized = {"in"}
    temporaries = {"ftmp", "ftmp2", "ftmp3", "ftmp4", "ftmp5", "ftmp6"}
    calls = []
    loop = re.compile(
        r"\s*for\s*\(i\s*=\s*0;\s*i\s*<\s*(\d+);\s*i\+\+\)"
        r"\s*felem_square_reduce\((\w+),\s*(\w+)\);"
    )
    call = re.compile(r"\s*(felem_square_reduce|felem_mul_reduce|felem_assign)\(([^();]+)\);")
    while re.fullmatch(r"\s*memcpy\(out,\s*ftmp,\s*sizeof\(felem\)\);\s*", fragment[pos:]) is None:
        if match := loop.match(fragment, pos):
            count, dest, src = match.groups()
            if dest != src or not 0 <= int(count) <= 384:
                raise ValueError("Unmodeled inverse square loop")
            name, args = "square_n", [dest, src, count]
            inputs = [src]
        elif match := call.match(fragment, pos):
            name, arguments = match.groups()
            args = [value.strip() for value in arguments.split(",")]
            arity = 3 if name == "felem_mul_reduce" else 2
            if len(args) != arity:
                raise ValueError("Unmodeled inverse call arity")
            inputs = args[1:]
        else:
            raise ValueError("felem_inv contains unmodeled C statements")
        if args[0] not in temporaries or any(value not in initialized for value in inputs):
            raise ValueError("Uninitialized inverse operand")
        initialized.add(args[0])
        calls.append((name, ", ".join(args)))
        pos = match.end()
    if "ftmp" not in initialized:
        raise ValueError("Missing inverse output")
    return calls


def bounds_proof(node, names, proofs):
    if isinstance(node, ast.Constant):
        return "(And.intro (le_refl _) (le_refl _))"
    if isinstance(node, ast.Name):
        return proofs[node.id]
    left = bounds_proof(node.left, names, proofs)
    if isinstance(node.op, (ast.Add, ast.Sub)):
        right = bounds_proof(node.right, names, proofs)
        lemma = "bounds_add" if isinstance(node.op, ast.Add) else "bounds_sub"
        return f"({lemma} {left} {right})"
    if isinstance(node.op, (ast.LShift, ast.RShift)):
        k = 2**ast.literal_eval(node.right)
        lemma = "bounds_scale" if isinstance(node.op, ast.LShift) else "bounds_div"
        return f"({lemma} {left} {k} (by norm_num))"
    if isinstance(node.op, ast.BitAnd):
        k = ast.literal_eval(node.right) + 1
        return f"(bounds_mod {translate(node.left, names)} {k} (by norm_num))"
    raise ValueError(ast.dump(node))


def word_expression(node, names):
    if isinstance(node, ast.Constant):
        return f"(BitVec.ofInt 128 {node.value})"
    if isinstance(node, ast.Name):
        return names[node.id]
    left = word_expression(node.left, names)
    if isinstance(node.op, ast.BitAnd):
        mask = ast.literal_eval(node.right)
        if mask < 0 or (mask + 1) & mask:
            raise ValueError("Only low-bit masks are supported")
        return f"({left} &&& BitVec.ofNat 128 {mask})"
    if isinstance(node.op, (ast.LShift, ast.RShift)):
        shift = ast.literal_eval(node.right)
        if not 0 <= shift < 128:
            raise ValueError("Undefined C shift")
        op = "<<<" if isinstance(node.op, ast.LShift) else ">>>"
        return f"({left} {op} {shift})"
    right = word_expression(node.right, names)
    op = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}[type(node.op)]
    return f"({left} {op} {right})"


def word_proof(node, names, ranges, proofs, word_proofs):
    if isinstance(node, ast.Constant):
        return "(Eq.refl _)"
    if isinstance(node, ast.Name):
        return word_proofs[node.id]
    left = word_proof(node.left, names, ranges, proofs, word_proofs)
    value = translate(node.left, names)
    lo, hi = interval(node.left, ranges)
    if not 0 <= lo <= hi < 2**128:
        raise ValueError("Word operand is outside 128 bits")
    bound = f"(within_of_bounds {bounds_proof(node.left, names, proofs)} 128 (by norm_num) (by norm_num))"
    if isinstance(node.op, ast.BitAnd):
        mask = ast.literal_eval(node.right)
        n = (mask + 1).bit_length() - 1
        lifted = f"(congrArg (fun x : BitVec 128 => x &&& BitVec.ofNat 128 {mask}) {left})"
        return f"({lifted}.trans (ofInt_mask 128 {value} {bound} {n} (by decide)))"
    if isinstance(node.op, (ast.LShift, ast.RShift)):
        n = ast.literal_eval(node.right)
        if isinstance(node.op, ast.LShift):
            op, lemma = "<<<", f"ofInt_shiftLeft 128 {value} {n}"
        else:
            op, lemma = ">>>", f"ofInt_shiftRight 128 {value} {bound} {n}"
        lifted = f"(congrArg (fun x : BitVec 128 => x {op} {n}) {left})"
        return f"({lifted}.trans ({lemma}))"
    right = word_proof(node.right, names, ranges, proofs, word_proofs)
    op, lemma = {
        ast.Add: ("+", "(BitVec.ofInt_add _ _).symm"),
        ast.Sub: ("-", "(ofInt_sub 128 _ _)"),
        ast.Mult: ("*", "(BitVec.ofInt_mul _ _).symm"),
    }[type(node.op)]
    return f"((congrArg₂ (fun x y : BitVec 128 => x {op} y) {left} {right}).trans {lemma})"


def generate_machine(trace, outputs, shifts):
    out = ["-- Generated by generate.py from felem_reduce_ref.",
           "import P384.WordSemantics", "import P384.Reduction", "",
           "set_option autoImplicit false", "set_option maxRecDepth 16384",
           "set_option maxHeartbeats 8000000", "", "namespace P384", "",
           "abbrev WideWords := Fin 13 → BitVec 128", "abbrev LimbWords := Fin 7 → BitVec 64", "",
           "structure WordReductionTrace where", "  limbs : LimbWords", "  steps : List (BitVec 128)", "",
           "def machineReduceTrace (a : WideWords) : WordReductionTrace :="]
    out.extend(f"  let w{name[1:]} : BitVec 128 := {word}" for name, _, _, _, _, word, _ in trace)
    limbs = vector([f"(w{name[1:]}.setWidth 64)" for name in outputs])
    steps = "[" + ", ".join("w" + name[1:] for name, *_ in trace) + "]"
    ints = "[" + ", ".join(name for name, *_ in trace) + "]"
    out.extend([f"  ⟨{limbs}, {steps}⟩", "",
                "def machineReduce (a : WideWords) : LimbWords := (machineReduceTrace a).limbs", "",
                "theorem machineReduce_shifts_defined :",
                "    List.Forall (fun n : ℕ => n < 128) [" + ", ".join(map(str, shifts)) + "] := by",
                "  unfold List.Forall", "  decide", "",
                "theorem machineReduceTrace_refines (a : Widefelem)",
                f"    (ha : ∀ i, 0 ≤ a i ∧ a i < {LIMIT}) :",
                "    (fun i => unsigned ((machineReduceTrace (fun j => BitVec.ofInt 128 (a j))).limbs i)) = reduce a ∧",
                "      (machineReduceTrace (fun j => BitVec.ofInt 128 (a j))).steps.map unsigned = (reduceTrace a).steps := by",
                "  let input : WideWords := fun i => BitVec.ofInt 128 (a i)"])
    out.extend(f"  have ha{i} : 0 ≤ a {i} ∧ a {i} ≤ {LIMIT-1} := by have := ha {i}; omega" for i in range(13))
    for name, value, lo, hi, proof, word, equality in trace:
        word_name = "w" + name[1:]
        out.extend([f"  let {name} : ℤ := {value}",
                    f"  have h{name} : {lo} ≤ {name} ∧ {name} ≤ {hi} := {proof}",
                    f"  let {word_name} : BitVec 128 := {word.replace('(a ', '(input ')}",
                    f"  have h{word_name} : {word_name} = BitVec.ofInt 128 {name} := {equality}",
                    f"  have hv{name[1:]} : unsigned {word_name} = {name} := by",
                    f"    rw [h{word_name}]",
                    f"    exact unsigned_ofInt_exact 128 {name} (within_of_bounds h{name} 128 (by norm_num) (by norm_num))"])
    out.extend(["  constructor", "  · funext i", "    fin_cases i"])
    for name in outputs:
        word_name = "w" + name[1:]
        out.extend([f"    · change unsigned ({word_name}.setWidth 64) = {name}",
                    f"      rw [h{word_name}]",
                    f"      exact unsigned_setWidth_ofInt 128 64 {name}",
                    f"        (within_of_bounds h{name} 128 (by norm_num) (by norm_num))",
                    f"        (within_of_bounds h{name} 64 (by norm_num) (by norm_num))"])
    out.extend([f"  · change List.map unsigned {steps} = {ints}",
                "    simp only [List.map_cons, List.map_nil, " + ", ".join("hv" + name[1:] for name, *_ in trace) + "]", "",
                "theorem machineReduce_refines (a : Widefelem)",
                f"    (ha : ∀ i, 0 ≤ a i ∧ a i < {LIMIT}) :",
                "    (fun i => unsigned (machineReduce (fun j => BitVec.ofInt 128 (a j)) i)) = reduce a :=",
                "  (machineReduceTrace_refines a ha).1", "",
                "theorem machineReduce_correct (a : WideWords)",
                f"    (ha : ∀ i, unsigned (a i) < {LIMIT}) :",
                "    Congruent (eval7 (fun i => unsigned (machineReduce a i))) (eval13 (fun i => unsigned (a i))) ∧",
                "      Reduced (fun i => unsigned (machineReduce a i)) := by",
                f"  have hi : ∀ i, 0 ≤ unsigned (a i) ∧ unsigned (a i) < {LIMIT} :=",
                "    fun i => ⟨(unsigned_bounds (a i)).1, ha i⟩",
                "  have he : (fun i => BitVec.ofInt 128 (unsigned (a i))) = a := by",
                "    funext i", "    exact ofInt_unsigned (a i)",
                "  have hr := machineReduce_refines (fun i => unsigned (a i)) hi", "  rw [he] at hr",
                "  rw [hr]", "  exact ⟨reduce_correct _, (reduce_bounds _ hi).1⟩", "", "end P384", ""])
    return "\n".join(out)


def generate(source, machine=False):
    clean = re.sub(r"/\*.*?\*/", "", source, flags=re.S)
    defines = re.findall(r"^\s*#\s*define\s+NLIMBS\b([^\n]*)", clean, flags=re.M)
    if [value.strip() for value in defines] != ["7"] or re.search(r"#\s*undef\s+NLIMBS\b", clean):
        raise ValueError("The model requires NLIMBS = 7")
    for declaration in (r"typedef\s+uint64_t\s+limb\s*;", r"typedef\s+uint128_t\s+widelimb\s*;"):
        if re.search(declaration, clean) is None:
            raise ValueError("The model requires 64/128-bit unsigned limbs")
    validate_wrappers(clean)
    out = ["-- Generated by generate.py from crypto/ec/ecp_nistp384.c.",
           "import P384.Basic", "", "set_option autoImplicit false",
           "set_option maxRecDepth 8192", "set_option maxHeartbeats 4000000",
           "", "namespace P384", ""]
    for c_name, lean_name, count, arg_names in [
        ("felem_mul_ref", "mul", 13, ["a", "b"]),
        ("felem_square_ref", "square", 13, ["a"]),
    ]:
        names = {f"in_{i}": f"(a {i})" for i in range(7)}
        names.update({f"inx2_{i}": f"(2 * a {i})" for i in range(7)})
        for c_arg, lean_arg in [("in1", "a"), ("in2", "b")]:
            names.update({f"{c_arg}_{i}": f"({lean_arg} {i})" for i in range(7)})
        assignments = product_assignments(clean, c_name)
        args = " ".join(f"({name} : Felem)" for name in arg_names)
        out.extend([f"def {lean_name} {args} : Widefelem :=", "  !["])
        out.extend("    " + translate(expression(value), names) + ("," if int(i) < count-1 else "]")
                   for i, value in assignments)
        out.append("")

    for c_name, lean_name, count in [
        ("felem_neg", "pad64", 7),
        ("felem_diff_128_64", "pad128_64", 7),
        ("felem_diff128", "pad128", 13),
    ]:
        fragment = body(clean, c_name)
        constants, ranges = {}, {}
        for name, value in re.findall(r"static const (?:wide)?limb\s+(\w+)\s*=\s*(.*?);", fragment, re.S):
            node = expression(value)
            lo, hi = interval(node, ranges)
            assert lo == hi
            constants[name] = str(lo)
            ranges[name] = (lo, hi)
        assignments = re.findall(r"out\[(\d+)\]\s*(?:\+?=)\s*(\w+)", fragment)
        assert [int(i) for i, _ in assignments] == list(range(count))
        out.extend([f"def {lean_name} : {'Felem' if count == 7 else 'Widefelem'} :=",
                    "  " + vector([constants[value] for _, value in assignments]), ""])

    fragment = reduction_fragment(clean)
    names, ranges, proofs, word_names, word_proofs = {}, {}, {}, {}, {}
    for name, value in re.findall(r"static const widelimb\s+(\w+)\s*=\s*(.*?);", fragment, re.S):
        lo, hi = interval(expression(value), ranges)
        assert lo == hi
        names[name], ranges[name] = str(lo), (lo, hi)
        proofs[name] = "(And.intro (le_refl _) (le_refl _))"
        word_names[name] = f"(BitVec.ofInt 128 {lo})"
        word_proofs[name] = "(Eq.refl _)"
    for i in range(13):
        names[f"in_{i}"] = f"(a {i})"
        ranges[f"in_{i}"] = (0, LIMIT-1)
        proofs[f"in_{i}"] = f"ha{i}"
        word_names[f"in_{i}"] = f"(a {i})"
        word_proofs[f"in_{i}"] = "(Eq.refl _)"
    for i in range(9):
        names[f"acc_{i}"] = f"(a {i})"
        ranges[f"acc_{i}"] = (0, LIMIT-1)
        proofs[f"acc_{i}"] = f"ha{i}"
        word_names[f"acc_{i}"] = f"(a {i})"
        word_proofs[f"acc_{i}"] = "(Eq.refl _)"
    trace = []
    shifts = []
    quotient_terms = []
    quotient_terms.extend(f"a {i} * {2**(56*i-384)}" for i in range(9, 13))
    for target, op, value in re.findall(r"(acc\[\d+\]|temp)\s*(\+=|-=|&=|=)\s*(.*?);", fragment, re.S):
        target = re.sub(r"\[(\d+)\]", r"_\1", target)
        node = expression(value)
        if target == "acc_4" and op == "+=" and value.strip() == "acc[8] >> 32":
            quotient_terms.append(f"{names['acc_8']} * {2**64}")
        if target == "acc_3" and op == "+=" and value.strip() == "acc[7] >> 32":
            quotient_terms.append(f"{names['acc_7']} * {2**8}")
        if op != "=":
            node = ast.BinOp(ast.Name(target), {"+=": ast.Add(), "-=": ast.Sub(), "&=": ast.BitAnd()}[op], node)
        value_lean = translate(node, names)
        lo, hi = interval(node, ranges)
        if not (0 <= lo <= hi < 2**128):
            raise ValueError(f"Unproved interval at {target}: {(lo, hi)}")
        name = f"r{len(trace)}"
        for child in ast.walk(node):
            if isinstance(child, ast.BinOp) and isinstance(child.op, (ast.LShift, ast.RShift)):
                shifts.append(ast.literal_eval(child.right))
        trace.append((name, value_lean, lo, hi, bounds_proof(node, names, proofs),
                      word_expression(node, word_names), word_proof(node, names, ranges, proofs, word_proofs)))
        names[target], ranges[target] = name, (lo, hi)
        proofs[target] = "h" + name
        word_names[target] = "w" + name[1:]
        word_proofs[target] = "hw" + name[1:]
        if target == "temp":
            quotient_terms.append(name)
    limbs = vector([names[f"acc_{i}"] for i in range(7)])
    steps = "[" + ", ".join(name for name, *_ in trace) + "]"
    quotient = " + ".join(quotient_terms)
    assert len(quotient_terms) == 7
    if machine:
        return generate_machine(trace, [names[f"acc_{i}"] for i in range(7)], shifts)
    out.extend(["structure ReductionTrace where", "  limbs : Felem", "  quotient : ℤ",
                "  steps : List ℤ", "", "def reduceTrace (a : Widefelem) : ReductionTrace :="])
    out.extend(f"  let {name} : ℤ := {value}" for name, value, *_ in trace)
    out.extend([f"  ⟨{limbs}, {quotient}, {steps}⟩", "",
                "def reduce (a : Widefelem) : Felem := (reduceTrace a).limbs", ""])

    out.extend(["theorem reduce_bounds (a : Widefelem)",
                f"    (ha : ∀ i, 0 ≤ a i ∧ a i < {LIMIT}) :",
                "    Reduced (reduce a) ∧ (reduceTrace a).steps.Forall (Within 128) := by"])
    out.extend(f"  have ha{i} : 0 ≤ a {i} ∧ a {i} ≤ {LIMIT-1} := by have := ha {i}; omega" for i in range(13))
    for name, value, lo, hi, proof, *_ in trace:
        out.append(f"  let {name} : ℤ := {value}")
        out.append(f"  have h{name} : {lo} ≤ {name} ∧ {name} ≤ {hi} := {proof}")
    out.extend([f"  change Reduced {limbs} ∧ List.Forall (Within 128) {steps}", "  constructor",
                "  · constructor", "    · intro i", "      fin_cases i"])
    for i in range(6):
        out.append(f"      · exact within_of_bounds {proofs[f'acc_{i}']} 56 (by norm_num) (by norm_num)")
    out.extend([f"    · exact ⟨(by norm_num : (0 : ℤ) ≤ {ranges['acc_6'][0]}).trans {proofs['acc_6']}.1,",
                f"        {proofs['acc_6']}.2.trans (by norm_num)⟩", "  ·"])
    proof = ",\n      ".join(f"within_of_bounds h{name} 128 (by norm_num) (by norm_num)" for name, *_ in trace)
    out.extend(["    exact ⟨" + proof + "⟩", ""])
    out.extend(["def invProgram {α : Type} (sq : α → α) (times : α → α → α) (x : α) : α :="])
    names = {"in": "x"}
    calls = inversion_calls(clean)
    if len(calls) != 35:
        raise ValueError("Changed inverse program length")
    inv_trace = []
    inv_proofs = {"in": "hx"}
    for i, (call, arguments) in enumerate(calls):
        args = [arg.strip() for arg in arguments.split(",")]
        if call == "felem_square_reduce":
            value = f"sq {names[args[1]]}"
            proof = f"hs _ {inv_proofs[args[1]]}"
        elif call == "felem_mul_reduce":
            value = f"times {names[args[1]]} {names[args[2]]}"
            proof = f"hm _ _ {inv_proofs[args[1]]} {inv_proofs[args[2]]}"
        elif call == "felem_assign":
            value = names[args[1]]
            proof = inv_proofs[args[1]]
        elif call == "square_n":
            value = f"squares sq {args[2]} {names[args[1]]}"
            proof = f"squares_preserves sq prop hs {args[2]} _ {inv_proofs[args[1]]}"
        name = f"t{i}"
        out.append(f"  let {name} := {value}")
        inv_trace.append((name, value, proof))
        names[args[0]] = name
        inv_proofs[args[0]] = "h" + name
    out.extend(["  " + names["ftmp"], "",
        "theorem invProgram_preserves {α : Type} (prop : α → Prop)",
        "    (sq : α → α) (times : α → α → α)",
        "    (hs : ∀ x, prop x → prop (sq x))",
        "    (hm : ∀ x y, prop x → prop y → prop (times x y))",
        "    (x : α) (hx : prop x) : prop (invProgram sq times x) := by"])
    for name, value, proof in inv_trace:
        out.extend([f"  let {name} := {value}", f"  have h{name} : prop {name} := {proof}"])
    out.extend(["  exact " + inv_proofs["ftmp"], "", "end P384", ""])
    return "\n".join(out)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = SOURCE.read_text()
    content = generate(source)
    machine_content = generate(source, machine=True)
    products_content = generate_products(source)
    zero_content = generate_zero(source)
    generated = HERE / "P384/Generated.lean"
    machine_generated = HERE / "P384/GeneratedMachine.lean"
    products_generated = HERE / "P384/GeneratedProducts.lean"
    zero_generated = HERE / "P384/GeneratedZero.lean"
    digest = HERE / "source.sha256"
    expected = hashlib.sha256(SOURCE.read_bytes()).hexdigest() + "  crypto/ec/ecp_nistp384.c\n"
    if args.check:
        if (generated.read_text() != content or machine_generated.read_text() != machine_content
                or products_generated.read_text() != products_content or zero_generated.read_text() != zero_content
                or digest.read_text() != expected):
            raise SystemExit("Source/model mismatch; review changes and rerun generate.py")
        print("C source and extracted model match")
    else:
        generated.write_text(content)
        machine_generated.write_text(machine_content)
        products_generated.write_text(products_content)
        zero_generated.write_text(zero_content)
        digest.write_text(expected)


if __name__ == "__main__":
    main()
