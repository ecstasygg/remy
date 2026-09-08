theory Examples
  imports Frontend
begin

lemma overflow: "operate Add (-1) 1 = 0"
  by eval

lemma multiply_overflow: "operate Mul (2 ^ 63) 2 = 0"
  by eval

lemma shift_mask: "operate Shl 7 64 = 7"
  by eval

lemma shift_wrap: "operate Shl 7 65 = 14"
  by eval

lemma logical_shift: "operate Shr (-1) 63 = 1"
  by eval

lemma unsigned_comparison: "operate Less (-1) 1 = 0"
  by eval

lemma unsigned_high_bit: "operate Less 1 (2 ^ 63) = 1"
  by eval

lemma constant_fold:
  "optimise (Binary Add (Literal (-1)) (Literal 1)) = Literal 0"
  by eval

lemma neutral_arithmetic:
  "optimise (Binary Mul (Binary Add (Input X) (Literal 0)) (Literal 1)) = Input X"
  by eval

lemma neutral_bits:
  "optimise (Binary And (Binary Xor (Input Y) (Literal 0)) (Literal (-1))) = Input Y"
  by eval

lemma absorbing_arithmetic:
  "optimise (Binary Mul (Input X) (Literal 0)) = Literal 0"
  by eval

lemma absorbing_bits:
  "optimise (Binary Or (Binary And (Input Y) (Literal 0)) (Literal (-1))) = Literal (-1)"
  by eval

lemma dead_branch:
  "optimise (Cond (Literal 0) (Input X) (Input Y)) = Input Y"
  by eval

lemma literal_code:
  "executable (Literal 42) = [72,184,42,0,0,0,0,0,0,0,80,88,195]"
  by eval

lemma opcode_roundtrip:
  "decode [72,145,72,211,232,195] = Some (Arithmetic Shr,[195])"
  by eval

lemma truncated_literal: "decode [72,184,0,0] = None"
  by eval

lemma unaligned_slot: "decode [72,139,132,36,1,0,0,0] = None"
  by eval

lemma negative_slot: "decode [72,139,132,36,0,0,0,128] = None"
  by eval

lemma lexical_shadow:
  "reference ''(let x 7 (let x (+ x 2) (* x x)))'' ''1'' ''2'' ''3'' = (True,''81'' @ newline)"
  by eval

lemma nested_temporaries:
  "reference ''(+ 10 (let a 3 (+ a (let b 4 (* a b)))))'' ''0'' ''0'' ''0'' = (True,''25'' @ newline)"
  by eval

lemma unbound_rejected: "prepare ''(let a 3 b)'' = None"
  by eval

lemma trailing_rejected: "prepare ''(+ x y) 1'' = None"
  by eval

lemma literal_overflow_rejected: "prepare ''18446744073709551616'' = None"
  by eval

lemma incomplete_rejected: "prepare ''(if x y)'' = None"
  by eval

end
