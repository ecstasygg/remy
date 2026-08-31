theory Encoding
  imports Native
begin

fun octets :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "octets 0 n = []"
| "octets (Suc k) n = n mod 256 # octets k (n div 256)"

fun integer :: "nat list \<Rightarrow> nat" where
  "integer [] = 0"
| "integer (b # bs) = b + 256 * integer bs"

lemma octets_length [simp]: "length (octets k n) = k"
  by (induction k arbitrary: n) auto

lemma octets_bytes: "set (octets k n) \<subseteq> {..<256}"
  by (induction k arbitrary: n) auto

lemma integer_octets: "integer (octets k n) = n mod 256 ^ k"
  by (induction k arbitrary: n) (simp_all add: power_Suc mod_mult2_eq add.commute)

lemma literal_bound: "unat (v :: pixel) < 256 ^ 8"
  using unsigned_less[of v, where ?'a=nat] by simp

lemma integer_literal [simp]: "word_of_nat (integer (octets 8 (unat v))) = (v :: pixel)"
  using literal_bound[of v] by (simp add: integer_octets)

fun pushcode :: "register \<Rightarrow> nat list" where
  "pushcode Rax = [80]"
| "pushcode Rcx = [81]"
| "pushcode Rbx = [83]"
| "pushcode Rdx = [82]"
| "pushcode R8 = [65,80]"
| "pushcode R9 = [65,81]"

fun popcode :: "register \<Rightarrow> nat list" where
  "popcode Rax = [88]"
| "popcode Rcx = [89]"
| "popcode Rbx = [91]"
| "popcode Rdx = [90]"
| "popcode R8 = [65,88]"
| "popcode R9 = [65,89]"

fun arithmetic :: "operator \<Rightarrow> nat list" where
  "arithmetic Add = [72,1,200]"
| "arithmetic Sub = [72,145,72,41,200]"
| "arithmetic Mul = [72,15,175,193]"
| "arithmetic And = [72,33,200]"
| "arithmetic Or = [72,9,200]"
| "arithmetic Xor = [72,49,200]"
| "arithmetic Shl = [72,145,72,211,224]"
| "arithmetic Shr = [72,145,72,211,232]"
| "arithmetic Less = [72,145,72,57,200,15,146,192,72,15,182,192]"

fun encode :: "opcode \<Rightarrow> nat list" where
  "encode (Immediate v) = [72,184] @ octets 8 (unat v)"
| "encode (Push r) = pushcode r"
| "encode (Pop r) = popcode r"
| "encode (Peek i) = [72,139,132,36] @ octets 4 (8 * i)"
| "encode (Arithmetic op) = arithmetic op"
| "encode Conditional = [72,133,219,72,15,69,193]"

fun encodable :: "opcode \<Rightarrow> bool" where
  "encodable (Peek i) = (i < 2 ^ 28)"
| "encodable _ = True"

definition fixed :: "opcode list" where
  "fixed = map Push [Rax,Rcx,Rbx,Rdx,R8,R9] @ map Pop [Rax,Rcx,Rbx,Rdx,R8,R9] @
    map Arithmetic [Add,Sub,Mul,And,Or,Xor,Shl,Shr,Less] @ [Conditional]"

definition decode :: "nat list \<Rightarrow> (opcode \<times> nat list) option" where
  "decode bs = (if take 2 bs = [72,184] then
    if 10 \<le> length bs \<and> list_all (\<lambda>b. b < 256) (take 8 (drop 2 bs)) then
      Some (Immediate (word_of_nat (integer (take 8 (drop 2 bs)))), drop 10 bs) else None
    else if take 4 bs = [72,139,132,36] then
      let n = integer (take 4 (drop 4 bs)) in
      if 8 \<le> length bs \<and> list_all (\<lambda>b. b < 256) (take 4 (drop 4 bs)) \<and>
        n mod 8 = 0 \<and> n div 8 < 2 ^ 28 then Some (Peek (n div 8), drop 8 bs) else None
    else map_option (\<lambda>op. (op, drop (length (encode op)) bs))
      (List.find (\<lambda>op. take (length (encode op)) bs = encode op) fixed))"

lemma octets_all [simp]: "list_all (\<lambda>b. b < 256) (octets k n)"
  using octets_bytes[of k n] by (auto simp: list_all_iff)

lemma peek_bound:
  "(i :: nat) < 2 ^ 28 \<Longrightarrow> 8 * i < 256 ^ 4"
  by (simp; linarith)

theorem decode_encode:
  assumes valid: "encodable op"
  shows "decode (encode op @ tail) = Some (op, tail)"
proof (cases op)
  case (Immediate v)
  then show ?thesis
    by (simp add: decode_def take_add integer_literal)
next
  case (Push r)
  then show ?thesis by (cases r) (simp_all add: decode_def fixed_def)
next
  case (Pop r)
  then show ?thesis by (cases r) (simp_all add: decode_def fixed_def)
next
  case (Peek i)
  have small: "i < 2 ^ 28" using valid Peek by simp
  have bound: "8 * i < 4294967296" using peek_bound[OF small] by simp
  show ?thesis using Peek small bound
    by (simp add: decode_def integer_octets Let_def)
next
  case (Arithmetic op)
  then show ?thesis by (cases op) (simp_all add: decode_def fixed_def)
next
  case Conditional
  then show ?thesis by (simp add: decode_def fixed_def)
qed

theorem encode_bytes: "set (encode op) \<subseteq> {..<256}"
proof (cases op)
  case (Immediate v)
  then show ?thesis using octets_bytes by auto
next
  case (Push r)
  then show ?thesis by (cases r) auto
next
  case (Pop r)
  then show ?thesis by (cases r) auto
next
  case (Peek i)
  then show ?thesis using octets_bytes by auto
next
  case (Arithmetic op)
  then show ?thesis by (cases op) auto
next
  case Conditional
  then show ?thesis by simp
qed

theorem encode_injective:
  "encodable a \<Longrightarrow> encodable b \<Longrightarrow> encode a = encode b \<longleftrightarrow> a = b"
  using decode_encode[of a "[]"] decode_encode[of b "[]"]
  by (metis append_Nil option.inject prod.inject)

fun recover :: "nat \<Rightarrow> nat list \<Rightarrow> (opcode list \<times> nat list) option" where
  "recover 0 bs = Some ([],bs)"
| "recover (Suc n) bs = Option.bind (decode bs) (\<lambda>(op,tail).
    map_option (\<lambda>(ops,rest). (op # ops,rest)) (recover n tail))"

theorem recover_encode:
  "list_all encodable ops \<Longrightarrow>
    recover (length ops) (concat (map encode ops) @ tail) = Some (ops,tail)"
  by (induction ops) (simp_all add: decode_encode)

definition executable :: "expression \<Rightarrow> nat list" where
  "executable e = concat (map encode (native (compile (optimise e) []))) @ [88,195]"

theorem executable_bytes: "set (executable e) \<subseteq> {..<256}"
  unfolding executable_def using encode_bytes by auto

end
