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

fun regno :: "register \<Rightarrow> nat" where
  "regno Rax = 0" | "regno Rcx = 1" | "regno Rdx = 2"
| "regno Rbx = 3" | "regno R8 = 8" | "regno R9 = 9"

definition movecode :: "register \<Rightarrow> register \<Rightarrow> nat list" where
  "movecode dst src = [72 + (if regno src \<ge> 8 then 4 else 0) + (if regno dst \<ge> 8 then 1 else 0),
    137, 192 + 8 * (regno src mod 8) + regno dst mod 8]"

definition extend32 :: "nat \<Rightarrow> pixel" where
  "extend32 n = word_of_int (signed_take_bit 31 (int n))"

lemma extend32_octets [simp]: "extend32 (integer (octets 4 n)) = extend32 n"
proof -
  have "signed_take_bit 31 (int (n mod 256 ^ 4)) = signed_take_bit 31 (int n)"
    by (simp add: signed_take_bit_eq_iff_take_bit_eq take_bit_eq_mod of_nat_mod)
  then show ?thesis by (simp add: extend32_def integer_octets)
qed

fun encode :: "opcode \<Rightarrow> nat list" where
  "encode (Immediate v) = (if extend32 (unat v) = v then [72,199,192] @ octets 4 (unat v)
    else [72,184] @ octets 8 (unat v))"
| "encode (Push r) = pushcode r"
| "encode (Pop r) = popcode r"
| "encode (Peek i) = (if i < 16 then [72,139,68,36,8 * i]
    else [72,139,132,36] @ octets 4 (8 * i))"
| "encode (Arithmetic op) = arithmetic op"
| "encode Conditional = [72,133,219,72,15,69,193]"
| "encode (Move dst src) = movecode dst src"

fun encodable :: "opcode \<Rightarrow> bool" where
  "encodable (Peek i) = (i < 2 ^ 28)"
| "encodable _ = True"

definition fixed :: "opcode list" where
  "fixed = map Push [Rax,Rcx,Rbx,Rdx,R8,R9] @ map Pop [Rax,Rcx,Rbx,Rdx,R8,R9] @
    map Arithmetic [Add,Sub,Mul,And,Or,Xor,Shl,Shr,Less] @ [Conditional] @
    concat (map (\<lambda>dst. map (Move dst) [Rax,Rcx,Rbx,Rdx,R8,R9]) [Rax,Rcx,Rbx,Rdx,R8,R9])"

definition decode :: "nat list \<Rightarrow> (opcode \<times> nat list) option" where
  "decode bs = (if take 2 bs = [72,184] then
    if 10 \<le> length bs \<and> list_all (\<lambda>b. b < 256) (take 8 (drop 2 bs)) then
      Some (Immediate (word_of_nat (integer (take 8 (drop 2 bs)))), drop 10 bs) else None
    else if take 3 bs = [72,199,192] then
      if 7 \<le> length bs \<and> list_all (\<lambda>b. b < 256) (take 4 (drop 3 bs)) then
        Some (Immediate (extend32 (integer (take 4 (drop 3 bs)))), drop 7 bs) else None
    else if take 4 bs = [72,139,68,36] then
      let n = integer (take 1 (drop 4 bs)) in
      if 5 \<le> length bs \<and> n < 128 \<and> n mod 8 = 0
      then Some (Peek (n div 8), drop 5 bs) else None
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
    by (auto simp: decode_def take_add integer_literal split: if_splits)
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
    by (auto simp: decode_def integer_octets Let_def split: if_splits)
next
  case (Arithmetic op)
  then show ?thesis by (cases op) (simp_all add: decode_def fixed_def)
next
  case Conditional
  then show ?thesis by (simp add: decode_def fixed_def)
next
  case (Move dst src)
  then show ?thesis by (cases dst; cases src) (simp_all add: decode_def fixed_def movecode_def)

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
next
  case (Move dst src)
  then show ?thesis by (cases dst; cases src) (simp_all add: movecode_def)

qed

theorem encode_injective:
  "encodable a \<Longrightarrow> encodable b \<Longrightarrow> encode a = encode b \<longleftrightarrow> a = b"
  using decode_encode[of a "[]"] decode_encode[of b "[]"]
  by (metis append_Nil option.inject prod.inject)

lemma push_nonempty [simp]: "pushcode r \<noteq> []"
  by (cases r) auto

lemma pop_nonempty [simp]: "popcode r \<noteq> []"
  by (cases r) auto

lemma arithmetic_nonempty [simp]: "arithmetic op \<noteq> []"
  by (cases op) auto

lemma encode_nonempty [simp]: "encode op \<noteq> []"
  by (cases op) (auto simp: movecode_def)

lemma fixed_decode:
  "List.find (\<lambda>op. take (length (encode op)) bs = encode op) fixed = Some op \<Longrightarrow>
    0 < length (encode op) \<and> length (encode op) \<le> length bs \<and>
    list_all (\<lambda>b. b < 256) (take (length (encode op)) bs)"
  using encode_bytes[of op]
  by (auto simp: find_Some_iff list_all_iff dest: arg_cong[where f=length])

theorem decode_progress:
  "decode bs = Some (op,rest) \<Longrightarrow> length rest < length bs"
  unfolding decode_def
  apply (auto simp: Let_def dest: fixed_decode split: if_splits option.splits)
  apply (drule fixed_decode)
  apply auto
  by (cases bs) auto

theorem decode_consumed:
  "decode bs = Some (op,rest) \<Longrightarrow> list_all (\<lambda>b. b < 256) bs \<Longrightarrow>
    \<exists>prefix. bs = prefix @ rest \<and> prefix \<noteq> [] \<and> list_all (\<lambda>b. b < 256) prefix"
proof -
  assume decoded: "decode bs = Some (op,rest)"
    and input: "list_all (\<lambda>b. b < 256) bs"
  have drop: "rest = drop (length bs - length rest) bs"
    using decoded unfolding decode_def
    apply (auto simp: Let_def split: if_splits option.splits)
    apply (drule fixed_decode)
    by auto
  have bytes: "list_all (\<lambda>b. b < 256) (take (length bs - length rest) bs)"
    using input by (auto simp: list_all_iff dest: in_set_takeD)
  have decomposition: "bs = take (length bs - length rest) bs @ rest"
    using drop append_take_drop_id[of "length bs - length rest" bs] by metis
  show ?thesis
    using decomposition bytes decode_progress[OF decoded]
    by (intro exI[where x="take (length bs - length rest) bs"]) auto
qed

fun recover :: "nat \<Rightarrow> nat list \<Rightarrow> (opcode list \<times> nat list) option" where
  "recover 0 bs = Some ([],bs)"
| "recover (Suc n) bs = Option.bind (decode bs) (\<lambda>(op,tail).
    map_option (\<lambda>(ops,rest). (op # ops,rest)) (recover n tail))"

theorem recover_encode:
  "list_all encodable ops \<Longrightarrow>
    recover (length ops) (concat (map encode ops) @ tail) = Some (ops,tail)"
  by (induction ops) (simp_all add: decode_encode)

function blocks :: "nat list \<Rightarrow> (nat list \<times> opcode) list option" where
  "blocks bs = (if bs = [195] then Some [] else
    Option.bind (decode bs) (\<lambda>(op,rest).
      map_option (\<lambda>code. (take (length bs - length rest) bs,op) # code) (blocks rest)))"
  by pat_completeness auto
termination
  by (relation "measure length") (auto dest: decode_progress)

declare blocks.simps [simp del]

definition executable :: "expression \<Rightarrow> nat list" where
  "executable e = concat (map encode (program e)) @ [195]"

theorem executable_bytes: "set (executable e) \<subseteq> {..<256}"
  unfolding executable_def using encode_bytes by auto

end
