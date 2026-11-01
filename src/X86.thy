theory X86
  imports Bounds
begin

datatype micro = Imm64 pixel | Imm32 pixel | Copy register register | Save register | Restore register
  | Load nat | Alu operator | Exchange | Compare | Below | Extend | Test register | Select

record processor =
  state64 :: machine
  pointer64 :: pixel
  zero64 :: "bool option"
  carry64 :: "bool option"

definition put64 :: "register \<Rightarrow> pixel \<Rightarrow> processor \<Rightarrow> processor" where
  "put64 r v c = c\<lparr>state64 := (state64 c)\<lparr>registers := (registers (state64 c))(r := v)\<rparr>\<rparr>"

fun microstep :: "micro \<Rightarrow> processor \<Rightarrow> processor option" where
  "microstep (Imm64 v) c = Some (put64 Rax v c)"
| "microstep (Imm32 v) c = Some (put64 Rax v c)"
| "microstep (Copy dst src) c = Some (put64 dst (registers (state64 c) src) c)"
| "microstep (Save r) c = Some (c\<lparr>state64 := (state64 c)\<lparr>stack := registers (state64 c) r # stack (state64 c)\<rparr>,
    pointer64 := pointer64 c - 8\<rparr>)"
| "microstep (Restore r) c = (case stack (state64 c) of [] \<Rightarrow> None | v # vs \<Rightarrow>
    Some ((put64 r v c)\<lparr>state64 := (state64 (put64 r v c))\<lparr>stack := vs\<rparr>, pointer64 := pointer64 c + 8\<rparr>))"
| "microstep (Load i) c = (if i < length (stack (state64 c))
    then Some (put64 Rax (stack (state64 c) ! i) c) else None)"
| "microstep (Alu op) c = (if op = Less then None else
    Some ((put64 Rax (operate op (registers (state64 c) Rax) (registers (state64 c) Rcx)) c)
      \<lparr>zero64 := None, carry64 := None\<rparr>))"
| "microstep Exchange c = Some (put64 Rcx (registers (state64 c) Rax)
    (put64 Rax (registers (state64 c) Rcx) c))"
| "microstep Compare c = Some (c\<lparr>zero64 := Some (registers (state64 c) Rax = registers (state64 c) Rcx),
    carry64 := Some (registers (state64 c) Rax < registers (state64 c) Rcx)\<rparr>)"
| "microstep Below c = (case carry64 c of None \<Rightarrow> None | Some flag \<Rightarrow>
    Some (put64 Rax ((registers (state64 c) Rax AND NOT 255) OR (if flag then 1 else 0)) c))"
| "microstep Extend c = Some (put64 Rax (registers (state64 c) Rax AND 255) c)"
| "microstep (Test r) c = Some (c\<lparr>zero64 := Some (registers (state64 c) r = 0), carry64 := Some False\<rparr>)"
| "microstep Select c = (case zero64 c of None \<Rightarrow> None | Some flag \<Rightarrow>
    Some (if flag then c else put64 Rax (registers (state64 c) Rcx) c))"

fun microrun :: "micro list \<Rightarrow> processor \<Rightarrow> processor option" where
  "microrun [] c = Some c"
| "microrun (i # code) c = Option.bind (microstep i c) (microrun code)"

lemma microrun_append:
  "microrun (a @ b) c = Option.bind (microrun a c) (microrun b)"
  by (induction a arbitrary: c) (auto split: option.splits bind_splits)

fun microbytes :: "micro \<Rightarrow> nat list" where
  "microbytes (Imm64 v) = [72,184] @ octets 8 (unat v)"
| "microbytes (Imm32 v) = [72,199,192] @ octets 4 (unat v)"
| "microbytes (Copy dst src) = movecode dst src"
| "microbytes (Save r) = pushcode r"
| "microbytes (Restore r) = popcode r"
| "microbytes (Load i) = (if i < 16 then [72,139,68,36,8*i]
    else [72,139,132,36] @ octets 4 (8*i))"
| "microbytes (Alu Add) = [72,1,200]"
| "microbytes (Alu Sub) = [72,41,200]"
| "microbytes (Alu Mul) = [72,15,175,193]"
| "microbytes (Alu And) = [72,33,200]"
| "microbytes (Alu Or) = [72,9,200]"
| "microbytes (Alu Xor) = [72,49,200]"
| "microbytes (Alu Shl) = [72,211,224]"
| "microbytes (Alu Shr) = [72,211,232]"
| "microbytes (Alu Less) = []"
| "microbytes Exchange = [72,145]"
| "microbytes Compare = [72,57,200]"
| "microbytes Below = [15,146,192]"
| "microbytes Extend = [72,15,182,192]"
| "microbytes (Test r) = [72,133,192 + 9 * regno r]"
| "microbytes Select = [72,15,69,193]"

fun microvalid :: "micro \<Rightarrow> bool" where
  "microvalid (Imm32 v) = (extend32 (unat v) = v)"
| "microvalid (Load i) = (i < 2 ^ 28)"
| "microvalid (Alu Less) = False"
| "microvalid (Test r) = (r = Rax \<or> r = Rbx)"
| "microvalid _ = True"

fun expand :: "opcode \<Rightarrow> micro list" where
  "expand (Immediate v) = [if extend32 (unat v) = v then Imm32 v else Imm64 v]"
| "expand (Push r) = [Save r]"
| "expand (Pop r) = [Restore r]"
| "expand (Move dst src) = [Copy dst src]"
| "expand (Peek i) = [Load i]"
| "expand (Arithmetic op) = (if op = Less then [Exchange,Compare,Below,Extend]
    else if exchanges op then [Exchange,Alu op] else [Alu op])"
| "expand Conditional = [Test Rbx,Select]"

lemma byte_register:
  "((v AND NOT 255) OR (if flag then 1 else 0)) AND 255 = (if flag then 1 else 0 :: pixel)"
  by (cases flag) (simp_all add: word_ao_dist word_bw_assocs)

theorem expand_state:
  "map_option state64 (microrun (expand op) c) = transition op (state64 c)"
proof (cases op)
  case (Arithmetic f)
  then show ?thesis
    by (cases f)
      (auto simp: put64_def byte_register word_ao_dist2 word_ao_dist word_bw_assocs ac_simps split: option.splits)
next
  case (Pop r)
  then show ?thesis by (cases "stack (state64 c)") (auto simp: put64_def)
qed (auto simp: put64_def split: if_splits option.splits)

theorem expand_bytes:
  "concat (map microbytes (expand op)) = encode op"
proof (cases op)
  case (Arithmetic f)
  then show ?thesis by (cases f) auto
qed auto

lemma expand_valid:
  "encodable op \<Longrightarrow> list_all microvalid (expand op)"
proof (cases op)
  case (Arithmetic f)
  then show ?thesis by (cases f) auto
qed auto

theorem expand_run:
  "map_option state64 (microrun (concat (map expand code)) c) = run code (state64 c)"
proof (induction code arbitrary: c)
  case Nil
  then show ?case by simp
next
  case (Cons op code)
  then show ?case using expand_state[of op c]
    by (auto simp: microrun_append split: option.splits bind_splits)
qed

definition top64 :: "processor \<Rightarrow> pixel" where
  "top64 c = pointer64 c + 8 * of_nat (length (stack (state64 c)))"

lemma microstep_top:
  "microstep i c = Some d \<Longrightarrow> top64 d = top64 c"
  by (cases i)
    (auto simp: top64_def put64_def algebra_simps split: list.splits if_splits option.splits)

definition fixed64 :: "micro list" where
  "fixed64 = map Save [Rax,Rcx,Rbx,Rdx,R8,R9] @ map Restore [Rax,Rcx,Rbx,Rdx,R8,R9] @
    concat (map (\<lambda>dst. map (Copy dst) [Rax,Rcx,Rbx,Rdx,R8,R9]) [Rax,Rcx,Rbx,Rdx,R8,R9]) @
    map Alu [Add,Sub,Mul,And,Or,Xor,Shl,Shr] @ [Exchange,Compare,Below,Extend,Test Rax,Test Rbx,Select]"

definition decode64 :: "nat list \<Rightarrow> (micro \<times> nat list) option" where
  "decode64 bs = (if take 2 bs = [72,184] then
    if 10 \<le> length bs then Some (Imm64 (word_of_nat (integer (take 8 (drop 2 bs)))),drop 10 bs) else None
    else if take 3 bs = [72,199,192] then
      if 7 \<le> length bs then Some (Imm32 (extend32 (integer (take 4 (drop 3 bs)))),drop 7 bs) else None
    else if take 4 bs = [72,139,68,36] then
      let n = integer (take 1 (drop 4 bs)) in
      if 5 \<le> length bs \<and> n < 128 \<and> n mod 8 = 0 then Some (Load (n div 8),drop 5 bs) else None
    else if take 4 bs = [72,139,132,36] then
      let n = integer (take 4 (drop 4 bs)) in
      if 8 \<le> length bs \<and> n mod 8 = 0 \<and> n div 8 < 2 ^ 28
      then Some (Load (n div 8),drop 8 bs) else None
    else map_option (\<lambda>i. (i,drop (length (microbytes i)) bs))
      (List.find (\<lambda>i. take (length (microbytes i)) bs = microbytes i) fixed64))"

theorem decode64_encode:
  assumes "microvalid i"
  shows "decode64 (microbytes i @ tail) = Some (i,tail)"
proof (cases i)
  case (Imm64 v)
  then show ?thesis by (simp add: decode64_def)
next
  case (Imm32 v)
  then show ?thesis using assms by (simp add: decode64_def)
next
  case (Copy dst src)
  then show ?thesis by (cases dst; cases src) (simp_all add: decode64_def fixed64_def movecode_def)
next
  case (Save r)
  then show ?thesis by (cases r) (simp_all add: decode64_def fixed64_def)
next
  case (Restore r)
  then show ?thesis by (cases r) (simp_all add: decode64_def fixed64_def)
next
  case (Load n)
  then show ?thesis using assms peek_bound[of n]
    by (auto simp: decode64_def integer_octets Let_def)
next
  case (Alu op)
  then show ?thesis using assms by (cases op) (simp_all add: decode64_def fixed64_def movecode_def)
next
  case (Test r)
  then show ?thesis using assms by (cases r) (simp_all add: decode64_def fixed64_def movecode_def)
qed (simp_all add: decode64_def fixed64_def movecode_def)

inductive executes64 :: "nat list \<Rightarrow> processor \<Rightarrow> processor \<Rightarrow> bool" where
  empty: "executes64 [] c c"
| advance: "microvalid i \<Longrightarrow> microstep i c = Some d \<Longrightarrow> executes64 tail d e \<Longrightarrow>
    executes64 (microbytes i @ tail) c e"
| jump: "n < 2 ^ 31 \<Longrightarrow> n \<le> length tail \<Longrightarrow> executes64 (drop n tail) c d \<Longrightarrow>
    executes64 ([233] @ octets 4 n @ tail) c d"
| zero: "n < 2 ^ 31 \<Longrightarrow> n \<le> length tail \<Longrightarrow> zero64 c = Some True \<Longrightarrow>
    executes64 (drop n tail) c d \<Longrightarrow> executes64 ([15,132] @ octets 4 n @ tail) c d"
| nonzero: "n < 2 ^ 31 \<Longrightarrow> zero64 c = Some False \<Longrightarrow> executes64 tail c d \<Longrightarrow>
    executes64 ([15,132] @ octets 4 n @ tail) c d"

lemma executes64_append:
  "executes64 a c d \<Longrightarrow> executes64 b d e \<Longrightarrow> executes64 (a @ b) c e"
  by (induction a c d rule: executes64.induct)
    (auto simp: drop_append intro: executes64.intros[simplified])

lemma executes64_micro:
  "list_all microvalid code \<Longrightarrow> microrun code c = Some d \<Longrightarrow>
    executes64 (concat (map microbytes code)) c d"
  by (induction code arbitrary: c) (auto split: option.splits bind_splits intro: executes64.intros)

lemma executes64_top:
  "executes64 code c d \<Longrightarrow> top64 d = top64 c"
  by (induction rule: executes64.induct) (auto dest: microstep_top)

theorem executes64_native:
  "list_all encodable code \<Longrightarrow> run code (state64 c) = Some s \<Longrightarrow>
    \<exists>d. executes64 (concat (map encode code)) c d \<and> state64 d = s"
proof -
  assume valid: "list_all encodable code" and ran: "run code (state64 c) = Some s"
  obtain d where d: "microrun (concat (map expand code)) c = Some d" "state64 d = s"
    using expand_run[of code c] ran by (auto split: option.splits)
  have safe: "list_all microvalid (concat (map expand code))"
    using valid expand_valid by (auto simp: list_all_iff)
  have bytes: "concat (map microbytes (concat (map expand code))) = concat (map encode code)"
    using expand_bytes by (induction code) auto
  show ?thesis using executes64_micro[OF safe d(1)] d(2) bytes by auto
qed


theorem executes64_flow:
  assumes "flowvalid code" "flowrun code (state64 c) = Some s"
  shows "\<exists>d. executes64 (flowbytes code) c d \<and> state64 d = s"
  using assms
proof (induction code arbitrary: c s)
  case (Basic code)
  then show ?case using executes64_native by fastforce
next
  case (Sequence a b)
  obtain m where a: "flowrun a (state64 c) = Some m" and b: "flowrun b m = Some s"
    using Sequence.prems by (auto split: bind_splits)
  obtain d where d: "executes64 (flowbytes a) c d" "state64 d = m"
    using Sequence.IH(1) Sequence.prems a by auto
  obtain e where e: "executes64 (flowbytes b) d e" "state64 e = s"
    using Sequence.IH(2) Sequence.prems b d by auto
  show ?case using executes64_append[OF d(1) e(1)] e(2) by auto
next
  case (Choice a b)
  let ?c = "c\<lparr>zero64 := Some (registers (state64 c) Rax = 0), carry64 := Some False\<rparr>"
  have test: "microstep (Test Rax) c = Some ?c" by simp
  have limits: "length (flowbytes a) + 5 < 2 ^ 31" "length (flowbytes b) < 2 ^ 31"
    using Choice.prems by auto
  show ?case
  proof (cases "registers (state64 c) Rax = 0")
    case True
    obtain d where d: "executes64 (flowbytes b) ?c d" "state64 d = s"
      using Choice.IH(2)[of ?c s] Choice.prems True by auto
    have z: "executes64 ([15,132] @ octets 4 (length (flowbytes a) + 5) @
        (flowbytes a @ [233] @ octets 4 (length (flowbytes b)) @ flowbytes b)) ?c d"
      using d(1) limits True by (intro executes64.zero) auto
    have "executes64 (microbytes (Test Rax) @ ([15,132] @ octets 4 (length (flowbytes a) + 5) @
        (flowbytes a @ [233] @ octets 4 (length (flowbytes b)) @ flowbytes b))) c d"
      using test z by (intro executes64.advance) auto
    then show ?thesis using d(2) by auto
  next
    case False
    obtain d where d: "executes64 (flowbytes a) ?c d" "state64 d = s"
      using Choice.IH(1)[of ?c s] Choice.prems False by auto
    have skip: "executes64 ([233] @ octets 4 (length (flowbytes b)) @ flowbytes b) d d"
      using limits(2) by (intro executes64.jump) (auto intro: executes64.empty)
    have z: "executes64 ([15,132] @ octets 4 (length (flowbytes a) + 5) @
        (flowbytes a @ [233] @ octets 4 (length (flowbytes b)) @ flowbytes b)) ?c d"
      using executes64_append[OF d(1) skip] limits False
      by (intro executes64.nonzero) auto
    have "executes64 (microbytes (Test Rax) @ ([15,132] @ octets 4 (length (flowbytes a) + 5) @
        (flowbytes a @ [233] @ octets 4 (length (flowbytes b)) @ flowbytes b))) c d"
      using test z by (intro executes64.advance) auto
    then show ?thesis using d(2) by auto
  qed
qed

theorem compiled_execution:
  assumes "scoped 0 e" "flowvalid (branching e)"
  shows "\<exists>d. executes64 (flowbytes (branching e)) c d \<and>
    registers (state64 d) Rax = evaluate e [] (inputs (state64 c)) \<and>
    stack (state64 d) = stack (state64 c) \<and> inputs (state64 d) = inputs (state64 c) \<and>
    pointer64 d = pointer64 c"
proof -
  obtain s where s: "flowrun (branching e) (state64 c) = Some s"
    "registers s Rax = evaluate e [] (inputs (state64 c))"
    "stack s = stack (state64 c)" "inputs s = inputs (state64 c)"
    using branching_return[OF assms(1), of "state64 c"] by blast
  obtain d where d: "executes64 (flowbytes (branching e)) c d" "state64 d = s"
    using executes64_flow[OF assms(2) s(1)] by blast
  have "pointer64 d = pointer64 c"
    using executes64_top[OF d(1)] d(2) s(3) by (simp add: top64_def)
  then show ?thesis using d s by blast
qed

definition ret64 :: "processor \<Rightarrow> (pixel \<times> processor) option" where
  "ret64 c = (case stack (state64 c) of [] \<Rightarrow> None | address # rest \<Rightarrow>
    Some (address,c\<lparr>state64 := (state64 c)\<lparr>stack := rest\<rparr>, pointer64 := pointer64 c + 8\<rparr>))"

definition returns64 :: "nat list \<Rightarrow> processor \<Rightarrow> pixel \<Rightarrow> processor \<Rightarrow> bool" where
  "returns64 bytes c address d \<longleftrightarrow> (\<exists>body q. bytes = body @ [195] \<and>
    executes64 body c q \<and> ret64 q = Some (address,d))"

theorem compiled_return:
  assumes "scoped 0 e" "flowvalid (branching e)" "stack (state64 c) = address # rest"
  shows "\<exists>d. returns64 (flowbytes (branching e) @ [195]) c address d \<and>
    registers (state64 d) Rax = evaluate e [] (inputs (state64 c)) \<and>
    stack (state64 d) = rest \<and> inputs (state64 d) = inputs (state64 c) \<and>
    pointer64 d = pointer64 c + 8"
proof -
  obtain q where q: "executes64 (flowbytes (branching e)) c q"
    "registers (state64 q) Rax = evaluate e [] (inputs (state64 c))"
    "stack (state64 q) = stack (state64 c)" "inputs (state64 q) = inputs (state64 c)"
    "pointer64 q = pointer64 c"
    using compiled_execution[OF assms(1,2), of c] by blast
  let ?d = "q\<lparr>state64 := (state64 q)\<lparr>stack := rest\<rparr>, pointer64 := pointer64 q + 8\<rparr>"
  have ret: "ret64 q = Some (address,?d)"
    using q(3) assms(3) by (simp add: ret64_def)
  have "returns64 (flowbytes (branching e) @ [195]) c address ?d"
    using q(1) ret by (auto simp: returns64_def)
  then show ?thesis using q by auto
qed

function simulate64 :: "nat \<Rightarrow> nat list \<Rightarrow> processor \<Rightarrow> processor option" where
  "simulate64 0 bytes c = None"
| "simulate64 (Suc fuel) bytes c = (if bytes = [] then None else
    if bytes = [195] then map_option snd (ret64 c) else
    if take 1 bytes = [233] then let n = integer (take 4 (drop 1 bytes)) in
      if 5 \<le> length bytes \<and> n < 2 ^ 31 \<and> n \<le> length bytes - 5
      then simulate64 fuel (drop (5+n) bytes) c else None
    else if take 2 bytes = [15,132] then let n = integer (take 4 (drop 2 bytes)) in
      if 6 \<le> length bytes \<and> n < 2 ^ 31 \<and> n \<le> length bytes - 6 then
        (case zero64 c of None \<Rightarrow> None | Some flag \<Rightarrow>
          simulate64 fuel (drop (6 + (if flag then n else 0)) bytes) c)
      else None
    else Option.bind (decode64 bytes) (\<lambda>(i,rest).
      if microvalid i then Option.bind (microstep i c) (simulate64 fuel rest) else None))"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(fuel,bytes,c). fuel)") auto

declare simulate64.simps [simp del]

end
