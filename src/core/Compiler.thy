theory Compiler
  imports Model
begin

datatype instruction = Constant pixel | Fetch input | Pick nat | Calculate operator | Choose | Slide

fun step :: "(input \<Rightarrow> pixel) \<Rightarrow> instruction \<Rightarrow> pixel list \<Rightarrow> pixel list option" where
  "step inputs (Constant v) s = Some (v # s)"
| "step inputs (Fetch i) s = Some (inputs i # s)"
| "step inputs (Pick i) s = (if i < length s then Some (s ! i # s) else None)"
| "step inputs (Calculate op) (b # a # s) = Some (operate op a b # s)"
| "step inputs Choose (b # a # c # s) = Some ((if c = 0 then b else a) # s)"
| "step inputs Slide (b # a # s) = Some (b # s)"
| "step inputs _ _ = None"

fun execute :: "(input \<Rightarrow> pixel) \<Rightarrow> instruction list \<Rightarrow> pixel list \<Rightarrow> pixel list option" where
  "execute inputs [] s = Some s"
| "execute inputs (i # code) s = (case step inputs i s of None \<Rightarrow> None | Some t \<Rightarrow> execute inputs code t)"

lemma execute_append:
  "execute inputs (a @ b) s = Option.bind (execute inputs a s) (execute inputs b)"
  by (induction a arbitrary: s) (auto split: option.splits bind_splits)

fun compile :: "expression \<Rightarrow> nat list \<Rightarrow> instruction list" where
  "compile (Literal v) slots = [Constant v]"
| "compile (Input i) slots = [Fetch i]"
| "compile (Variable i) slots = [Pick (slots ! i)]"
| "compile (Binary op a b) slots = compile a slots @ compile b (map Suc slots) @ [Calculate op]"
| "compile (Cond c a b) slots = compile c slots @ compile a (map Suc slots) @
    compile b (map (\<lambda>i. Suc (Suc i)) slots) @ [Choose]"
| "compile (Let a b) slots = compile a slots @ compile b (0 # map Suc slots) @ [Slide]"

definition represents :: "nat list \<Rightarrow> pixel list \<Rightarrow> pixel list \<Rightarrow> bool" where
  "represents slots s env \<longleftrightarrow> length slots = length env \<and>
    (\<forall>i < length env. slots ! i < length s \<and> s ! (slots ! i) = env ! i)"

lemma represents_push:
  "represents slots s env \<Longrightarrow> represents (map Suc slots) (v # s) env"
  by (auto simp: represents_def)

lemma represents_push_two:
  "represents slots s env \<Longrightarrow> represents (map (\<lambda>i. Suc (Suc i)) slots) (a # b # s) env"
  by (auto simp: represents_def)

lemma represents_bind:
  "represents slots s env \<Longrightarrow> represents (0 # map Suc slots) (v # s) (v # env)"
  by (auto simp: represents_def nth_Cons split: nat.splits)

theorem compile_correct:
  assumes "scoped (length env) e" "represents slots s env"
  shows "execute inputs (compile e slots) s = Some (evaluate e env inputs # s)"
  using assms
proof (induction e arbitrary: slots s env)
  case (Literal v)
  then show ?case by simp
next
  case (Input i)
  then show ?case by simp
next
  case (Variable i)
  then show ?case by (simp add: represents_def)
next
  case (Binary op a b)
  have a: "execute inputs (compile a slots) s = Some (evaluate a env inputs # s)"
    using Binary.IH(1) Binary.prems by simp
  have b: "execute inputs (compile b (map Suc slots)) (evaluate a env inputs # s) =
      Some (evaluate b env inputs # evaluate a env inputs # s)"
    using Binary.IH(2) Binary.prems represents_push by simp
  show ?case by (simp add: execute_append a b)
next
  case (Cond c a b)
  have c: "execute inputs (compile c slots) s = Some (evaluate c env inputs # s)"
    using Cond.IH(1) Cond.prems by simp
  have a: "execute inputs (compile a (map Suc slots)) (evaluate c env inputs # s) =
      Some (evaluate a env inputs # evaluate c env inputs # s)"
    using Cond.IH(2) Cond.prems represents_push by simp
  have b: "execute inputs (compile b (map (\<lambda>i. Suc (Suc i)) slots))
      (evaluate a env inputs # evaluate c env inputs # s) =
      Some (evaluate b env inputs # evaluate a env inputs # evaluate c env inputs # s)"
    using Cond.IH(3) Cond.prems represents_push_two by simp
  show ?case by (simp add: execute_append c a b)
next
  case (Let a b)
  have a: "execute inputs (compile a slots) s = Some (evaluate a env inputs # s)"
    using Let.IH(1) Let.prems by simp
  have b: "execute inputs (compile b (0 # map Suc slots)) (evaluate a env inputs # s) =
      Some (evaluate b (evaluate a env inputs # env) inputs # evaluate a env inputs # s)"
    using Let.IH(2) Let.prems represents_bind by simp
  show ?case by (simp add: execute_append a b)
qed

corollary compile_closed:
  "scoped 0 e \<Longrightarrow> execute inputs (compile (optimise e) []) [] = Some [evaluate e [] inputs]"
  using compile_correct[where e="optimise e" and env="[]" and slots="[]" and s="[]" and inputs=inputs]
  by (simp add: represents_def optimise_correct optimise_scoped)

fun height :: "instruction \<Rightarrow> nat \<Rightarrow> nat option" where
  "height (Constant v) n = Some (Suc n)"
| "height (Fetch i) n = Some (Suc n)"
| "height (Pick i) n = (if i < n then Some (Suc n) else None)"
| "height (Calculate op) n = (if 2 \<le> n then Some (n - 1) else None)"
| "height Choose n = (if 3 \<le> n then Some (n - 2) else None)"
| "height Slide n = (if 2 \<le> n then Some (n - 1) else None)"

fun check :: "instruction list \<Rightarrow> nat \<Rightarrow> nat option" where
  "check [] n = Some n"
| "check (i # code) n = Option.bind (height i n) (check code)"

lemma check_append:
  "check (a @ b) n = Option.bind (check a n) (check b)"
  by (induction a arbitrary: n) (auto split: option.splits bind_splits)

lemma step_height:
  "height i (length s) = Some n \<Longrightarrow> \<exists>t. step inputs i s = Some t \<and> length t = n"
  by (cases i; cases s; simp; rename_tac a xs; case_tac xs; simp;
      rename_tac b ys; case_tac ys; auto split: if_splits)

theorem check_sound:
  "check code (length s) = Some n \<Longrightarrow> \<exists>t. execute inputs code s = Some t \<and> length t = n"
proof (induction code arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons i code)
  then obtain m where h: "height i (length s) = Some m" and c: "check code m = Some n"
    by (auto simp: bind_eq_Some_conv)
  obtain t where step: "step inputs i s = Some t" and len: "length t = m"
    using step_height[OF h] by blast
  obtain u where run: "execute inputs code t = Some u" and "length u = n"
    using Cons.IH c len by blast
  then show ?case using step by simp
qed

fun demand :: "expression \<Rightarrow> nat" where
  "demand (Binary op a b) = max (demand a) (Suc (demand b))"
| "demand (Cond c a b) = max (demand c) (max (Suc (demand a)) (2 + demand b))"
| "demand (Let a b) = max (demand a) (Suc (demand b))"
| "demand _ = 1"

lemma demand_positive: "0 < demand e"
  by (induction e) auto

fun bounded :: "nat \<Rightarrow> instruction list \<Rightarrow> nat \<Rightarrow> bool" where
  "bounded limit [] n = (n \<le> limit)"
| "bounded limit (i # code) n = (n \<le> limit \<and> (case height i n of None \<Rightarrow> False | Some m \<Rightarrow> bounded limit code m))"

lemma bounded_start: "bounded limit code n \<Longrightarrow> n \<le> limit"
  by (cases code) auto

lemma bounded_append:
  "bounded limit (a @ b) n \<longleftrightarrow> bounded limit a n \<and> (\<exists>m. check a n = Some m \<and> bounded limit b m)"
  by (induction a arbitrary: n) (auto dest: bounded_start split: option.splits bind_splits)

lemma bounded_check:
  "bounded limit code n \<Longrightarrow> \<exists>m. check code n = Some m \<and> m \<le> limit"
  by (induction code arbitrary: n) (auto split: option.splits bind_splits)

theorem compiled_height:
  "scoped (length slots) e \<Longrightarrow> list_all (\<lambda>i. i < n) slots \<Longrightarrow>
    check (compile e slots) n = Some (Suc n)"
proof (induction e arbitrary: slots n)
  case (Literal v)
  then show ?case by simp
next
  case (Input i)
  then show ?case by simp
next
  case (Variable i)
  then show ?case by (simp add: list_all_length)
next
  case (Binary op a b)
  then show ?case
    by (simp add: check_append list_all_iff)
next
  case (Cond c a b)
  then show ?case by (simp add: check_append list_all_iff)
next
  case (Let a b)
  then show ?case by (simp add: check_append list_all_iff)
qed

theorem compiled_demand:
  assumes "scoped (length slots) e" "list_all (\<lambda>i. i < n) slots"
  shows "bounded limit (compile e slots) n \<longleftrightarrow> n + demand e \<le> limit"
  using assms
proof (induction e arbitrary: slots n)
  case (Literal v)
  then show ?case by auto
next
  case (Input i)
  then show ?case by auto
next
  case (Variable i)
  then show ?case by (auto simp: list_all_length)
next
  case (Binary op a b)
  then show ?case using demand_positive[of a] demand_positive[of b]
    by (auto simp: bounded_append compiled_height list_all_iff max_def; arith)
next
  case (Cond c a b)
  then show ?case using demand_positive[of c] demand_positive[of a] demand_positive[of b]
    by (auto simp: bounded_append compiled_height list_all_iff max_def; arith)
next
  case (Let a b)
  then show ?case using demand_positive[of a] demand_positive[of b]
    by (auto simp: bounded_append compiled_height list_all_iff max_def; arith)
qed

corollary closed_demand:
  "scoped 0 e \<Longrightarrow> bounded limit (compile e []) 0 \<longleftrightarrow> demand e \<le> limit"
  using compiled_demand[where slots="[]" and n=0] by simp

fun snapshots :: "(input \<Rightarrow> pixel) \<Rightarrow> instruction list \<Rightarrow> pixel list \<Rightarrow> (pixel list list) option" where
  "snapshots inputs [] s = Some [s]"
| "snapshots inputs (i # code) s = Option.bind (step inputs i s)
    (\<lambda>t. map_option ((#) s) (snapshots inputs code t))"

lemma snapshots_nonempty:
  "snapshots inputs code s = Some frames \<Longrightarrow> frames \<noteq> []"
  by (cases code) (auto split: bind_splits option.splits)

theorem snapshots_execute:
  "snapshots inputs code s = Some frames \<Longrightarrow> execute inputs code s = Some (last frames)"
proof (induction code arbitrary: s frames)
  case Nil
  then show ?case by auto
next
  case (Cons i code)
  then obtain t rest where step: "step inputs i s = Some t"
    and tail: "snapshots inputs code t = Some rest" and frames: "frames = s # rest"
    by (auto split: bind_splits option.splits)
  have "rest \<noteq> []" using snapshots_nonempty[OF tail] .
  then show ?case using Cons.IH[OF tail] step frames by simp
qed

theorem bounded_execution:
  "bounded limit code (length s) \<Longrightarrow>
    \<exists>frames. snapshots inputs code s = Some frames \<and> list_all (\<lambda>t. length t \<le> limit) frames"
proof (induction code arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons i code)
  then obtain m where bound: "length s \<le> limit" and h: "height i (length s) = Some m"
    and tail: "bounded limit code m"
    by (auto split: option.splits)
  obtain t where step: "step inputs i s = Some t" and len: "length t = m"
    using step_height[OF h] by blast
  obtain frames where trace: "snapshots inputs code t = Some frames"
    and safe: "list_all (\<lambda>t. length t \<le> limit) frames"
    using Cons.IH tail len by blast
  show ?case using step trace safe bound by auto
qed

corollary bounded_result:
  "bounded limit code (length s) \<Longrightarrow>
    \<exists>t. execute inputs code s = Some t \<and> length t \<le> limit"
proof -
  assume bound: "bounded limit code (length s)"
  obtain frames where trace: "snapshots inputs code s = Some frames"
    and safe: "list_all (\<lambda>t. length t \<le> limit) frames"
    using bounded_execution[OF bound] by blast
  have "frames \<noteq> []" using snapshots_nonempty[OF trace] .
  then have "length (last frames) \<le> limit" using safe by (simp add: list_all_iff)
  then show ?thesis using snapshots_execute[OF trace] by blast
qed

end
