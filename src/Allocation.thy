theory Allocation
  imports "Remybase.Checker"
begin

fun allocate :: "bool \<Rightarrow> expression \<Rightarrow> nat list \<Rightarrow> opcode list" where
  "allocate free (Literal v) slots = [Immediate v]"
| "allocate free (Input i) slots = [Move Rax (input_register i)]"
| "allocate free (Variable i) slots = [Peek (slots ! i)]"
| "allocate free (Binary op a b) slots = (if free then
    allocate True a slots @ [Move Rbx Rax] @ allocate False b slots @
      [Move Rcx Rbx, Arithmetic op]
    else allocate False a slots @ [Push Rax] @ allocate False b (map Suc slots) @
      [Pop Rcx, Arithmetic op])"
| "allocate free (Cond c a b) slots = [Push Rbx] @
    allocate True c (map Suc slots) @ [Push Rax] @
    allocate True a (map (\<lambda>i. Suc (Suc i)) slots) @ [Push Rax] @
    allocate True b (map (\<lambda>i. Suc (Suc (Suc i))) slots) @
    [Pop Rcx, Pop Rbx, Conditional, Pop Rbx]"
| "allocate free (Let a b) slots = allocate free a slots @ [Push Rax] @
    allocate free b (0 # map Suc slots) @ [Pop Rcx]"

definition allocated_result :: "bool \<Rightarrow> expression \<Rightarrow> pixel list \<Rightarrow> machine \<Rightarrow> machine \<Rightarrow> bool" where
  "allocated_result free e env s q \<longleftrightarrow>
    registers q Rax = evaluate e env (inputs s) \<and> stack q = stack s \<and>
    inputs q = inputs s \<and> (\<not> free \<longrightarrow> registers q Rbx = registers s Rbx)"

theorem allocate_correct:
  assumes "scoped (length env) e" "represents slots (stack s) env"
  shows "\<exists>q. run (allocate free e slots) s = Some q \<and> allocated_result free e env s q"
  using assms
proof (induction e arbitrary: free slots env s)
  case (Literal v)
  then show ?case by (auto simp: allocated_result_def)
next
  case (Input i)
  then show ?case by (auto simp: allocated_result_def inputs_def fun_eq_iff)
next
  case (Variable i)
  then show ?case by (auto simp: allocated_result_def represents_def)
next
  case (Binary op a b)
  obtain p where a: "run (allocate free a slots) s = Some p"
    and p: "allocated_result free a env s p"
    using Binary.IH(1)[of env slots s free] Binary.prems by auto
  show ?case
  proof (cases free)
    case True
    let ?p = "p\<lparr>registers := (registers p)(Rbx := registers p Rax)\<rparr>"
    obtain q where b: "run (allocate False b slots) ?p = Some q"
      and q: "allocated_result False b env ?p q"
      using Binary.IH(2)[of env slots ?p False] Binary.prems p
      by (auto simp: allocated_result_def)
    show ?thesis using a b p q True
      by (auto simp: allocated_result_def run_append; auto simp: inputs_def fun_eq_iff)
  next
    case False
    let ?p = "p\<lparr>stack := registers p Rax # stack p\<rparr>"
    obtain q where b: "run (allocate False b (map Suc slots)) ?p = Some q"
      and q: "allocated_result False b env ?p q"
      using Binary.IH(2)[of env "map Suc slots" ?p False] Binary.prems p
        represents_push[OF Binary.prems(2), of "registers p Rax"]
      by (auto simp: allocated_result_def)
    show ?thesis using a b p q False
      by (auto simp: allocated_result_def run_append; auto simp: inputs_def fun_eq_iff)
  qed
next
  case (Cond c a b)
  have sc: "scoped (length env) c" and sa: "scoped (length env) a"
    and sb: "scoped (length env) b" using Cond.prems by auto
  let ?s = "s\<lparr>stack := registers s Rbx # stack s\<rparr>"
  have repc: "represents (map Suc slots) (stack ?s) env"
    using represents_push[OF Cond.prems(2)] by simp
  obtain p where c: "run (allocate True c (map Suc slots)) ?s = Some p"
    and p: "allocated_result True c env ?s p"
    using Cond.IH(1)[of env "map Suc slots" ?s True] sc repc by blast
  let ?p = "p\<lparr>stack := registers p Rax # stack p\<rparr>"
  have repa: "represents (map (\<lambda>i. Suc (Suc i)) slots) (stack ?p) env"
    using Cond.prems(2) p by (auto simp: allocated_result_def represents_def)
  obtain q where a: "run (allocate True a (map (\<lambda>i. Suc (Suc i)) slots)) ?p = Some q"
    and q: "allocated_result True a env ?p q"
    using Cond.IH(2)[of env "map (\<lambda>i. Suc (Suc i)) slots" ?p True] sa repa by blast
  let ?q = "q\<lparr>stack := registers q Rax # stack q\<rparr>"
  have repb: "represents (map (\<lambda>i. Suc (Suc (Suc i))) slots) (stack ?q) env"
    using Cond.prems(2) p q by (auto simp: allocated_result_def represents_def)
  obtain r where b: "run (allocate True b (map (\<lambda>i. Suc (Suc (Suc i))) slots)) ?q = Some r"
    and r: "allocated_result True b env ?q r"
    using Cond.IH(3)[of env "map (\<lambda>i. Suc (Suc (Suc i))) slots" ?q True] sb repb by blast
  show ?case using c a b p q r
    by (auto simp: allocated_result_def run_append; auto simp: inputs_def fun_eq_iff)
next
  case (Let a b)
  obtain p where a: "run (allocate free a slots) s = Some p"
    and p: "allocated_result free a env s p"
    using Let.IH(1)[of env slots s free] Let.prems by auto
  let ?p = "p\<lparr>stack := registers p Rax # stack p\<rparr>"
  obtain q where b: "run (allocate free b (0 # map Suc slots)) ?p = Some q"
    and q: "allocated_result free b (registers p Rax # env) ?p q"
    using Let.IH(2)[of "registers p Rax # env" "0 # map Suc slots" ?p free]
      Let.prems p represents_bind[OF Let.prems(2), of "registers p Rax"]
    by (auto simp: allocated_result_def)
  show ?case using a b p q
    by (auto simp: allocated_result_def run_append; auto simp: inputs_def fun_eq_iff)
qed

definition allocated :: "expression \<Rightarrow> opcode list" where
  "allocated e = transfers (allocate True (optimise e) [])"

theorem allocated_return:
  "scoped 0 e \<Longrightarrow> \<exists>q. run (allocated e) s = Some q \<and>
    registers q Rax = evaluate e [] (inputs s) \<and> stack q = stack s \<and> inputs q = inputs s"
  using allocate_correct[where env="[]" and slots="[]" and free=True and e="optimise e"]
    optimise_scoped
  by (auto simp: allocated_def transfers_correct allocated_result_def represents_def optimise_correct)

definition allocated_bytes :: "expression \<Rightarrow> nat list" where
  "allocated_bytes e = concat (map encode (allocated e)) @ [195]"

lemma allocated_add:
  "allocated (Binary Add (Input X) (Input Y)) =
    [Move Rax R8, Move Rbx Rax, Move Rax R9, Move Rcx Rbx, Arithmetic Add]"
  by eval

end
