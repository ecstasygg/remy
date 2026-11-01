theory Branches
  imports Allocation
begin

datatype flow = Basic "opcode list" | Sequence flow flow | Choice flow flow

fun flowrun :: "flow \<Rightarrow> machine \<Rightarrow> machine option" where
  "flowrun (Basic code) s = run code s"
| "flowrun (Sequence a b) s = Option.bind (flowrun a s) (flowrun b)"
| "flowrun (Choice a b) s = flowrun (if registers s Rax = 0 then b else a) s"

fun chain :: "flow list \<Rightarrow> flow" where
  "chain [] = Basic []"
| "chain (a # code) = Sequence a (chain code)"

fun branch_allocate :: "bool \<Rightarrow> expression \<Rightarrow> nat list \<Rightarrow> flow" where
  "branch_allocate free (Literal v) slots = Basic [Immediate v]"
| "branch_allocate free (Input i) slots = Basic [Move Rax (input_register i)]"
| "branch_allocate free (Variable i) slots = Basic [Peek (slots ! i)]"
| "branch_allocate free (Binary op a b) slots = (if free then
    chain [branch_allocate True a slots, Basic [Move Rbx Rax], branch_allocate False b slots,
      Basic [Move Rcx Rbx, Arithmetic op]]
    else chain [branch_allocate False a slots, Basic [Push Rax], branch_allocate False b (map Suc slots),
      Basic [Pop Rcx, Arithmetic op]])"
| "branch_allocate free (Cond c a b) slots = Sequence (branch_allocate free c slots)
    (Choice (branch_allocate free a slots) (branch_allocate free b slots))"
| "branch_allocate free (Let a b) slots = chain [branch_allocate free a slots, Basic [Push Rax],
    branch_allocate free b (0 # map Suc slots), Basic [Pop Rcx]]"

theorem branch_allocate_correct:
  assumes "scoped (length env) e" "represents slots (stack s) env"
  shows "\<exists>q. flowrun (branch_allocate free e slots) s = Some q \<and> allocated_result free e env s q"
  using assms
proof (induction e arbitrary: free slots env s)
  case (Literal v)
  then show ?case by (auto simp: allocated_result_def chain.simps)
next
  case (Input i)
  then show ?case by (auto simp: allocated_result_def inputs_def fun_eq_iff)
next
  case (Variable i)
  then show ?case by (auto simp: allocated_result_def represents_def)
next
  case (Binary op a b)
  obtain p where a: "flowrun (branch_allocate free a slots) s = Some p"
    and p: "allocated_result free a env s p"
    using Binary.IH(1)[of env slots s free] Binary.prems by auto
  show ?case
  proof (cases free)
    case True
    let ?p = "p\<lparr>registers := (registers p)(Rbx := registers p Rax)\<rparr>"
    obtain q where b: "flowrun (branch_allocate False b slots) ?p = Some q"
      and q: "allocated_result False b env ?p q"
      using Binary.IH(2)[of env slots ?p False] Binary.prems p
      by (auto simp: allocated_result_def chain.simps)
    show ?thesis using a b p q True
      by (auto simp: allocated_result_def run_append flowrun.simps chain.simps; auto simp: inputs_def fun_eq_iff)
  next
    case False
    let ?p = "p\<lparr>stack := registers p Rax # stack p\<rparr>"
    obtain q where b: "flowrun (branch_allocate False b (map Suc slots)) ?p = Some q"
      and q: "allocated_result False b env ?p q"
      using Binary.IH(2)[of env "map Suc slots" ?p False] Binary.prems p
        represents_push[OF Binary.prems(2), of "registers p Rax"]
      by (auto simp: allocated_result_def chain.simps)
    show ?thesis using a b p q False
      by (auto simp: allocated_result_def run_append flowrun.simps chain.simps; auto simp: inputs_def fun_eq_iff)
  qed
next
  case (Cond c a b)
  obtain p where c: "flowrun (branch_allocate free c slots) s = Some p"
    and p: "allocated_result free c env s p"
    using Cond.IH(1)[of env slots s free] Cond.prems by auto
  show ?case
    using Cond.IH(2)[of env slots p free] Cond.IH(3)[of env slots p free]
      Cond.prems c p
    by (auto simp: allocated_result_def split: if_splits)
next
  case (Let a b)
  obtain p where a: "flowrun (branch_allocate free a slots) s = Some p"
    and p: "allocated_result free a env s p"
    using Let.IH(1)[of env slots s free] Let.prems by auto
  let ?p = "p\<lparr>stack := registers p Rax # stack p\<rparr>"
  obtain q where b: "flowrun (branch_allocate free b (0 # map Suc slots)) ?p = Some q"
    and q: "allocated_result free b (registers p Rax # env) ?p q"
    using Let.IH(2)[of "registers p Rax # env" "0 # map Suc slots" ?p free]
      Let.prems p represents_bind[OF Let.prems(2), of "registers p Rax"]
    by (auto simp: allocated_result_def chain.simps)
  show ?case using a b p q
    by (auto simp: allocated_result_def run_append flowrun.simps chain.simps; auto simp: inputs_def fun_eq_iff)
qed

definition branching :: "expression \<Rightarrow> flow" where
  "branching e = branch_allocate True (optimise e) []"

theorem branching_return:
  "scoped 0 e \<Longrightarrow> \<exists>q. flowrun (branching e) s = Some q \<and>
    registers q Rax = evaluate e [] (inputs s) \<and> stack q = stack s \<and> inputs q = inputs s"
  using branch_allocate_correct[where env="[]" and slots="[]" and free=True and e="optimise e"]
    optimise_scoped
  by (auto simp: branching_def allocated_result_def represents_def optimise_correct)

fun flowaudit :: "flow \<Rightarrow> nat \<Rightarrow> nat option" where
  "flowaudit (Basic code) n = audit code n"
| "flowaudit (Sequence a b) n = Option.bind (flowaudit a n) (flowaudit b)"
| "flowaudit (Choice a b) n = (case (flowaudit a n, flowaudit b n) of
    (Some x,Some y) \<Rightarrow> if x = y then Some x else None | _ \<Rightarrow> None)"

theorem flowaudit_sound:
  "flowaudit code (length (stack s)) = Some n \<Longrightarrow>
    \<exists>q. flowrun code s = Some q \<and> length (stack q) = n \<and> inputs q = inputs s"
proof (induction code arbitrary: s n)
  case (Basic code)
  then show ?case using audit_sound audit_inputs by fastforce
next
  case (Sequence a b)
  then show ?case by (auto split: option.splits bind_splits; fastforce)
next
  case (Choice a b)
  then show ?case by (auto split: option.splits if_splits; fastforce)
qed

fun flowbytes :: "flow \<Rightarrow> nat list" where
  "flowbytes (Basic code) = concat (map encode code)"
| "flowbytes (Sequence a b) = flowbytes a @ flowbytes b"
| "flowbytes (Choice a b) = [72,133,192,15,132] @ octets 4 (length (flowbytes a) + 5) @
    flowbytes a @ [233] @ octets 4 (length (flowbytes b)) @ flowbytes b"

fun flowvalid :: "flow \<Rightarrow> bool" where
  "flowvalid (Basic code) = list_all encodable code"
| "flowvalid (Sequence a b) = (flowvalid a \<and> flowvalid b)"
| "flowvalid (Choice a b) = (flowvalid a \<and> flowvalid b \<and>
    length (flowbytes a) + 5 < 2 ^ 31 \<and> length (flowbytes b) < 2 ^ 31)"

lemma flowbytes_bytes: "set (flowbytes code) \<subseteq> {..<256}"
  by (induction code) (auto dest: subsetD[OF encode_bytes] subsetD[OF octets_bytes])

function unpack :: "nat \<Rightarrow> nat list \<Rightarrow> flow option" where
  "unpack 0 bytes = (if bytes = [] then Some (Basic []) else None)"
| "unpack (Suc fuel) bytes = (if bytes = [] then Some (Basic []) else
    if take 5 bytes = [72,133,192,15,132] then
      let offset = integer (take 4 (drop 5 bytes)); pos = 9 + (offset - 5);
        count = integer (take 4 (drop (Suc pos) bytes)) in
      if 9 \<le> length bytes \<and> 5 \<le> offset \<and> pos + 5 + count \<le> length bytes \<and>
        bytes ! pos = 233 then
        Option.bind (unpack fuel (take (offset - 5) (drop 9 bytes))) (\<lambda>a.
        Option.bind (unpack fuel (take count (drop (pos + 5) bytes))) (\<lambda>b.
        map_option (Sequence (Choice a b)) (unpack fuel (drop (pos + 5 + count) bytes))))
      else None
    else Option.bind (decode bytes) (\<lambda>(op,rest).
      map_option (Sequence (Basic [op])) (unpack fuel rest)))"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(fuel,bytes). fuel)") auto

declare unpack.simps [simp del]

definition inspect :: "nat list \<Rightarrow> flow option" where
  "inspect bytes = (if bytes = [] \<or> last bytes \<noteq> 195 \<or> \<not> list_all (\<lambda>b. b < 256) bytes then None else
    Option.bind (unpack (length bytes) (butlast bytes)) (\<lambda>code.
      if flowvalid code \<and> flowbytes code = butlast bytes \<and> flowaudit code 0 = Some 0
      then Some code else None))"

theorem inspected_sound:
  "inspect bytes = Some code \<Longrightarrow> \<exists>q. flowrun code (s\<lparr>stack := []\<rparr>) = Some q \<and>
    stack q = [] \<and> inputs q = inputs s"
  using flowaudit_sound[where s="s\<lparr>stack := []\<rparr>" and n=0]
  by (auto simp: inspect_def split: if_splits option.splits bind_splits)

end
