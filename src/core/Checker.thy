theory Checker
  imports Encoding
begin

fun effect :: "opcode \<Rightarrow> nat \<Rightarrow> nat option" where
  "effect (Push r) n = Some (Suc n)"
| "effect (Pop r) n = (if n = 0 then None else Some (n - 1))"
| "effect (Peek i) n = (if i < n then Some n else None)"
| "effect _ n = Some n"

fun audit :: "opcode list \<Rightarrow> nat \<Rightarrow> nat option" where
  "audit [] n = Some n"
| "audit (op # code) n = (if writes op \<subseteq> {Rax,Rcx,Rbx} then
    Option.bind (effect op n) (\<lambda>m. if m \<le> 512 then audit code m else None) else None)"

lemma effect_sound:
  "effect op (length (stack s)) = Some n \<Longrightarrow>
    \<exists>t. transition op s = Some t \<and> length (stack t) = n"
  by (cases op; cases "stack s") (auto split: if_splits)

theorem audit_sound:
  "audit code (length (stack s)) = Some n \<Longrightarrow>
    \<exists>t. run code s = Some t \<and> length (stack t) = n"
proof (induction code arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons op code)
  then show ?case
    by (auto dest!: effect_sound split: if_splits bind_splits; fastforce)
qed

lemma audit_scratch:
  "audit code n = Some m \<Longrightarrow> list_all (\<lambda>op. writes op \<subseteq> {Rax,Rcx,Rbx}) code"
  by (induction code arbitrary: n) (auto split: if_splits bind_splits)

theorem audit_inputs:
  "audit code n = Some m \<Longrightarrow> run code s = Some t \<Longrightarrow> inputs t = inputs s"
proof -
  assume audited: "audit code n = Some m" and ran: "run code s = Some t"
  have scratch: "list_all (\<lambda>op. writes op \<subseteq> {Rax,Rcx,Rbx}) code"
    using audit_scratch[OF audited] .
  show ?thesis
  proof (rule ext)
    fix i
    have keep: "list_all (\<lambda>op. input_register i \<notin> writes op) code"
      unfolding list_all_iff
    proof (rule ballI)
      fix op
      assume member: "op \<in> set code"
      have bound: "writes op \<subseteq> {Rax,Rcx,Rbx}"
        using scratch member by (auto simp: list_all_iff)
      show "input_register i \<notin> writes op"
      proof
        assume written: "input_register i \<in> writes op"
        have "input_register i \<in> {Rax,Rcx,Rbx}"
          using subsetD[OF bound written] .
        then show False by simp
      qed
    qed
    show "inputs t i = inputs s i"
      unfolding inputs_def using run_preserves[OF ran keep] .
  qed
qed

end
