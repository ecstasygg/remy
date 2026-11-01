theory Bounds
  imports Branches
begin

fun guarded_run :: "nat \<Rightarrow> opcode list \<Rightarrow> machine \<Rightarrow> bool" where
  "guarded_run limit [] s = (length (stack s) \<le> limit)"
| "guarded_run limit (op # code) s = (length (stack s) \<le> limit \<and>
    (case transition op s of None \<Rightarrow> False | Some q \<Rightarrow> guarded_run limit code q))"

fun guarded_flow :: "nat \<Rightarrow> flow \<Rightarrow> machine \<Rightarrow> bool" where
  "guarded_flow limit (Basic code) s = guarded_run limit code s"
| "guarded_flow limit (Sequence a b) s = (guarded_flow limit a s \<and>
    (case flowrun a s of None \<Rightarrow> False | Some q \<Rightarrow> guarded_flow limit b q))"
| "guarded_flow limit (Choice a b) s = guarded_flow limit (if registers s Rax = 0 then b else a) s"

lemma effect_shift:
  "effect op n = Some m \<Longrightarrow> effect op (n + base) = Some (m + base)"
  by (cases op; cases n; auto split: if_splits; arith)

lemma effect_frame:
  "effect op n = Some m \<Longrightarrow> transition op s = Some q \<Longrightarrow>
    drop m (stack q) = drop n (stack s)"
  by (cases op; cases n; cases "stack s") (auto simp: effect.simps transition.simps split: if_splits)

lemma audit_limit:
  "n \<le> 512 \<Longrightarrow> audit code n = Some m \<Longrightarrow> m \<le> 512"
  by (induction code arbitrary: n) (auto split: if_splits bind_splits)

lemma flowaudit_limit:
  "n \<le> 512 \<Longrightarrow> flowaudit code n = Some m \<Longrightarrow> m \<le> 512"
proof (induction code arbitrary: n m)
  case (Basic code)
  then show ?case by (auto dest: audit_limit)
next
  case (Sequence a b)
  obtain k where a: "flowaudit a n = Some k" and b: "flowaudit b k = Some m"
    using Sequence.prems(2) by (auto split: bind_splits)
  have "k \<le> 512" using Sequence.IH(1)[OF Sequence.prems(1) a] .
  then show ?case using Sequence.IH(2)[OF _ b] by blast
next
  case (Choice a b)
  have "flowaudit a n = Some m"
    using Choice.prems(2) by (auto split: option.splits if_splits)
  then show ?case using Choice.IH(1)[OF Choice.prems(1)] by blast
qed

theorem audit_window:
  assumes "length (stack s) = base + n" "n \<le> 512" "audit code n = Some m"
  shows "\<exists>q. run code s = Some q \<and> length (stack q) = base + m \<and>
    drop m (stack q) = drop n (stack s) \<and> guarded_run (base + 512) code s"
  using assms
proof (induction code arbitrary: s n m)
  case Nil
  then show ?case by auto
next
  case (Cons op code)
  obtain k where effect: "effect op n = Some k" and bound: "k \<le> 512"
    and tail: "audit code k = Some m"
    using Cons.prems(3) by (auto split: if_splits bind_splits)
  have shifted: "effect op (length (stack s)) = Some (base + k)"
    using effect_shift[OF effect, of base] Cons.prems(1) by (simp add: add.commute)
  obtain p where p: "transition op s = Some p" "length (stack p) = base + k"
    using effect_sound[OF shifted] by blast
  obtain q where q: "run code p = Some q" "length (stack q) = base + m"
    "drop m (stack q) = drop k (stack p)" "guarded_run (base + 512) code p"
    using Cons.IH[OF p(2) bound tail] by blast
  have frame: "drop k (stack p) = drop n (stack s)"
    using effect_frame[OF effect p(1)] .
  have "length (stack s) \<le> base + 512" using Cons.prems(1,2) by arith
  then show ?case using p q frame by auto
qed

theorem flow_window:
  assumes "length (stack s) = base + n" "n \<le> 512" "flowaudit code n = Some m"
  shows "\<exists>q. flowrun code s = Some q \<and> length (stack q) = base + m \<and>
    drop m (stack q) = drop n (stack s) \<and> inputs q = inputs s \<and>
    guarded_flow (base + 512) code s"
  using assms
proof (induction code arbitrary: s n m)
  case (Basic code)
  have audit: "audit code n = Some m" using Basic.prems by simp
  obtain q where q: "run code s = Some q" "length (stack q) = base + m"
    "drop m (stack q) = drop n (stack s)" "guarded_run (base + 512) code s"
    using audit_window[OF Basic.prems(1,2) audit] by blast
  show ?case using q audit_inputs[OF audit q(1)] by auto
next
  case (Sequence a b)
  obtain k where a: "flowaudit a n = Some k" and b: "flowaudit b k = Some m"
    using Sequence.prems(3) by (auto split: bind_splits)
  obtain p where p: "flowrun a s = Some p" "length (stack p) = base + k"
    "drop k (stack p) = drop n (stack s)" "inputs p = inputs s"
    "guarded_flow (base + 512) a s"
    using Sequence.IH(1)[OF Sequence.prems(1,2) a] by blast
  have bound: "k \<le> 512" using flowaudit_limit[OF Sequence.prems(2) a] .
  obtain q where q: "flowrun b p = Some q" "length (stack q) = base + m"
    "drop m (stack q) = drop k (stack p)" "inputs q = inputs p"
    "guarded_flow (base + 512) b p"
    using Sequence.IH(2)[OF p(2) bound b] by blast
  show ?case using p q by auto
next
  case (Choice a b)
  have a: "flowaudit a n = Some m" and b: "flowaudit b n = Some m"
    using Choice.prems(3) by (auto split: option.splits if_splits)
  show ?case
    using Choice.IH(1)[OF Choice.prems(1,2) a] Choice.IH(2)[OF Choice.prems(1,2) b]
    by (cases "registers s Rax = 0") auto
qed

corollary checked_frame:
  "flowaudit code 0 = Some 0 \<Longrightarrow> \<exists>q. flowrun code s = Some q \<and>
    stack q = stack s \<and> inputs q = inputs s \<and>
    guarded_flow (length (stack s) + 512) code s"
  using flow_window[where s=s and base="length (stack s)" and n=0 and m=0 and code=code]
  by auto

end
