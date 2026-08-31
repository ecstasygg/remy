theory Native
  imports Compiler
begin

datatype register = Rax | Rcx | Rbx | Rdx | R8 | R9

datatype opcode = Immediate pixel | Push register | Pop register | Peek nat
  | Arithmetic operator | Conditional

record machine =
  registers :: "register \<Rightarrow> pixel"
  stack :: "pixel list"

fun input_register :: "input \<Rightarrow> register" where
  "input_register X = R8"
| "input_register Y = R9"
| "input_register T = Rdx"

definition inputs :: "machine \<Rightarrow> input \<Rightarrow> pixel" where
  "inputs s i = registers s (input_register i)"

fun exchanges :: "operator \<Rightarrow> bool" where
  "exchanges Sub = True"
| "exchanges Shl = True"
| "exchanges Shr = True"
| "exchanges Less = True"
| "exchanges _ = False"

fun transition :: "opcode \<Rightarrow> machine \<Rightarrow> machine option" where
  "transition (Immediate v) s = Some (s\<lparr>registers := (registers s)(Rax := v)\<rparr>)"
| "transition (Push r) s = Some (s\<lparr>stack := registers s r # stack s\<rparr>)"
| "transition (Pop r) s = (case stack s of [] \<Rightarrow> None | v # vs \<Rightarrow>
    Some (s\<lparr>registers := (registers s)(r := v), stack := vs\<rparr>))"
| "transition (Peek i) s = (if i < length (stack s) then
    Some (s\<lparr>registers := (registers s)(Rax := stack s ! i)\<rparr>) else None)"
| "transition (Arithmetic op) s = Some (s\<lparr>registers :=
    (registers s)(Rcx := if exchanges op then registers s Rax else registers s Rcx,
      Rax := operate op (registers s Rcx) (registers s Rax))\<rparr>)"
| "transition Conditional s = Some (s\<lparr>registers :=
    (registers s)(Rax := if registers s Rbx = 0 then registers s Rax else registers s Rcx)\<rparr>)"

fun run :: "opcode list \<Rightarrow> machine \<Rightarrow> machine option" where
  "run [] s = Some s"
| "run (i # code) s = Option.bind (transition i s) (run code)"

lemma run_append:
  "run (a @ b) s = Option.bind (run a s) (run b)"
  by (induction a arbitrary: s) (auto split: option.splits bind_splits)

fun lower :: "instruction \<Rightarrow> opcode list" where
  "lower (Constant v) = [Immediate v, Push Rax]"
| "lower (Fetch i) = [Push (input_register i)]"
| "lower (Pick i) = [Peek i, Push Rax]"
| "lower (Calculate op) = [Pop Rax, Pop Rcx, Arithmetic op, Push Rax]"
| "lower Choose = [Pop Rax, Pop Rcx, Pop Rbx, Conditional, Push Rax]"
| "lower Slide = [Pop Rax, Pop Rcx, Push Rax]"

definition observe :: "machine \<Rightarrow> (input \<Rightarrow> pixel) \<times> pixel list" where
  "observe s = (inputs s, stack s)"

lemma input_scratch [simp]:
  "input_register i \<noteq> Rax"
  "input_register i \<noteq> Rcx"
  "input_register i \<noteq> Rbx"
  by (cases i; simp)+

lemma inputs_update [simp]:
  "inputs (s\<lparr>registers := (registers s)(Rax := a)\<rparr>) = inputs s"
  "inputs (s\<lparr>registers := (registers s)(Rcx := a)\<rparr>) = inputs s"
  "inputs (s\<lparr>registers := (registers s)(Rbx := a)\<rparr>) = inputs s"
  "inputs (s\<lparr>stack := vs\<rparr>) = inputs s"
  by (auto simp: inputs_def fun_eq_iff split: input.splits)

theorem lower_correct:
  "map_option observe (run (lower i) s) =
    map_option (\<lambda>vs. (inputs s, vs)) (step (inputs s) i (stack s))"
proof (cases i)
  case (Constant v)
  then show ?thesis by (simp add: observe_def)
next
  case (Fetch i)
  then show ?thesis by (simp add: observe_def inputs_def)
next
  case (Pick i)
  then show ?thesis by (simp add: observe_def)
next
  case (Calculate op)
  then show ?thesis
    by (cases "stack s"; simp add: observe_def inputs_def fun_eq_iff split: list.splits input.splits)
next
  case Choose
  then show ?thesis
    by (cases "stack s"; simp add: observe_def inputs_def fun_eq_iff split: list.splits input.splits)
next
  case Slide
  then show ?thesis
    by (cases "stack s"; simp add: observe_def inputs_def fun_eq_iff split: list.splits input.splits)
qed

definition native :: "instruction list \<Rightarrow> opcode list" where
  "native code = concat (map lower code)"

theorem native_correct:
  "map_option observe (run (native code) s) =
    map_option (\<lambda>vs. (inputs s, vs)) (execute (inputs s) code (stack s))"
proof (induction code arbitrary: s)
  case Nil
  then show ?case by (simp add: native_def observe_def)
next
  case (Cons i code)
  show ?case
    using Cons.IH lower_correct[of i s]
    by (auto simp: native_def run_append observe_def split: option.splits bind_splits)
qed

corollary native_expression:
  assumes "scoped 0 e"
  shows "map_option observe (run (native (compile (optimise e) [])) s) =
    Some (inputs s, evaluate e [] (inputs s) # stack s)"
proof -
  have code: "execute (inputs s) (compile (optimise e) []) (stack s) =
      Some (evaluate e [] (inputs s) # stack s)"
    using compile_correct[where e="optimise e" and env="[]" and slots="[]" and s="stack s" and inputs="inputs s"]
      assms optimise_scoped
    by (simp add: represents_def optimise_correct)
  show ?thesis using native_correct[of "compile (optimise e) []" s] code by simp
qed

theorem native_return:
  assumes "scoped 0 e"
  shows "\<exists>q. run (native (compile (optimise e) []) @ [Pop Rax]) s = Some q \<and>
    registers q Rax = evaluate e [] (inputs s) \<and> stack q = stack s \<and> inputs q = inputs s"
proof -
  obtain q where run: "run (native (compile (optimise e) [])) s = Some q"
    and ins: "inputs q = inputs s" and stk: "stack q = evaluate e [] (inputs s) # stack s"
    using native_expression[OF assms, of s]
    by (auto simp: observe_def split: option.splits)
  show ?thesis using run ins stk
    by (auto simp: run_append inputs_def fun_eq_iff)
qed

fun writes :: "opcode \<Rightarrow> register set" where
  "writes (Immediate v) = {Rax}"
| "writes (Pop r) = {r}"
| "writes (Peek i) = {Rax}"
| "writes (Arithmetic op) = {Rax,Rcx}"
| "writes Conditional = {Rax}"
| "writes _ = {}"

lemma transition_preserves:
  "transition i s = Some t \<Longrightarrow> r \<notin> writes i \<Longrightarrow> registers t r = registers s r"
  by (cases i) (auto split: list.splits if_splits)

theorem run_preserves:
  "run code s = Some t \<Longrightarrow> list_all (\<lambda>i. r \<notin> writes i) code \<Longrightarrow>
    registers t r = registers s r"
  by (induction code arbitrary: s) (auto dest: transition_preserves split: option.splits bind_splits)

lemma lower_scratch:
  "list_all (\<lambda>i. writes i \<subseteq> {Rax,Rcx,Rbx}) (lower op)"
  by (cases op) auto

end
