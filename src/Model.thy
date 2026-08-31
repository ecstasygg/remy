theory Model
  imports "HOL-Library.Word" "HOL-Library.Code_Target_Numeral"
begin

unbundle bit_operations_syntax

type_synonym pixel = "64 word"

datatype input = X | Y | T

datatype operator = Add | Sub | Mul | And | Or | Xor | Shl | Shr | Less

fun operate :: "operator \<Rightarrow> pixel \<Rightarrow> pixel \<Rightarrow> pixel" where
  "operate Add a b = a + b"
| "operate Sub a b = a - b"
| "operate Mul a b = a * b"
| "operate And a b = a AND b"
| "operate Or a b = a OR b"
| "operate Xor a b = a XOR b"
| "operate Shl a b = push_bit (unat b mod 64) a"
| "operate Shr a b = drop_bit (unat b mod 64) a"
| "operate Less a b = (if a < b then 1 else 0)"

datatype expression = Literal pixel | Input input | Variable nat
  | Binary operator expression expression
  | Cond expression expression expression
  | Let expression expression

fun evaluate :: "expression \<Rightarrow> pixel list \<Rightarrow> (input \<Rightarrow> pixel) \<Rightarrow> pixel" where
  "evaluate (Literal v) env inputs = v"
| "evaluate (Input i) env inputs = inputs i"
| "evaluate (Variable i) env inputs = env ! i"
| "evaluate (Binary op a b) env inputs = operate op (evaluate a env inputs) (evaluate b env inputs)"
| "evaluate (Cond c a b) env inputs = (if evaluate c env inputs = 0 then evaluate b env inputs else evaluate a env inputs)"
| "evaluate (Let a b) env inputs = evaluate b (evaluate a env inputs # env) inputs"

fun scoped :: "nat \<Rightarrow> expression \<Rightarrow> bool" where
  "scoped n (Literal v) = True"
| "scoped n (Input i) = True"
| "scoped n (Variable i) = (i < n)"
| "scoped n (Binary op a b) = (scoped n a \<and> scoped n b)"
| "scoped n (Cond c a b) = (scoped n c \<and> scoped n a \<and> scoped n b)"
| "scoped n (Let a b) = (scoped n a \<and> scoped (Suc n) b)"

fun fold_binary :: "operator \<Rightarrow> expression \<Rightarrow> expression \<Rightarrow> expression" where
  "fold_binary op (Literal a) (Literal b) = Literal (operate op a b)"
| "fold_binary op a b = Binary op a b"

fun fold_cond :: "expression \<Rightarrow> expression \<Rightarrow> expression \<Rightarrow> expression" where
  "fold_cond (Literal c) a b = (if c = 0 then b else a)"
| "fold_cond c a b = Cond c a b"

fun optimise :: "expression \<Rightarrow> expression" where
  "optimise (Binary op a b) = fold_binary op (optimise a) (optimise b)"
| "optimise (Cond c a b) = fold_cond (optimise c) (optimise a) (optimise b)"
| "optimise (Let a b) = Let (optimise a) (optimise b)"
| "optimise e = e"

lemma fold_binary_value:
  "evaluate (fold_binary op a b) env inputs = operate op (evaluate a env inputs) (evaluate b env inputs)"
  by (cases a; cases b) auto

lemma fold_cond_value:
  "evaluate (fold_cond c a b) env inputs = (if evaluate c env inputs = 0 then evaluate b env inputs else evaluate a env inputs)"
  by (cases c) auto

theorem optimise_correct:
  "evaluate (optimise e) env inputs = evaluate e env inputs"
  by (induction e arbitrary: env) (simp_all add: fold_binary_value fold_cond_value)

lemma fold_binary_scoped:
  "scoped n a \<Longrightarrow> scoped n b \<Longrightarrow> scoped n (fold_binary op a b)"
  by (cases a; cases b) auto

lemma fold_cond_scoped:
  "scoped n c \<Longrightarrow> scoped n a \<Longrightarrow> scoped n b \<Longrightarrow> scoped n (fold_cond c a b)"
  by (cases c) auto

theorem optimise_scoped: "scoped n e \<Longrightarrow> scoped n (optimise e)"
  by (induction e arbitrary: n) (auto intro: fold_binary_scoped fold_cond_scoped)

fun nodes :: "expression \<Rightarrow> nat" where
  "nodes (Binary op a b) = Suc (nodes a + nodes b)"
| "nodes (Cond c a b) = Suc (nodes c + nodes a + nodes b)"
| "nodes (Let a b) = Suc (nodes a + nodes b)"
| "nodes _ = 1"

lemma fold_binary_nodes: "nodes (fold_binary op a b) \<le> Suc (nodes a + nodes b)"
  by (cases a; cases b) auto

lemma fold_cond_nodes: "nodes (fold_cond c a b) \<le> Suc (nodes c + nodes a + nodes b)"
  by (cases c) auto

theorem optimise_size: "nodes (optimise e) \<le> nodes e"
  by (induction e) (auto intro: order_trans[OF fold_binary_nodes] order_trans[OF fold_cond_nodes])

end
