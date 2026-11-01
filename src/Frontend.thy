theory Frontend
  imports X86
begin

fun finish :: "string \<Rightarrow> string list \<Rightarrow> string list" where
  "finish [] out = out"
| "finish word out = rev word # out"

fun scan :: "string \<Rightarrow> string \<Rightarrow> string list \<Rightarrow> bool \<Rightarrow> string list" where
  "scan [] word out comment = rev (finish word out)"
| "scan (c # cs) word out comment = (if comment then
      scan cs [] out (c \<noteq> CHR 0x0A \<and> c \<noteq> CHR 0x0D)
    else if c = CHR '';'' then scan cs [] (finish word out) True
    else if c = CHR '' '' \<or> c = CHR 0x09 \<or> c = CHR 0x0A \<or> c = CHR 0x0D
    then scan cs [] (finish word out) False
    else if c = CHR ''('' \<or> c = CHR '')'' then scan cs [] ([c] # finish word out) False
    else scan cs (c # word) out False)"

definition lex :: "string \<Rightarrow> string \<Rightarrow> string list \<Rightarrow> string list" where
  "lex s word out = scan s word out False"

fun digit :: "char \<Rightarrow> nat" where
  "digit c = (let n = nat_of_char c in
    if 48 \<le> n \<and> n < 58 then n - 48 else
    if 65 \<le> n \<and> n < 71 then n - 55 else
    if 97 \<le> n \<and> n < 103 then n - 87 else 16)"

definition parse_digits :: "nat \<Rightarrow> string \<Rightarrow> nat option" where
  "parse_digits base s = (if s = [] \<or> \<not> list_all (\<lambda>c. digit c < base) s
    then None else let n = foldl (\<lambda>n c. min (2 ^ 64) (base * n + digit c)) 0 s in
    if n < 2 ^ 64 then Some n else None)"

definition number :: "string \<Rightarrow> nat option" where
  "number s = (case s of a # b # rest \<Rightarrow>
    if a = CHR ''0'' \<and> (b = CHR ''x'' \<or> b = CHR ''X'') then parse_digits 16 rest
    else parse_digits 10 s | _ \<Rightarrow> parse_digits 10 s)"

lemma parse_digits_bound: "parse_digits base s = Some n \<Longrightarrow> n < 2 ^ 64"
  by (auto simp only: parse_digits_def Let_def option.inject option.distinct split: if_splits)

theorem number_bound: "number s = Some n \<Longrightarrow> n < 2 ^ 64"
  using parse_digits_bound by (auto simp: number_def split: list.splits if_splits)

definition valid_name :: "string \<Rightarrow> bool" where
  "valid_name s = (case s of [] \<Rightarrow> False | c # cs \<Rightarrow>
    97 \<le> nat_of_char c \<and> nat_of_char c \<le> 122 \<and>
    list_all (\<lambda>d. (97 \<le> nat_of_char d \<and> nat_of_char d \<le> 122) \<or>
      (48 \<le> nat_of_char d \<and> nat_of_char d < 58)) cs \<and> s \<noteq> ''let'' \<and> s \<noteq> ''if'')"

fun lookup :: "string \<Rightarrow> string list \<Rightarrow> nat option" where
  "lookup name [] = None"
| "lookup name (x # xs) = (if name = x then Some 0 else map_option Suc (lookup name xs))"

lemma lookup_bound: "lookup name names = Some i \<Longrightarrow> i < length names"
  by (induction names arbitrary: i) (auto split: if_splits option.splits)

fun operator :: "string \<Rightarrow> operator option" where
  "operator s = (if s = ''+'' then Some Add else if s = ''-'' then Some Sub else if s = ''*'' then Some Mul
    else if s = ''and'' then Some And else if s = ''or'' then Some Or else if s = ''xor'' then Some Xor
    else if s = ''shl'' then Some Shl else if s = ''shr'' then Some Shr else if s = ''<'' then Some Less else None)"

definition atom :: "string list \<Rightarrow> string \<Rightarrow> expression option" where
  "atom names s = (case lookup s names of Some i \<Rightarrow> Some (Variable i) | None \<Rightarrow>
    if s = ''x'' then Some (Input X) else if s = ''y'' then Some (Input Y) else if s = ''t'' then Some (Input T)
    else map_option (Literal \<circ> word_of_nat) (number s))"

lemma atom_scoped: "atom names s = Some e \<Longrightarrow> scoped (length names) e"
  by (auto simp: atom_def split: option.splits if_splits dest: lookup_bound)

fun close :: "expression \<Rightarrow> string list \<Rightarrow> (expression \<times> string list) option" where
  "close e (s # rest) = (if s = '')'' then Some (e,rest) else None)"
| "close e [] = None"

lemma close_expression: "close e tokens = Some (a,rest) \<Longrightarrow> a = e"
  by (cases tokens) (auto split: if_splits)

function parse :: "nat \<Rightarrow> string list \<Rightarrow> string list \<Rightarrow> (expression \<times> string list) option" where
  "parse fuel names tokens = (if fuel = 0 then None else case tokens of [] \<Rightarrow> None | s # rest \<Rightarrow>
    if s \<noteq> ''('' then map_option (\<lambda>e. (e,rest)) (atom names s)
    else case rest of [] \<Rightarrow> None | op # args \<Rightarrow>
      if op = ''let'' then (case args of [] \<Rightarrow> None | name # body \<Rightarrow>
        if \<not> valid_name name then None else
        Option.bind (parse (fuel - 1) names body) (\<lambda>(a,tail).
        Option.bind (parse (fuel - 1) (name # names) tail) (\<lambda>(b,tail). close (Let a b) tail)))
      else if op = ''if'' then
        Option.bind (parse (fuel - 1) names args) (\<lambda>(c,tail).
        Option.bind (parse (fuel - 1) names tail) (\<lambda>(a,tail).
        Option.bind (parse (fuel - 1) names tail) (\<lambda>(b,tail). close (Cond c a b) tail)))
      else Option.bind (operator op) (\<lambda>f.
        Option.bind (parse (fuel - 1) names args) (\<lambda>(a,tail).
        Option.bind (parse (fuel - 1) names tail) (\<lambda>(b,tail). close (Binary f a b) tail))))"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(fuel,names,tokens). fuel)") auto

declare parse.simps [simp del]

theorem parse_scoped:
  "parse fuel names tokens = Some (e,rest) \<Longrightarrow> scoped (length names) e"
proof (induction fuel arbitrary: names tokens e rest)
  case 0
  then show ?case by (subst (asm) parse.simps) auto
next
  case (Suc fuel)
  from Suc.prems show ?case
    by (subst (asm) parse.simps)
      (auto simp del: operator.simps dest: atom_scoped split: list.splits if_splits bind_splits option.splits prod.splits;
        drule close_expression; auto dest: Suc.IH)
qed

record limits =
  depth_budget :: nat
  node_budget :: nat
  stack_budget :: nat

definition defaults :: limits where
  "defaults = \<lparr>depth_budget = 128, node_budget = 4096, stack_budget = 512\<rparr>"

definition valid_limits :: "limits \<Rightarrow> bool" where
  "valid_limits lim = (depth_budget lim \<le> 128 \<and> node_budget lim \<le> 4096 \<and> stack_budget lim \<le> 512)"

definition prepare_with :: "limits \<Rightarrow> string \<Rightarrow> expression option" where
  "prepare_with lim s = (if \<not> valid_limits lim \<or> \<not> list_all (\<lambda>c. nat_of_char c < 128) s then None else
    Option.bind (parse (depth_budget lim) [] (lex s [] [])) (\<lambda>(e,rest).
      if rest = [] \<and> nodes e \<le> node_budget lim then
        let code = compile (optimise e) [] in
        if check code 0 = Some 1 \<and> demand (optimise e) \<le> stack_budget lim \<and> list_all encodable (native code)
        then Some e else None else None))"

definition prepare :: "string \<Rightarrow> expression option" where
  "prepare = prepare_with defaults"

lemma prepare_with_scoped: "prepare_with lim s = Some e \<Longrightarrow> scoped 0 e"
  by (auto simp: prepare_with_def Let_def dest: parse_scoped split: if_splits bind_splits prod.splits)

lemma prepare_with_bounded:
  "prepare_with lim s = Some e \<Longrightarrow> bounded (stack_budget lim) (compile (optimise e) []) 0"
  by (auto simp: prepare_with_def Let_def closed_demand optimise_scoped dest: parse_scoped split: if_splits bind_splits prod.splits)

lemma prepare_scoped: "prepare s = Some e \<Longrightarrow> scoped 0 e"
  unfolding prepare_def using prepare_with_scoped by blast

lemma prepare_bounded:
  "prepare s = Some e \<Longrightarrow> bounded 512 (compile (optimise e) []) 0"
  using prepare_with_bounded[where lim=defaults] by (simp add: prepare_def defaults_def)

lemma prepare_encodable:
  "prepare s = Some e \<Longrightarrow> list_all encodable (native (compile (optimise e) []))"
  by (auto simp: prepare_def prepare_with_def Let_def split: if_splits bind_splits prod.splits)

lemma prepare_program:
  "prepare s = Some e \<Longrightarrow> list_all encodable (program e)"
  unfolding program_def using prepare_encodable
  by (auto intro: transfers_property)

theorem prepared_correct:
  "prepare source = Some e \<Longrightarrow>
    execute values (compile (optimise e) []) [] = Some [evaluate e [] values]"
  using compile_closed prepare_scoped by blast

theorem prepared_native:
  "prepare source = Some e \<Longrightarrow>
    map_option observe (run (native (compile (optimise e) [])) s) =
    Some (inputs s, evaluate e [] (inputs s) # stack s)"
  using native_expression prepare_scoped by blast

theorem prepared_bytes:
  "prepare source = Some e \<Longrightarrow>
    recover (length (program e)) (executable e) =
    Some (program e, [195])"
  unfolding executable_def using recover_encode prepare_program by blast

theorem prepared_stacks:
  "prepare source = Some e \<Longrightarrow>
    \<exists>frames. snapshots values (compile (optimise e) []) [] = Some frames \<and>
      list_all (\<lambda>s. length s \<le> 512) frames"
  using bounded_execution[where s="[]" and limit=512] prepare_bounded by auto

function decimal :: "nat \<Rightarrow> string" where
  "decimal n = (if n < 10 then [char_of_nat (48+n)] else decimal (n div 10) @ [char_of_nat (48+n mod 10)])"
  by pat_completeness auto
termination by (relation "measure id") (auto simp: div_less_dividend)

definition newline :: string where "newline = [CHR 0x0A]"

fun regname :: "register \<Rightarrow> string" where
  "regname Rax = ''rax''" | "regname Rcx = ''rcx''" | "regname Rbx = ''rbx''"
| "regname Rdx = ''rdx''" | "regname R8 = ''r8''" | "regname R9 = ''r9''"

fun opname :: "operator \<Rightarrow> string" where
  "opname Add = ''add''" | "opname Sub = ''sub''" | "opname Mul = ''mul''"
| "opname And = ''and''" | "opname Or = ''or''" | "opname Xor = ''xor''"
| "opname Shl = ''shl''" | "opname Shr = ''shr''" | "opname Less = ''less''"

fun mnemonic :: "opcode \<Rightarrow> string" where
  "mnemonic (Immediate v) = ''immediate rax '' @ decimal (unat v)"
| "mnemonic (Push r) = ''push '' @ regname r"
| "mnemonic (Pop r) = ''pop '' @ regname r"
| "mnemonic (Move dst src) = ''mov '' @ regname dst @ '' '' @ regname src"
| "mnemonic (Peek i) = ''peek rax stack['' @ decimal i @ '']''"
| "mnemonic (Arithmetic op) = ''arithmetic '' @ opname op"
| "mnemonic Conditional = ''conditional rax rcx rbx''"

fun listing :: "nat \<Rightarrow> (nat list \<times> opcode) list \<Rightarrow> string" where
  "listing offset [] = decimal offset @ ''  ret'' @ newline"
| "listing offset ((bytes,op) # code) = decimal offset @ ''  '' @ mnemonic op @
    ''  ['' @ concat (map (\<lambda>b. decimal b @ '' '') bytes) @ '']'' @ newline @
    listing (offset + length bytes) code"

fun linear_listing :: "nat \<Rightarrow> opcode list \<Rightarrow> string" where
  "linear_listing offset [] = []"
| "linear_listing offset (op # code) = decimal offset @ ''  '' @ mnemonic op @ newline @
    linear_listing (offset + length (encode op)) code"

fun flowlisting :: "nat \<Rightarrow> flow \<Rightarrow> string" where
  "flowlisting offset (Basic code) = linear_listing offset code"
| "flowlisting offset (Sequence a b) = flowlisting offset a @
    flowlisting (offset + length (flowbytes a)) b"
| "flowlisting offset (Choice a b) = decimal offset @ ''  test rax rax'' @ newline @
    decimal (offset + 3) @ ''  jz '' @ decimal (offset + 14 + length (flowbytes a)) @ newline @
    flowlisting (offset + 9) a @ decimal (offset + 9 + length (flowbytes a)) @ ''  jmp '' @
    decimal (offset + length (flowbytes (Choice a b))) @ newline @
    flowlisting (offset + 14 + length (flowbytes a)) b"

definition disassemble :: "string \<Rightarrow> bool \<times> string" where
  "disassemble bytes = (case blocks (map nat_of_char bytes) of
    None \<Rightarrow> (case inspect (map nat_of_char bytes) of
      None \<Rightarrow> (False,''invalid native block stream'' @ newline)
      | Some code \<Rightarrow> (True,flowlisting 0 code @ decimal (length (flowbytes code)) @ ''  ret'' @ newline))
    | Some code \<Rightarrow> (True,listing 0 code))"

definition validate :: "string \<Rightarrow> bool \<times> string" where
  "validate bytes = (case blocks (map nat_of_char bytes) of
    None \<Rightarrow> (case inspect (map nat_of_char bytes) of
      None \<Rightarrow> (False,''invalid native block stream'' @ newline)
      | Some code \<Rightarrow> (True,''native branch, stack and register effects verified'' @ newline))
    | Some code \<Rightarrow> if audit (map snd code) 0 = Some 0
      then (True,''native stack and register effects verified'' @ newline)
      else (False,''invalid native stack or register effects'' @ newline))"

datatype problem = Unexpected nat | Exhausted nat

datatype 'a outcome = Failed problem | Parsed 'a

fun parsed_bind :: "'a outcome \<Rightarrow> ('a \<Rightarrow> 'b outcome) \<Rightarrow> 'b outcome" where
  "parsed_bind (Failed p) f = Failed p"
| "parsed_bind (Parsed x) f = f x"

fun close_at :: "expression \<Rightarrow> string list \<Rightarrow> nat \<Rightarrow> (expression \<times> string list \<times> nat) outcome" where
  "close_at e [] pos = Failed (Unexpected pos)"
| "close_at e (s # rest) pos = (if s = '')'' then Parsed (e,rest,Suc pos) else Failed (Unexpected pos))"

lemma close_at_cursor:
  "close_at e tokens pos = Parsed (a,rest,nextpos) \<Longrightarrow> a = e \<and> nextpos = Suc pos"
  by (cases tokens) (auto split: if_splits)

function diagnose :: "nat \<Rightarrow> string list \<Rightarrow> string list \<Rightarrow> nat \<Rightarrow>
    (expression \<times> string list \<times> nat) outcome" where
  "diagnose fuel names tokens pos = (if fuel = 0 then Failed (Exhausted pos)
    else case tokens of [] \<Rightarrow> Failed (Unexpected pos) | s # rest \<Rightarrow>
    if s \<noteq> ''('' then (case atom names s of None \<Rightarrow> Failed (Unexpected pos)
      | Some e \<Rightarrow> Parsed (e,rest,Suc pos))
    else case rest of [] \<Rightarrow> Failed (Unexpected (Suc pos)) | op # args \<Rightarrow>
      if op = ''let'' then (case args of [] \<Rightarrow> Failed (Unexpected (pos + 2)) | name # body \<Rightarrow>
        if \<not> valid_name name then Failed (Unexpected (pos + 2)) else
        parsed_bind (diagnose (fuel - 1) names body (pos + 3)) (\<lambda>(a,tail,nextpos).
        parsed_bind (diagnose (fuel - 1) (name # names) tail nextpos) (\<lambda>(b,tail,lastpos).
          close_at (Let a b) tail lastpos)))
      else if op = ''if'' then
        parsed_bind (diagnose (fuel - 1) names args (pos + 2)) (\<lambda>(c,tail,nextpos).
        parsed_bind (diagnose (fuel - 1) names tail nextpos) (\<lambda>(a,tail,nextpos).
        parsed_bind (diagnose (fuel - 1) names tail nextpos) (\<lambda>(b,tail,lastpos).
          close_at (Cond c a b) tail lastpos)))
      else case operator op of None \<Rightarrow> Failed (Unexpected (Suc pos)) | Some f \<Rightarrow>
        parsed_bind (diagnose (fuel - 1) names args (pos + 2)) (\<lambda>(a,tail,nextpos).
        parsed_bind (diagnose (fuel - 1) names tail nextpos) (\<lambda>(b,tail,lastpos).
          close_at (Binary f a b) tail lastpos)))"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(fuel,names,tokens,pos). fuel)") auto

declare diagnose.simps [simp del]

definition source_error_with :: "limits \<Rightarrow> string \<Rightarrow> string" where
  "source_error_with lim s = (if \<not> valid_limits lim then ''limits exceed compiler bounds'' @ newline else if \<not> list_all (\<lambda>c. nat_of_char c < 128) s then ''source must contain ASCII'' @ newline else
    case diagnose (depth_budget lim) [] (lex s [] []) 0 of
    Failed (Unexpected pos) \<Rightarrow> ''syntax error at token '' @ decimal pos @ newline
    | Failed (Exhausted pos) \<Rightarrow> ''parse depth limit exceeded at token '' @ decimal pos @ newline
    | Parsed (e,rest,pos) \<Rightarrow> if rest \<noteq> [] then ''syntax error at token '' @ decimal pos @ newline
      else if nodes e > node_budget lim then ''program exceeds '' @ decimal (node_budget lim) @ '' nodes'' @ newline
      else if demand (optimise e) > stack_budget lim then ''evaluation stack exceeds '' @ decimal (stack_budget lim) @ '' words'' @ newline
      else ''native validation failed'' @ newline)"

definition artifact_with :: "limits \<Rightarrow> string \<Rightarrow> (bool \<times> string) \<times> string" where
  "artifact_with lim s = (case prepare_with lim s of None \<Rightarrow> ((False,[]), source_error_with lim s)
    | Some e \<Rightarrow> let opt = optimise e; code = branching e; bytes = flowbytes code @ [195] in
      if flowaudit code 0 = Some 0 \<and> flowvalid code then
        ((True, map char_of_nat bytes), decimal (nodes e) @ '' nodes -> '' @ decimal (nodes opt) @
          '' nodes, '' @ decimal (length bytes) @ '' bytes, '' @ decimal (demand opt) @ '' stack words'' @ newline)
      else ((False,[]),''allocated code exceeds native limits'' @ newline))"

definition source_error :: "string \<Rightarrow> string" where
  "source_error = source_error_with defaults"

definition artifact :: "string \<Rightarrow> (bool \<times> string) \<times> string" where
  "artifact = artifact_with defaults"

theorem artifact_execution:
  assumes "artifact source = ((True,bytes),report)"
  shows "\<exists>e d. prepare source = Some e \<and>
    bytes = map char_of_nat (flowbytes (branching e) @ [195]) \<and>
    executes64 (flowbytes (branching e)) c d \<and>
    registers (state64 d) Rax = evaluate e [] (inputs (state64 c)) \<and>
    stack (state64 d) = stack (state64 c) \<and> inputs (state64 d) = inputs (state64 c)"
proof -
  obtain e where e: "prepare source = Some e" "flowvalid (branching e)"
    "bytes = map char_of_nat (flowbytes (branching e) @ [195])"
    using assms by (auto simp: artifact_def artifact_with_def prepare_def Let_def split: option.splits if_splits)
  show ?thesis using compiled_execution[OF prepare_scoped[OF e(1)] e(2), of c] e by blast
qed

definition baseline :: "string \<Rightarrow> (bool \<times> string) \<times> string" where
  "baseline s = (case prepare s of None \<Rightarrow> ((False,[]),source_error s)
    | Some e \<Rightarrow> ((True,map char_of_nat (executable e)),''stack backend'' @ newline))"

definition configured :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> (bool \<times> string) \<times> string" where
  "configured depth count stacktext source = (case (number depth, number count, number stacktext) of
    (Some d,Some n,Some k) \<Rightarrow> artifact_with \<lparr>depth_budget=d, node_budget=n, stack_budget=k\<rparr> source
    | _ \<Rightarrow> ((False,[]),''invalid resource limits'' @ newline))"

definition boundary :: "nat list" where
  "boundary = [0,1,63,64,65,127,255,256,2 ^ 31,2 ^ 32,2 ^ 63,2 ^ 64 - 1]"

definition sample :: "nat \<Rightarrow> input \<Rightarrow> pixel" where
  "sample i = (\<lambda>v. word_of_nat (if i < 12 then boundary ! ((i + (case v of X \<Rightarrow> 0 | Y \<Rightarrow> 3 | T \<Rightarrow> 7)) mod 12)
    else case v of X \<Rightarrow> (17*i) mod 257 | Y \<Rightarrow> (29*i) mod 131 | T \<Rightarrow> 13*i))"

definition row :: "expression \<Rightarrow> nat \<Rightarrow> nat list" where
  "row e i = concat (map (\<lambda>v. octets 8 (unat v))
    [sample i X, sample i Y, sample i T, evaluate e [] (sample i)])"

definition vectors :: "string \<Rightarrow> bool \<times> string" where
  "vectors s = (case prepare s of None \<Rightarrow> (False, source_error s)
    | Some e \<Rightarrow> (True, map char_of_nat (concat (map (row e) [0..<512]))))"

definition reference :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool \<times> string" where
  "reference source x y t = (case prepare source of None \<Rightarrow> (False,source_error source) | Some e \<Rightarrow>
    case (number x, number y, number t) of (Some a,Some b,Some c) \<Rightarrow>
      (True, decimal (unat (evaluate e [] (\<lambda>v. word_of_nat (case v of X \<Rightarrow> a | Y \<Rightarrow> b | T \<Rightarrow> c)))) @ newline)
    | _ \<Rightarrow> (False,''invalid input'' @ newline))"

definition initial64 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> processor" where
  "initial64 x y t = \<lparr>state64 = \<lparr>registers = (\<lambda>r. word_of_nat
    (if r = R8 then x else if r = R9 then y else if r = Rdx then t else 0)), stack = [0]\<rparr>,
    pointer64 = 65536, zero64 = None, carry64 = None\<rparr>"

definition simulate :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool \<times> string" where
  "simulate code x y t = (if \<not> fst (validate code) then (False,''invalid native image'' @ newline) else
    case (number x,number y,number t) of (Some a,Some b,Some c) \<Rightarrow>
      (case simulate64 (Suc (length code)) (map nat_of_char code) (initial64 a b c) of
        None \<Rightarrow> (False,''unsupported or incomplete x86 execution'' @ newline)
        | Some q \<Rightarrow> if stack (state64 q) = []
          then (True,decimal (unat (registers (state64 q) Rax)) @ newline)
          else (False,''return frame was not consumed'' @ newline))
    | _ \<Rightarrow> (False,''invalid input'' @ newline))"

end
