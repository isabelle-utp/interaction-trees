section \<open> Circus Interaction Tree Semantics \<close>

theory ITree_Circus                          
  imports "ITree_FDSem" "Shallow-Expressions-Z.Shallow_Expressions_Z"
begin

unbundle Z_Relation_Syntax

subsection \<open> Main Operators \<close>

type_synonym ('e, 's) action = "('e, 's) htree"
type_synonym 'e process = "('e, unit) itree"

definition Skip :: "('e, 'r) htree" where
"Skip = (\<lambda> s. Ret s)"

expr_ctr subst_id

lemma straces_Skip: "traces\<^sub>s (Skip) = ({[], [\<checkmark> [\<leadsto>]]})\<^sub>e"
  by (simp add: Skip_def straces_def traces_Ret, expr_simp)

abbreviation Div :: "('e, 'r) htree" where
"Div \<equiv> (\<lambda> s. diverge)"

lemma traces_deadlock: "traces(deadlock) = {[]}"
  by (auto simp add: deadlock_def traces_Vis)

abbreviation 
"Stop \<equiv> (\<lambda> s. deadlock)"

definition "assume" :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree" where
"assume b = (\<lambda> s. if (b s) then Ret s else diverge)"

syntax "_assume" :: "logic \<Rightarrow> logic" ("\<questiondown>_?")
translations "_assume b" == "CONST assume (b)\<^sub>e"

lemma assume_true: "\<questiondown>True? = Skip"
  by (simp add: assume_def Skip_def)

lemma assert_false: "\<questiondown>False? = Div"
  by (simp add: assume_def)

definition test :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree" where
"test b = (\<lambda> s. if (b s) then Ret s else deadlock)"

abbreviation (input) "assert b \<equiv> test b"

syntax "_test" :: "logic \<Rightarrow> logic" ("\<exclamdown>_!")
translations "_test b" == "CONST test (b)\<^sub>e"

lemma test_true: "\<exclamdown>True! = Skip"
  by (simp add: test_def Skip_def)

lemma test_false: "\<exclamdown>False! = Stop"
  by (simp add: test_def)

definition cond_itree :: "('e, 's) htree \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
"cond_itree P b Q = (\<lambda> s. if b s then P s else Q s)"

text \<open> Similar to @{const Let} in HOL, but it evaluates the assigned expression on the initial state. \<close>

definition let_itree :: "('i, 's) expr \<Rightarrow> ('i \<Rightarrow> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
"let_itree e S = (\<lambda> s. S (e s) s)"

definition for_itree :: "'i list \<Rightarrow> ('i \<Rightarrow> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
"for_itree I P = (\<lambda> s. (foldr (\<lambda> i Q. P i \<Zcomp> Q) I Skip) s)"

syntax 
  "_cond_itree"  :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("if _ then _ else _ fi")
  "_cond_itree1" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("if _ then _ fi")
  "_while_itree" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("while _ do _ od")
  "_let_itree" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(let _ \<leftarrow> (_) in (_))" [0, 0, 10] 10)
  "_for_itree"   :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("for _ in _ do _ od")

translations
  "_cond_itree b P Q" == "CONST cond_itree P (b)\<^sub>e Q"
  "_cond_itree1 b P " == "CONST cond_itree P (b)\<^sub>e (CONST Skip)"
  "_while_itree b P" == "CONST iterate (b)\<^sub>e P"
  "_let_itree x e S" == "CONST let_itree (e)\<^sub>e (\<lambda> x. S)"
  "_for_itree i I P" == "CONST for_itree I (\<lambda> i. P)"

definition assigns :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('s\<^sub>1 \<Rightarrow> ('e, 's\<^sub>2) itree)" ("\<langle>_\<rangle>\<^sub>a") where
"assigns \<sigma> = (\<lambda> s. Ret (\<sigma> s))"

lemma assigns_id: "\<langle>id\<rangle>\<^sub>a = Skip"
  by (simp add: assigns_def Skip_def)

lemma assigns_seq: "\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> (P \<Zcomp> Q) = (\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> P) \<Zcomp> Q"
  by (simp add: kleisli_comp_def assigns_def)

lemma assigns_seq_comp: "\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>a"
  by (simp add: kleisli_comp_def assigns_def subst_comp_def)

lemma assigns_test: "\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> \<exclamdown>b! = \<exclamdown>\<sigma> \<dagger> b! \<Zcomp> \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: kleisli_comp_def assigns_def test_def fun_eq_iff expr_defs)

lemma assigns_assume: "\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> \<questiondown>b? = \<questiondown>\<sigma> \<dagger> b? \<Zcomp> \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: kleisli_comp_def assigns_def assume_def fun_eq_iff expr_defs)

lemma for_empty: "for x in [] do P x od = Skip"
  by (simp add: for_itree_def)

text \<open> Hide the state of an action to produce a process \<close>

definition process :: "'s::default subst \<Rightarrow> ('e, 's, 'a) ktree \<Rightarrow> 'e process" where
"process I A = (\<langle>(\<lambda> _. default)\<rangle>\<^sub>a \<Zcomp> \<langle>I\<rangle>\<^sub>a \<Zcomp> A \<Zcomp> assigns (\<lambda> s. ())) ()"

abbreviation "abs_st P \<equiv> P \<Zcomp> assigns (\<lambda> s. ())"

syntax
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=" 61)

translations
  "_assignment x e" == "CONST assigns (CONST subst_upd (CONST subst_id) x (e)\<^sub>e)"
  "_assignment (_svid_tuple (_of_svid_list (x +\<^sub>L y))) e" <= "_assignment (x +\<^sub>L y) e"

lemma traces_inp: "wb_prism c \<Longrightarrow> traces (inp c) = {[]} \<union> {[Ev (build\<^bsub>c\<^esub> v)] | v. True} \<union> {[Ev (build\<^bsub>c\<^esub> v), \<checkmark> v] | v. True}" 
  apply (simp add: inp_in_where_def traces_Vis traces_Ret)
  apply (auto simp add: inp_in_where_def bind_eq_Some_conv traces_Ret domIff pdom.abs_eq  elim!: in_tracesE trace_to_VisE)
  done 

definition input_in_where :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('s \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> (('s \<Rightarrow> bool) \<times> ('e, 's) htree)) \<Rightarrow> ('e, 's) htree" where
"input_in_where c A P = (\<lambda>s. inp_in_where c (A s) (\<lambda> v. fst (P v) s) \<bind> (\<lambda>x. snd (P x) s))"

definition input_list_where :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('s \<Rightarrow> 'a list) \<Rightarrow> ('a \<Rightarrow> ('s \<Rightarrow> bool) \<times> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
"input_list_where c A P = (\<lambda>s. inp_list_where c (A s) (\<lambda> v. fst (P v) s) \<bind> (\<lambda>x. snd (P x) s))"

definition input_map_in_where :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> _ \<Rightarrow> ('a \<Rightarrow> ('s \<Rightarrow> bool) \<times> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
"input_map_in_where c A P = (\<lambda>s. inp_map_in_where c (A s) (\<lambda> v. fst (P v) s) \<bind> (\<lambda>x. snd (P x) s))"

abbreviation "input c P \<equiv> input_in_where c (UNIV)\<^sub>e (\<lambda> e. ((True)\<^sub>e, P e))"

(*
definition input :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
"input c P = (\<lambda> s. inp c \<bind> (\<lambda> x. P x s))"
*)

abbreviation input_in :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('s \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
"input_in c A P \<equiv> input_in_where c A (\<lambda> e. ((True)\<^sub>e, P e))"

lemma input_in_where_map_code:
  "wb_prism c \<Longrightarrow> input_in_where c A P = input_map_in_where c A P"
  by (simp add: input_in_where_def inp_in_where_map_code input_map_in_where_def)

lemma input_in_where_enum [code_unfold]: "wb_prism c \<Longrightarrow> input_in_where c (UNIV)\<^sub>e P = input_list_where c (enum_class.enum)\<^sub>e P"
  by (simp add: input_in_where_def input_list_where_def inp_in_where_list_code inp_where_enum)

abbreviation input_where :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('s \<Rightarrow> bool) \<times> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
"input_where c P \<equiv> input_in_where c (UNIV)\<^sub>e P"

(*
definition "input' c P = (\<lambda>s. inp' c \<bind> (\<lambda>x. P x s))"

lemma input_code_unfold [code_unfold]: 
  "wb_prism c \<Longrightarrow> input c P = input' c P"
  using inp_in_coset by (fastforce simp add: input_def input'_def inp_in_coset inp'_def)

term inp_list

lemma "wb_prism c \<Longrightarrow> input_where c P = (\<lambda>s. inp_list_where c enum_class.enum (\<lambda> v. fst (P v) s) \<bind> (\<lambda>x. snd (P x) s))"
*)

bundle Circus_Syntax
begin

unbundle Expression_Syntax

no_notation disj (infixr "|" 30)
no_notation conj (infixr "&" 35)

end

unbundle Circus_Syntax

syntax 
  "_input"          :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("_?_ \<rightarrow> _" [60, 0, 61] 61)
  "_input_in_where" :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_?_:_/ |/ _ \<rightarrow> _" [60, 0, 0, 0, 61] 61)
  "_input_in"       :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_?_:_ \<rightarrow> _" [60, 0, 0, 61] 61)
  "_input_where"    :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_?_/ |/ _ \<rightarrow> _" [60, 0, 0, 61] 61)

translations "c?(x) \<rightarrow> P" == "CONST input c (\<lambda> (x). P)"
translations "c?(x):A|B \<rightarrow> P" == "CONST input_in_where c (A)\<^sub>e (\<lambda> x. ((B)\<^sub>e, P))"
translations "c?(x):A \<rightarrow> P" == "CONST input_in c (A)\<^sub>e (\<lambda> (x). P)"
translations "c?(x)|P \<rightarrow> Q" == "CONST input_where c (\<lambda> (x). ((P)\<^sub>e, Q))"

lemma assigns_input: "\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> c?(x) \<rightarrow> P(x) = c?(x) \<rightarrow> (\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> P(x))"
  by (simp add: input_in_where_def kleisli_comp_def assigns_def)

definition "output" :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('s \<Rightarrow> 'a) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
"output c e P = (\<lambda> s. outp c (e s) \<then> P s)"

syntax "_output" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_!'(_') \<rightarrow> _" [90, 0, 91] 91)
translations "c!(e) \<rightarrow> P" == "CONST output c (e)\<^sub>e P"

lemma assigns_output: "\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> c!(e) \<rightarrow> P = c!(\<sigma> \<dagger> e) \<rightarrow> (\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> P)"
  by (simp add: assigns_def kleisli_comp_def output_def expr_defs)

lemma trace_of_deadlock: "deadlock \<midarrow>t\<leadsto> P \<Longrightarrow> (t, P) = ([], deadlock)"
  by (auto simp add: deadlock_def)

instantiation "fun" :: (type, extchoice) extchoice
begin

definition extchoice_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
"extchoice_fun P Q \<equiv> (\<lambda> s. extchoice (P s) (Q s))"

instance ..

end

lemma extchoice_Stop: "Stop \<box> P = P"
  by (auto simp add: extchoice_fun_def fun_eq_iff)

lemma extchoice_Div: "Div \<box> P = Div"
  by (simp add: choice_diverge extchoice_fun_def)

lemma assigns_extchoice: "\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> (P \<box> Q) = (\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> P) \<box> (\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> Q)"
  by (simp add: kleisli_comp_def extchoice_fun_def expr_defs assigns_def)

no_notation conj  (infixr "&" 35)

syntax
  "_cguard" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ & _" [50, 51] 50)

translations
  "_cguard b P" == "(CONST test (b)\<^sub>e) \<Zcomp> P"

definition frame :: "'s scene \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
"frame a P = (\<lambda> s. P s \<bind> (\<lambda> s'. Ret (s' \<oplus>\<^sub>S s on a)))"

definition frame_ext :: "('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('e, 's\<^sub>1) htree \<Rightarrow> ('e, 's\<^sub>2) htree" where
"frame_ext a P = (\<lambda> s. P (get\<^bsub>a\<^esub> s) \<bind> (\<lambda> v. Ret (put\<^bsub>a\<^esub> s v)))"

definition promote :: "('e, 's\<^sub>1) htree \<Rightarrow> ('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('e, 's\<^sub>2) htree" where
[code_unfold]: "promote P a = \<exclamdown>\<^bold>D(a)! \<Zcomp> frame_ext a P"

syntax "_promote" :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infix "\<Up>\<Up>" 60)
translations "_promote P a" == "CONST promote P a"

end