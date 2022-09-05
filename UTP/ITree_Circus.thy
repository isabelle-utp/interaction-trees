section \<open> Circus Interaction Tree Semantics \<close>

theory ITree_Circus                          
  imports "ITree_FDSem" "Shallow-Expressions-Z.Shallow_Expressions_Z"
begin

subsection \<open> Main Operators \<close>

type_synonym ('e, 's) action = "('e, 's) htree"
type_synonym 'e process = "('e, unit) itree"

definition Skip :: "('e, 'r) htree" where
"Skip = (\<lambda> s. Ret s)"

lemma Skip_unit [simp]: 
  "Skip ;; S = S" "S ;; Skip = S"
  by (simp_all add: seq_itree_def Skip_def kleisli_comp_def bind_itree_right_unit)

text \<open> Like @{const Skip}, but do a single silent step. \<close>

definition Step :: "('e, 'r) htree" where
"Step = \<tau> \<circ> Skip"

lemma straces_Skip: "traces\<^sub>s (Skip) = ({[], [\<checkmark> [\<leadsto>]]})\<^sub>e"
  by (simp add: Skip_def straces_def traces_Ret, expr_simp)

abbreviation Div :: "('e, 'r) htree" where
"Div \<equiv> (\<lambda> s. diverge)"

lemma Div_left_zero [simp]: "Div ;; P = Div"
  by (simp add: seq_itree_def kleisli_comp_def)

lemma traces_deadlock: "traces(deadlock) = {[]}"
  by (auto simp add: deadlock_def traces_Vis)

abbreviation 
"Stop \<equiv> (\<lambda> s. deadlock)"

lemma Stop_left_zero [simp]: "Stop ;; S = Stop"
  by (simp add: seq_itree_def kleisli_comp_def)

definition "assume" :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree" where
"assume b = (\<lambda> s. if (b s) then Ret s else diverge)"

syntax "_assume" :: "logic \<Rightarrow> logic" ("\<questiondown>_?")
translations "_assume b" == "CONST assume (b)\<^sub>e"

lemma assume_true: "\<questiondown>True? = Skip"
  by (simp add: assume_def Skip_def)

lemma assume_false: "\<questiondown>False? = Div"
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
"for_itree I P = (\<lambda> s. (foldr (\<lambda> i Q. P i ;; Q) I Skip) s)"

syntax 
  "_cond_itree"  :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("if _ then _ else _ fi")
  "_cond_itree1" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("if _ then _ fi")
  "_cond_itree_infix"  :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<lhd> _ \<rhd>/ _)" [52,0,53] 52)
  "_while_itree" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("while _ do _ od")
  "_let_itree" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(let _ \<leftarrow> (_) in (_))" [0, 0, 10] 10)
  "_for_itree"   :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("for _ in _ do _ od")

translations
  "_cond_itree b P Q" == "CONST cond_itree P (b)\<^sub>e Q"
  "_cond_itree1 b P " == "CONST cond_itree P (b)\<^sub>e (CONST Skip)"
  "_cond_itree_infix P b Q" => "_cond_itree b P Q"
  "_while_itree b P" == "CONST iterate (b)\<^sub>e P"
  "_let_itree x e S" == "CONST let_itree (e)\<^sub>e (\<lambda> x. S)"
  "_for_itree i I P" == "CONST for_itree I (\<lambda> i. P)"

definition assigns :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('s\<^sub>1 \<Rightarrow> ('e, 's\<^sub>2) itree)" ("\<langle>_\<rangle>\<^sub>a") where
"assigns \<sigma> = (\<lambda> s. Ret (\<sigma> s))"

syntax
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=" 61)
  "_swap" :: "svid \<Rightarrow> svid \<Rightarrow> logic" ("swap'(_, _')")

translations
  "_assignment x e" == "CONST assigns (CONST subst_upd (CONST subst_id) x (e)\<^sub>e)"
  "_assignment (_svid_tuple (_of_svid_list (x +\<^sub>L y))) e" <= "_assignment (x +\<^sub>L y) e"
  "_swap x y" => "(x, y) := ($y, $x)"

named_theorems assigns_combine

lemma assigns_id: "\<langle>id\<rangle>\<^sub>a = Skip"
  by (simp add: assigns_def Skip_def)

lemma assigns_empty: "\<langle>[\<leadsto>]\<rangle>\<^sub>a = Skip"
  by (simp add: subst_id_def assigns_def Skip_def)

lemma assigns_seq: "\<langle>\<sigma>\<rangle>\<^sub>a ;; (P ;; Q) = (\<langle>\<sigma>\<rangle>\<^sub>a ;; P) ;; Q"
  by (simp add: seq_itree_def kleisli_comp_def assigns_def)

lemma assigns_seq_comp [assigns_combine]: "\<langle>\<sigma>\<rangle>\<^sub>a ;; \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>a"
  by (simp add: seq_itree_def kleisli_comp_def assigns_def subst_comp_def)

lemma assigns_test: "\<langle>\<sigma>\<rangle>\<^sub>a ;; \<exclamdown>b! = \<exclamdown>\<sigma> \<dagger> b! ;; \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: seq_itree_def kleisli_comp_def assigns_def test_def fun_eq_iff expr_defs)

lemma assigns_assume: "\<langle>\<sigma>\<rangle>\<^sub>a ;; \<questiondown>b? = \<questiondown>\<sigma> \<dagger> b? ;; \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: seq_itree_def kleisli_comp_def assigns_def assume_def fun_eq_iff expr_defs)

lemma assigns_Stop: "\<langle>\<sigma>\<rangle>\<^sub>a ;; Stop = Stop"
  by (simp add: seq_itree_def assigns_def kleisli_comp_def)

lemma assign_Stop: "x := e ;; Stop = Stop"
  by (fact assigns_Stop)

lemma assigns_Step: "\<langle>\<sigma>\<rangle>\<^sub>a ;; Step = Step ;; \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: seq_itree_def assigns_def Step_def kleisli_comp_def Skip_def)

lemma assign_self: "vwb_lens x \<Longrightarrow> x := $x = Skip"
  by (simp add: usubst assigns_empty)

lemma assign_twice: "vwb_lens x \<Longrightarrow> (x := e;; x := f) = x := f\<lbrakk>e/x\<rbrakk>"
  by (simp add: assigns_combine usubst)

lemma assign_combine: 
  assumes "vwb_lens x" "vwb_lens y" "x \<bowtie> y"
  shows "x := e ;; y := f = (x, y) := (e, f\<lbrakk>e/x\<rbrakk>)"
  using assms by (simp add: seq_itree_def kleisli_comp_def assigns_def fun_eq_iff expr_defs lens_defs lens_indep_comm)

lemma swap_self: "vwb_lens x \<Longrightarrow> swap(x, x) = Skip"
  by (simp add: usubst assigns_empty)

lemma swap_commute: "x \<bowtie> y \<Longrightarrow> swap(x, y) = swap(y, x)"
  by (simp add: usubst usubst_upd_comm)

lemma cond_assigns [assigns_combine]: "(cond_itree \<langle>\<sigma>\<rangle>\<^sub>a b \<langle>\<rho>\<rangle>\<^sub>a) = \<langle>expr_if \<sigma> b \<rho>\<rangle>\<^sub>a"
  by (auto simp add: assigns_def cond_itree_def fun_eq_iff expr_defs Skip_def)

lemma cond1_assigns [assigns_combine]: "(cond_itree \<langle>\<sigma>\<rangle>\<^sub>a b Skip) = \<langle>expr_if \<sigma> b [\<leadsto>]\<rangle>\<^sub>a"
  by (auto simp add: assigns_def cond_itree_def fun_eq_iff expr_defs Skip_def)

lemma assign_cond: "if b then x := e else x := f fi = x := (if b then e else f)"
  by (simp add: assigns_combine usubst, simp add: expr_if_def)

lemma cond_simps:
  "S \<lhd> True \<rhd> T = S"
  "S \<lhd> False \<rhd> T = T"
  "S \<lhd> \<not> b \<rhd> T = T \<lhd> b \<rhd> S"
  "S \<lhd> b \<rhd> (T \<lhd> b \<rhd> U) = S \<lhd> b \<rhd> U"
  "(S \<lhd> b \<rhd> T) ;; U = (S ;; U) \<lhd> b \<rhd> (T ;; U)"
  "x := e ;; (S \<lhd> b \<rhd> T) = (x := e ;; S) \<lhd> b\<lbrakk>e/x\<rbrakk> \<rhd> (x := e ;; T)"
   by (simp_all add: seq_itree_def cond_itree_def fun_eq_iff kleisli_comp_def assigns_def expr_defs)

lemma for_empty: "for x in [] do P x od = Skip"
  by (simp add: for_itree_def)

lemma for_Cons: "for_itree (x # xs) P = P x ;; for_itree xs P"
  by (simp add: for_itree_def)

lemma while_unfold: "while b do S od = (S ;; Step ;; while b do S od) \<lhd> b \<rhd> Skip"
  by (auto simp add: seq_itree_def fun_eq_iff iterate.code kleisli_comp_def cond_itree_def Step_def Skip_def comp_def)

lemma while_True_Skip: "while True do Skip od = Div"
  by (simp add: Skip_def SEXP_def loop_Ret)

text \<open> Hide the state of an action to produce a process \<close>

definition process :: "'s::default subst \<Rightarrow> ('e, 's, 'a) ktree \<Rightarrow> 'e process" where
"process I A = (\<langle>(\<lambda> _. default)\<rangle>\<^sub>a ;; \<langle>I\<rangle>\<^sub>a ;; A ;; assigns (\<lambda> s. ())) ()"

lemma deadlock_free_processI: "(\<And> s. deadlock_free ((\<langle>\<sigma>\<rangle>\<^sub>a ;; P) s)) \<Longrightarrow> deadlock_free (process \<sigma> P)"
  by (simp add: process_def seq_itree_def kleisli_comp_def deadlock_free_bind_iff assigns_def deadlock_free_Ret)

abbreviation "abs_st P \<equiv> P ;; assigns (\<lambda> s. ())"

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

lemma assigns_input: "\<langle>\<sigma>\<rangle>\<^sub>a ;; c?(x) \<rightarrow> P(x) = c?(x) \<rightarrow> (\<langle>\<sigma>\<rangle>\<^sub>a ;; P(x))"
  by (simp add: seq_itree_def input_in_where_def kleisli_comp_def assigns_def)

definition "output" :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('s \<Rightarrow> 'a) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
"output c e P = (\<lambda> s. outp c (e s) \<then> P s)"

syntax "_output" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_!'(_') \<rightarrow> _" [90, 0, 91] 91)
translations "c!(e) \<rightarrow> P" == "CONST output c (e)\<^sub>e P"

lemma assigns_output: "\<langle>\<sigma>\<rangle>\<^sub>a ;; c!(e) \<rightarrow> P = c!(\<sigma> \<dagger> e) \<rightarrow> (\<langle>\<sigma>\<rangle>\<^sub>a ;; P)"
  by (simp add: seq_itree_def assigns_def kleisli_comp_def output_def expr_defs)

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

lemma assigns_extchoice: "\<langle>\<sigma>\<rangle>\<^sub>a ;; (P \<box> Q) = (\<langle>\<sigma>\<rangle>\<^sub>a ;; P) \<box> (\<langle>\<sigma>\<rangle>\<^sub>a ;; Q)"
  by (simp add: seq_itree_def kleisli_comp_def extchoice_fun_def expr_defs assigns_def)

no_notation conj  (infixr "&" 35)

syntax
  "_cguard" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ & _" [50, 51] 50)

translations
  "_cguard b P" == "(CONST test (b)\<^sub>e) ;; P"

definition frame :: "'s scene \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
"frame a P = (\<lambda> s. P s \<bind> (\<lambda> s'. Ret (s' \<oplus>\<^sub>S s on a)))"

definition frame_ext :: "('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('e, 's\<^sub>1) htree \<Rightarrow> ('e, 's\<^sub>2) htree" where
"frame_ext a P = (\<lambda> s. P (get\<^bsub>a\<^esub> s) \<bind> (\<lambda> v. Ret (put\<^bsub>a\<^esub> s v)))"

definition promote :: "('e, 's\<^sub>1) htree \<Rightarrow> ('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('e, 's\<^sub>2) htree" where
[code_unfold]: "promote P a = \<exclamdown>\<^bold>D(a)! ;; frame_ext a P"

syntax "_promote" :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infix "\<Up>\<Up>" 60)
translations "_promote P a" == "CONST promote P a"

named_theorems prog_defs

subsection \<open> Event Choice Blocks \<close>

definition event_fun_empty :: "('s \<Rightarrow> 'e \<Zpfun> ('e, 's) itree)" ("{}\<^sub>E") where
"event_fun_empty = (\<lambda> s. {\<mapsto>})"

definition event_fun_upd :: "('s \<Rightarrow> 'e \<Zpfun> ('e, 's) itree) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('s \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> ('s \<Rightarrow> \<bool>) \<times> ('s \<Rightarrow> ('e, 's) itree)) \<Rightarrow> 's \<Rightarrow> 'e \<Zpfun> ('e, 's) itree" where
"event_fun_upd F c A PB = (\<lambda> s. (F s)(c{v \<in> A s. fst (PB v) s} \<Rightarrow> snd (PB v) s))"

syntax
  "_event_fun_upd" :: "logic \<Rightarrow> prism_maplets \<Rightarrow> logic" ("_'(_')\<^sub>E" [900, 0] 900)
  "_event_fun" :: "prism_maplets \<Rightarrow> logic" ("{_}\<^sub>E")

translations
  "f(c{v \<in> A. P} \<Rightarrow> B)\<^sub>E" == "CONST event_fun_upd f c (A)\<^sub>e (\<lambda> v. ((P)\<^sub>e, B))"
  "_event_fun_upd m (_prism_Maplets xy ms)"  \<rightleftharpoons> "_event_fun_upd (_event_fun_upd m xy) ms"
  "_event_fun ms"                            \<rightleftharpoons> "_event_fun_upd {}\<^sub>E ms"
  "_event_fun (_prism_Maplets ms1 ms2)"     \<leftharpoondown> "_event_fun_upd (_event_fun ms1) ms2"

definition "event_choice F = (\<lambda> s. Vis (F s))"

definition event_block :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('s \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> ('s \<Rightarrow> \<bool>) \<times> ('s \<Rightarrow> 's)) \<Rightarrow> ('e, 's) htree" where
"event_block c A PB = (\<lambda> s. Vis (prism_fun c (A s) (\<lambda> c. (fst (PB c) s, Ret (snd (PB c) s)))))"

lemma prism_diff_implies_indep_funs: 
  "\<lbrakk> wb_prism c; wb_prism d; c \<nabla> d \<rbrakk> \<Longrightarrow> pdom(prism_fun c A P\<sigma>) \<inter> pdom(prism_fun d B Q\<rho>) = {}"
  by (auto simp add: dom_prism_fun prism_diff_build)

lemma case_sum_prod_dist: "case_sum (\<lambda> x. (f\<^sub>1 x, f\<^sub>2 x)) (\<lambda> x. (g\<^sub>1 x, g\<^sub>2 x)) = (\<lambda> x. (case_sum f\<^sub>1 g\<^sub>1 x, case_sum f\<^sub>2 g\<^sub>2 x))"
  by (simp add: fun_eq_iff sum.case_eq_if)

lemma case_sum_dist: "(case a of Inl x \<Rightarrow> op (f x) | Inr y \<Rightarrow> op (g y)) = op (case a of Inl x \<Rightarrow> f x | Inr y \<Rightarrow> g y)"
  by (simp add: sum.case_eq_if)

lemma extchoice_event_block: 
  assumes "wb_prism c" "wb_prism d" "c \<nabla> d"
  shows "event_block c A P\<sigma> \<box> event_block d B Q\<sigma> = event_block (c +\<^sub>\<triangle> d) (A <+> B)\<^sub>e (case_sum P\<sigma> Q\<sigma>)"
  using assms
  by (auto intro!:prism_fun_cong simp add: event_block_def fun_eq_iff extchoice_fun_def map_prod_as_ovrd prism_diff_implies_indep_funs prism_fun_combine case_sum_prod_dist sum.case_eq_if)

end