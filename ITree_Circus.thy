section \<open> Circus Interaction Tree Semantics \<close>

theory ITree_Circus                          
  imports "ITree_FDSem"  "Shallow-Expressions.Shallow_Expressions"
begin

subsection \<open> Main Operators \<close>

type_synonym ('e, 's) action = "('e, 's) ktree"
type_synonym 'e process = "('e, unit) itree"

definition Skip :: "('e, 'r) ktree" where
"Skip = (\<lambda> s. Ret s)"

expr_ctr subst_id

lemma straces_Skip: "traces\<^sub>s (Skip) = ({[], [\<cmark> [\<leadsto>]]})\<^sub>e"
  by (simp add: Skip_def straces_def traces_Ret, expr_simp)

abbreviation Div :: "('e, 'r) ktree" where
"Div \<equiv> (\<lambda> s. diverge)"

lemma traces_deadlock: "traces(deadlock) = {[]}"
  by (auto simp add: deadlock_def traces_Vis)

abbreviation 
"Stop \<equiv> (\<lambda> s. deadlock)"

definition test :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) ktree" where
"test b = (\<lambda> s. if (b s) then Ret s else deadlock)"

lemma test_true: "test (True)\<^sub>e = Skip"
  by (simp add: test_def Skip_def)

lemma test_false: "test (False)\<^sub>e = Stop"
  by (simp add: test_def)

definition assigns :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('s\<^sub>1 \<Rightarrow> ('e, 's\<^sub>2) itree)" ("\<langle>_\<rangle>\<^sub>a") where
"assigns \<sigma> = (\<lambda> s. Ret (\<sigma> s))"

text \<open> Hide the state of an action to produce a process \<close>

definition proc :: "'s::default subst \<Rightarrow> ('e, 's) action \<Rightarrow> 'e process" where
"proc I A = (\<langle>(\<lambda> _. default)\<rangle>\<^sub>a \<Zcomp> \<langle>I\<rangle>\<^sub>a \<Zcomp> A \<Zcomp> assigns (\<lambda> s. ())) ()"

abbreviation "abs_st P \<equiv> P \<Zcomp> assigns (\<lambda> s. ())"

typ "'a::default"

syntax
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  ("'(_') := '(_')")  
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=" 92)
  "_mk_usubst"      :: "svids \<Rightarrow> uexprs \<Rightarrow> 's subst"

translations
  "_assignment x e" == "CONST assigns [x \<leadsto> e]"
(*  "_assignment x v" <= "CONST assigns (CONST subst_upd [\<leadsto>] x v)" *)

lemma traces_inp: "wb_prism c \<Longrightarrow> traces (inp c) = {[]} \<union> {[Ev (build\<^bsub>c\<^esub> v)] | v. True} \<union> {[Ev (build\<^bsub>c\<^esub> v), \<cmark> v] | v. True}" 
  apply (simp add: inp_def traces_Vis traces_Ret)
  apply (auto simp add: inp_def bind_eq_Some_conv traces_Ret domIff pdom.abs_eq  elim!: in_tracesE trace_to_VisE)
   apply (metis (no_types, lifting) wb_prism_def)
  apply (force simp add: traces_Ret)
  done 

definition input :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 's) ktree) \<Rightarrow> ('e, 's) ktree" where
"input c P = (\<lambda> s. inp c \<bind> (\<lambda> x. P x s))"

definition input_in :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('s \<Rightarrow> 'a list) \<Rightarrow> ('a \<Rightarrow> ('e, 's) ktree) \<Rightarrow> ('e, 's) ktree" where
"input_in c A P = (\<lambda> s. inp_in c (A s) \<bind> (\<lambda> x. P x s))"

syntax 
  "_input"    :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("_?_ \<rightarrow> _" [90, 0, 91] 91)
  "_input_in" :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_?_:_ \<rightarrow> _" [90, 0, 0, 91] 91)

translations "c?(x) \<rightarrow> P" == "CONST input c (\<lambda> (x). P)"
translations "c?(x):A \<rightarrow> P" == "CONST input_in c (A)\<^sub>e (\<lambda> (x). P)"

definition "output" :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('s \<Rightarrow> 'a) \<Rightarrow> ('e, 's) ktree \<Rightarrow> ('e, 's) ktree" where
"output c e P = (\<lambda> s. outp c (e s) \<then> P s)"

syntax "_output" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_!'(_') \<rightarrow> _" [90, 0, 91] 91)
translations "c!(e) \<rightarrow> P" == "CONST output c (e)\<^sub>e P"

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

subsection \<open> Examples \<close>

alphabet State = 
  buf :: "integer list"

instantiation State_ext :: (default) default
begin
  definition default_State_ext :: "'a State_scheme" where
    "default_State_ext = State.extend (State.make []) default"

instance ..
end

chantype Chan =
  Input :: integer
  Output :: integer
  State :: "integer list"

no_notation conj  (infixr "&" 35)

syntax
  "_cguard" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ & _" [70, 71] 70)

translations
  "_cguard b P" == "(CONST test (b)\<^sub>e) \<Zcomp> P"

lit_vars

definition "buffer 
  = proc 
      ([buf \<leadsto> []] :: State \<Rightarrow> State)
      (loop ((Input?(i):[0,1,2,3] \<rightarrow> buf := (buf @ [i]))
            \<box> ((length(buf) > 0) & Output!(hd buf) \<rightarrow> buf := (tl buf) \<Zcomp> State!(buf) \<rightarrow> Skip)
            \<box> State!(buf) \<rightarrow> Skip))"

definition "mytest = loop (Input?(i) \<rightarrow> (\<lambda> s. Ret (s @ [i])) \<box> Stop)"

definition "bitree = loop (\<lambda> s. inp_in Input [0,1,2,3] \<bind> outp Output)"

chantype schan = 
  a :: unit b :: unit c :: unit

definition "partest = 
  (\<lambda> s. hide
        (gpar_csp (loop (\<lambda> s. (do { outp a (); outp b (); Ret () })) s) {build\<^bsub>b\<^esub> ()} 
                  (loop (\<lambda> s. (do { outp b (); outp c (); Ret () })) s)) {build\<^bsub>b\<^esub> ()})" 

subsection \<open> Code Generation \<close>
             
export_code mytest bitree buffer partest diverge deadlock in Haskell module_name ITree_Examples (string_classes)

end