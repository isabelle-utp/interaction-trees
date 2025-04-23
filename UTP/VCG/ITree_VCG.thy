section \<open> ITree VCG meta-theory \<close>

theory ITree_VCG
  imports "Explorer.Explorer" "ITree_UTP.ITree_Countable_Nondeterminism" "ITree_UTP.ITree_Random"
  keywords "program" "procedure" :: "thy_decl_block"
begin

notation seq_itree (infixr ";" 54)

declare [[literal_variables]]

setup Explorer_Lib.switch_to_quotes

def_consts MAX_SIL_STEPS = 500

lemma nth'_as_nth [simp]: "k < length xs \<Longrightarrow> nth' xs k = nth xs k"
  by (simp add: nth'_def)

declare list_augment_as_update [simp] 

declare nth_list_update [simp]

(* Added alternative syntax for list update to avoid ambiguity with assignment *)

syntax
  "_lupdbind":: "['a, 'a] => lupdbind"    ("(2_ \<leftarrow>/ _)")
  "_updbind" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"      ("(2_ \<leftarrow>// _)")

(* Should lens gets appear in VCs, it's better they are concise and pretty *)

syntax
  "_lens_get_pretty" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_<_>" [999,0] 999)

translations
  "_lens_get_pretty x s" == "CONST lens_get x s"

(* Syntax to allow programs to exit returning a value *)

definition exit_prog :: "('a, 's) expr \<Rightarrow> 's \<Rightarrow> ('e, 'a) itree" where 
"exit_prog e = (\<lambda> s. Ret (e s))"

syntax "_exit_prog" :: "logic \<Rightarrow> logic" ("exit _")
translations "exit e" == "CONST exit_prog (e)\<^sub>e"

lemma hl_exit [hoare_safe]: "\<forall> s. (P)\<^sub>e s \<longrightarrow> (Q)\<^sub>e (e s) \<Longrightarrow> H{P} exit e {Q}"
  by (simp add: exit_prog_def hoare_alt_def)

(* Set up the program and procedure command *)

ML \<open>
Outer_Syntax.command @{command_keyword program} "define an ITree program"
  (ITree_Procedure.parse_program >> (Toplevel.local_theory NONE NONE o ITree_Procedure.mk_program @{typ pndet}));

Outer_Syntax.command @{command_keyword procedure} "define an ITree procedure"
  (ITree_Procedure.parse_procedure >> (Toplevel.local_theory NONE NONE o ITree_Procedure.mk_procedure @{typ pndet}));
\<close>

unbundle Expression_Syntax
unbundle prog_ndet_syntax

(* Print translation tweaks for syntax *)

translations
  (* Display sequents using the semantic bracket notation *)
  "_bigimpl (_asm P) Q" <= "CONST Pure.imp P Q"
  "_bigimpl (_asms (_asm P) Q) R" <= "_bigimpl (_asm P) (_bigimpl Q R)"
  (* Hide dollar symbols on program variables *)
  "x" <= "_sexp_var x"

end