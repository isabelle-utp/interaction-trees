section \<open> ITree VCG meta-theory \<close>

theory ITree_VCG
  imports "Explorer.Explorer" "ITree_UTP.ITree_Countable_Nondeterminism"
  keywords "procedure" :: "thy_decl_block"
begin

notation seq_itree (infixr ";" 54)

lit_vars

setup Explorer_Lib.switch_to_quotes

def_consts MAX_SIL_STEPS = 500

lemma nth'_as_nth [simp]: "k < length xs \<Longrightarrow> nth' xs k = nth xs k"
  by (simp add: nth'_def)

declare list_augment_as_update [simp] 

declare nth_list_update [simp]

(* Added alternative syntax for list update to avoid ambiguity with assignment *)

syntax
  "_lupdbind":: "['a, 'a] => lupdbind"    ("(2_ \<leftarrow>/ _)")


(* Set up the procedure command *)

ML \<open>
Outer_Syntax.command @{command_keyword procedure} "define an ITree procedure"
  (ITree_Procedure.parse_procedure >> (Toplevel.local_theory NONE NONE o ITree_Procedure.mk_procedure @{typ pndet}));
\<close>

unbundle prog_ndet_syntax

end