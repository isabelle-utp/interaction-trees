theory ITree_Procedure
  imports ITree_Circus
begin

datatype (discs_sels) ('inp, 'outp) methop = Call_C 'inp | Return_C 'outp

definition [lens_defs]: "Call = ctor_prism Call_C is_Call_C un_Call_C"
definition [lens_defs]: "Return = ctor_prism Return_C (Not \<circ> is_Call_C) un_Return_C"

record ('val, 'st) valst =
  vval :: 'val
  vst  :: 'st

type_synonym ('e, 'inp, 'outp, 'st) procedure = "('e, ('inp, 'st) valst, ('outp, 'st) valst) ktree"

translations
  (type) "('e, 'inp, 'outp, 'st) procedure" <= (type) "('inp, 'st) valst \<Rightarrow> ('e, ('outp, 'st') valst) itree" 

definition procproc :: "(_, 'inp, 'outp, 'st::default) procedure \<Rightarrow> ('inp, 'outp) methop process" where
"procproc P = process [\<leadsto>] (\<lambda> s. inp Call \<bind> (\<lambda> inp. P \<lparr> vval = inp, vst = s \<rparr> \<bind> (\<lambda> vst. outp Return (vval vst) \<bind> Ret)))"

definition promote_proc :: "('e, 'inp, 'outp, 'ls) procedure \<Rightarrow> ('i \<Rightarrow> ('ls \<Longrightarrow> 's)) \<Rightarrow> ('e, 'i \<times> 'inp, 'outp, 's) procedure" where
"promote_proc P a = (\<lambda> v. P \<lparr> vval = snd (vval v), vst = get\<^bsub>a (fst (vval v))\<^esub> (vst v) \<rparr> \<bind> (\<lambda> v'. Ret \<lparr> vval = vval v', vst = put\<^bsub>a (fst (vval v))\<^esub> (vst v) (vst v')\<rparr>))"

lemma Call_wb_prism [simp, code_unfold]: "wb_prism Call" by (unfold_locales, auto simp add: lens_defs)
lemma Return_wb_prism [simp, code_unfold]: "wb_prism Return" by (unfold_locales, auto simp add: lens_defs)

definition "proc_ret e = (\<lambda> s. Ret \<lparr> vval = e s, vst = s \<rparr>)"

definition procedure :: "('inp \<Rightarrow> 'st \<Rightarrow> ('e, ('outp, 'st) valst) itree) \<Rightarrow> ('e, 'inp, 'outp, 'st) procedure" where
"procedure P = (\<lambda> vs. P (vval vs) (vst vs))"

definition proc_call :: "('o \<Longrightarrow> 's) \<Rightarrow> ('e, 'i, 'o, 'ls::default) procedure \<Rightarrow> ('i, 's) expr \<Rightarrow> ('e, 's) htree" 
  where "proc_call x P e = (\<lambda> s. P \<lparr> vval = e s, vst = default \<rparr> \<bind> (\<lambda> vs. Ret (put\<^bsub>x\<^esub> s (vval vs))))"

definition exec_proc :: "(unit, 'inp, 'out, 'st::default) procedure \<Rightarrow> 'inp \<Rightarrow> (unit, 'out) itree" where
"exec_proc P i = P \<lparr> vval = i, vst = default \<rparr> \<bind> (\<lambda> x. Ret (vval x))"

syntax 
  "_procedure" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("proc _./ _" [0, 20] 20)
  "_call" :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ := call _ _" [61, 0, 61] 61)
  "_return" :: "logic \<Rightarrow> logic" ("return")

translations 
  "_procedure x P" == "CONST procedure (\<lambda> x. P)"
  "_return e" == "CONST proc_ret (e)\<^sub>e"
  "_call x P e" == "CONST proc_call x P (e)\<^sub>e"

end