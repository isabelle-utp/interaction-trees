theory TrivialPursuit
  imports "../ITree_Extraction" "../ITree_Operations"
begin

definition [lens_defs]: "pfun_collection_lens = pfun_lens"

adhoc_overloading collection_lens pfun_collection_lens

lemma pfun_collection_lens_mwb [simp]: "mwb_lens (pfun_collection_lens e)"
  by (simp add: pfun_collection_lens_def)

lemma source_pfun_collection_lens: "\<S>\<^bsub>pfun_collection_lens i\<^esub> = {f. i \<in> pdom(f)}"
  by (auto simp add: lens_defs lens_source_def, metis pfun_upd_ext)

lemma defined_pfun_collection_lens [simp, code_unfold]: 
  "\<lbrakk> vwb_lens x; $x \<sharp> (e)\<^sub>e \<rbrakk> \<Longrightarrow> \<^bold>D(x[e]) = (e \<in> pdom($x))\<^sub>e"
  by (simp add: lens_defined_def src_dyn_lens unrest source_ns_alpha source_pfun_collection_lens)
     (simp add: lens_defs wb_lens.source_UNIV expr_defs)

lit_vars

enumtype Player = one | two | three | four | five | six

enumtype Colour = blue | pink | yellow | brown | green | orange

alphabet LocalScore =
  s :: "Colour set"

record_default LocalScore

alphabet GlobalScore =
  score :: "Player \<Zpfun> LocalScore"

record_default GlobalScore

definition AnswerLocal :: "Colour \<Rightarrow> ('e, LocalScore) htree" where
[code_unfold]: "AnswerLocal c = \<questiondown>c \<notin> s? \<Zcomp> s := s \<union> {c}"

chantype chan1 =
  answer1 :: "Colour"


chantype chan =
  answer :: "Player \<times> Colour"

definition "Answer = operation answer1 AnswerLocal"

definition AnswerGlobal :: "(chan, GlobalScore) htree" where
[code_unfold]: "AnswerGlobal = operation answer (promote_op (\<lambda> p. (score[p])\<^sub>v) AnswerLocal)"

definition "TrivialPursuit = process [\<leadsto>] (loop (Answer \<box> Stop))"

lemma "AnswerGlobal = undefined"
  apply (simp add: AnswerGlobal_def operation_def)
  oops

declare operation_def [code_unfold]
declare wp [code_unfold]
declare unrest [code_unfold]

export_code TrivialPursuit in Haskell module_name TrivialPursuit (string_classes)

term "AnswerLocal c \<Up>\<Up> score[p]"

end