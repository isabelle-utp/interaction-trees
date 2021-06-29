theory TrivialPursuit
  imports "../ITree_Extraction"
begin

lit_vars

type_synonym Player = "String.literal"

enumtype Colour = blue | pink | yellow | brown | green | orange

alphabet LocalScore =
  s :: "Colour set"
 
alphabet GlobalScore =
  score :: "Player \<Zpfun> LocalScore"

definition AnswerLocal :: "Colour \<Rightarrow> ('e, LocalScore) htree" where
"AnswerLocal c = s := s \<union> {c}"

definition [lens_defs]: "pfun_collection_lens = pfun_lens"

adhoc_overloading collection_lens pfun_collection_lens

lemma pfun_collection_lens_mwb [simp]: "mwb_lens (pfun_collection_lens e)"
  by (simp add: pfun_collection_lens_def)

lemma source_pfun_collection_lens: "\<S>\<^bsub>pfun_collection_lens i\<^esub> = {f. i \<in> pdom(f)}"
  by (auto simp add: lens_defs lens_source_def, metis pfun_upd_ext)

lemma defined_pfun_collection_lens [simp]: 
  "\<lbrakk> vwb_lens x; $x \<sharp> (@e)\<^sub>e \<rbrakk> \<Longrightarrow> \<^bold>D(x[e]) = (e \<in> pdom($x))\<^sub>e"
  by (simp add: lens_defined_def src_dyn_lens unrest source_ns_alpha source_pfun_collection_lens)
     (simp add: lens_defs wb_lens.source_UNIV)

term "AnswerLocal c \<Up>\<Up> score[p]"

end