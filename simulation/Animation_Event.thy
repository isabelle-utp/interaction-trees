section \<open> Animation Events \<close>

theory Animation_Event
  imports Channel_Type_Rep "Interaction_Trees.ITree_Extraction" 
begin

declare [[typedef_overloaded]]

text \<open> For animation, we support three kinds of basic event: an input, output, and "mixed" event, 
  consisting of an output followed by an input. The types of the various data is supplied by the
  @{class uchantyperep}. \<close>

datatype ('e, 'proc) animev =
  AnimInput "'e name" "uval \<Rightarrow> bool" "uval \<Rightarrow> 'proc" | \<comment> \<open> Input over named channel, with continuation function \<close>
  AnimOutput "'e name" "uval" "'proc" | \<comment> \<open> Output value over channel, single continuation\<close>
  AnimIO "'e name" "uval" "uval \<Rightarrow> bool" "uval \<Rightarrow> 'proc" \<comment> \<open> Both output and input \<close>

declare [[typedef_overloaded=false]]

text \<open> The following function turns an animation event into a partial function, the domain of
  which is the set of events corresponding to the animation event. \<close>

fun pfun_of_animev :: "('e::uchantyperep, 'proc) animev \<Rightarrow> 'e \<Zpfun> 'proc" where
"pfun_of_animev (AnimInput n B P) 
  = (\<lambda> e\<in>{uchan_mk (event_of (label_of n, inp)) | inp. inp :\<^sub>u name_type n \<and> B inp} \<bullet> P (ev_uval (uchan_dest e)))" |
"pfun_of_animev (AnimOutput n v P) 
  = (\<lambda> e\<in>{uchan_mk (event_of (label_of n, v))} \<bullet> P)" |
\<comment> \<open> I *think* the next line is correct, but it needs checking \<close>
"pfun_of_animev (AnimIO n out B Q) 
  = (\<lambda> e\<in>{uchan_mk (event_of (label_of n, PairV (out, inp))) | inp. inp :\<^sub>u snd (ofPairT (name_type n)) \<and> B inp} 
     \<bullet> Q (snd (ofPairV (ev_uval (uchan_dest e)))))"

lemma map_pfun_pfun_of_animev: 
  "map_pfun f (pfun_of_animev aev) = pfun_of_animev (map_animev f aev)"
  by (cases aev, simp_all add: pfun_eq_iff)

definition anim_input :: "('a::uvals, 'e::uchantyperep) channel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('e, 's) itree) \<Rightarrow> ('e, ('e, 's) itree) animev" where
"anim_input c P C = AnimInput (channel_name c) (P \<circ> from_uval) (C \<circ> from_uval)"

(*
lemma "wf_channel c \<Longrightarrow> pfun_of_animev (anim_input c P C) = (\<lambda> e\<in>{channel_build c v | v. P v} \<bullet> C (the (channel_match c e)))"
  apply (simp add: anim_input_def channel_build_def channel_match_def)
  apply (rule pabs_cong)
*)
  

definition anim_inp :: 
  "('a::uvals, 'e::uchantyperep) channel \<Rightarrow> bool \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('e, 's) itree) \<Rightarrow> ('e, ('e, 's) itree) animev list" where
"anim_inp c P Q C = (if P then [AnimInput (channel_name c) (Q \<circ> from_uval) (C \<circ> from_uval)] else [])"

definition anim_outp ::
  "('a::uvals, 'e::uchantyperep) channel \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> ('e, 's) itree \<Rightarrow> ('e, ('e, 's) itree) animev list" where
"anim_outp c B v P = (if B then [AnimOutput (channel_name c) (to_uval v) P] else [])"

text \<open> How can we represent the domain of an animation event partial function? Do we need to? \<close>

definition pfun_of_animevs ::
  "('e::uchantyperep, 'b) animev list \<Rightarrow> 'e \<Zpfun> 'b" where
"pfun_of_animevs aevs = foldr (\<lambda> c f. pfun_of_animev c \<oplus> f) aevs {}\<^sub>p"

(* Need channel set notation *)
(*
lemma pdom_anim_inp: 
  "\<lbrakk> wf_channel d; c = channel_prism d \<rbrakk> \<Longrightarrow> pdom (pfun_of_animevs (anim_inp d True B P)) = \<lbrace> c v. B v \<rbrace>"
  apply (auto simp add: pfun_of_animevs_def anim_inp_def evcollect_def channel_prism_def)
  apply (smt (verit, ccfv_SIG) channel_build.rep_eq from_uval_inv mk_event_event_of_def name_type_chantype wf_channel_def)
  apply (smt (verit, del_insts) channel_build.rep_eq mk_event_event_of_def name_type_chantype to_uval_inv to_uval_typ wf_channel_def)
  done
*)

definition animevs :: "('e::uchantyperep, ('e, 's) itree) animev list list \<Rightarrow> ('e, 's) itree" where
"animevs aevss = Vis (pfun_of_animevs (concat aevss))"

lemma map_pfun_pfun_of_animevs (* [code] *):
  "map_pfun f (pfun_of_animevs aevs) = pfun_of_animevs (map (map_animev f) aevs)"
  by (induct aevs, simp_all add: pfun_of_animevs_def map_pfun_pfun_of_animev)

lemma pfun_of_aevs_Nil [simp]: "pfun_of_animevs [] = {}\<^sub>p"
  by (simp add: pfun_of_animevs_def)

lemma pfun_of_avs_Cons [simp]: "pfun_of_animevs (chf # chfs) = pfun_of_animev chf \<oplus> pfun_of_animevs chfs"
  by (simp add: pfun_of_animevs_def)

lemma pfun_of_aevs_override (* [code] *): 
  "pfun_of_animevs chfs1 \<oplus> pfun_of_animevs chfs2 = pfun_of_animevs (chfs1 @ chfs2)"
  by (induct chfs1 arbitrary: chfs2; simp add: override_assoc; metis override_assoc)

end