theory Channel_Typerep
  imports Executable_Universe
begin

text \<open> A channel is represented by a name, a type, and a predicate that determines whether the event is on this channel. \<close>

datatype 'a chanrep = Chanrep (chan_name: String.literal) (chan_type: String.literal) (is_chan: "'a \<Rightarrow> bool") 

definition evs_of :: "'a chanrep \<Rightarrow> 'a set" where
"evs_of c = {e. is_chan c e}"

text \<open> A channel type is represented by a list of channels \<close>

type_synonym 'a chantyperep = "'a chanrep list"

text \<open> Well-formed channel type representations \<close>

definition wf_chantyperep :: "'a chanrep list \<Rightarrow> bool" where 
"wf_chantyperep ct = 
  (distinct (map chan_name ct) \<comment> \<open> Each channel name is unique \<close> 
  \<and> (\<forall> x. foldr (\<or>) (map (\<lambda> c. is_chan c x) ct) False) \<comment> \<open> Every event has a channel \<close>
  \<and> (\<forall> c1\<in>set ct. \<forall> c2\<in>set ct. \<forall> e. is_chan c1 e \<and> is_chan c2 e \<longrightarrow> c1 = c2) \<comment> \<open> Every event has exactly one channel \<close>
  \<and> (\<forall> c\<in>set ct. \<exists> e. is_chan c e))" \<comment> \<open> Every channel has at least one event \<close>

method wf_chantyperep uses disc def = (force intro: disc simp add: wf_chantyperep_def def)

lemma foldr_disj_one_True: "foldr (\<or>) Ps False \<Longrightarrow> (\<exists> P\<in>set Ps. P)"
  by (induct Ps, auto)

text \<open> Every event has a channel \<close>

lemma chantyperep_ev_has_chan: "wf_chantyperep ct \<Longrightarrow> \<exists> c\<in>set ct. is_chan c e"
  using foldr_disj_one_True by (fastforce simp add: wf_chantyperep_def)

definition find_chanrep :: "'a chantyperep \<Rightarrow> 'a \<Rightarrow> 'a chanrep option" where 
"find_chanrep ct e = find (\<lambda> c. is_chan c e) ct"

lemma find_chanrep_Some: "wf_chantyperep ct \<Longrightarrow> \<exists> c\<in>set ct. find_chanrep ct e = Some c"
  by (metis chantyperep_ev_has_chan find_None_iff2 find_Some_iff find_chanrep_def not_Some_eq nth_mem)

text \<open> Every channel has at least one event \<close>

lemma chantyperep_chan_has_ev:"\<lbrakk> wf_chantyperep ct; c \<in> set ct \<rbrakk> \<Longrightarrow> \<exists>e. is_chan c e"
  using wf_chantyperep_def by fastforce

class chantyperep = 
  fixes chantyperep :: "'a itself \<Rightarrow> 'a chantyperep"
  assumes wf_chantyperep: "wf_chantyperep (chantyperep TYPE('a))"
begin

definition chan_names :: "'a itself \<Rightarrow> String.literal list" where 
"chan_names t = map chan_name (chantyperep t)"

lemma distinct_chan_names [simp]: "distinct (chan_names TYPE('a))"
  using chan_names_def local.wf_chantyperep wf_chantyperep_def by auto
  
definition chanrep_of :: "'a \<Rightarrow> 'a chanrep" where
"chanrep_of e = the (find_chanrep (chantyperep TYPE('a)) e)"

lemma range_chanrep_of: "range chanrep_of = set (chantyperep TYPE('a))"
  apply (auto simp add: chanrep_of_def image_def)
  apply (metis find_chanrep_Some local.wf_chantyperep option.sel)
  apply (metis find_Some_iff find_chanrep_Some find_chanrep_def local.wf_chantyperep option.sel wf_chantyperep_def)
  done

lemma finite_chanreps: "finite (range chanrep_of)"
  using range_chanrep_of by auto

text \<open> An independent family of events, each corresponding to one set of channels. \<close>

definition ChanBasis :: "'a set set" where
"ChanBasis = evs_of ` range chanrep_of"

lemma family_chan_basis: "\<Union> ChanBasis = UNIV"
  apply (auto simp add: ChanBasis_def evs_of_def)
  apply (metis chantyperep_ev_has_chan image_iff local.wf_chantyperep range_chanrep_of)
  done

lemma indep_chan_basis: "\<lbrakk> A \<in> ChanBasis; B \<in> ChanBasis; A \<noteq> B \<rbrakk> \<Longrightarrow> A \<inter> B = {}"
  apply (auto simp add: ChanBasis_def evs_of_def)
  apply (metis local.wf_chantyperep rangeI range_chanrep_of wf_chantyperep_def)+
  done

end

definition prism_chanrep :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e::chantyperep) \<Rightarrow> 'e chanrep" where
"prism_chanrep c = (SOME d. evs_of d = range (build\<^bsub>c\<^esub>))"  

chantype c1 = 
  a :: int
  b :: int
  c :: bool
  d :: bool

instantiation c1 :: chantyperep
begin

definition chantyperep_c1 :: "c1 itself \<Rightarrow> c1 chanrep list" where
  "chantyperep_c1 x = [ Chanrep STR ''a'' STR ''int'' is_a_C
                      , Chanrep STR ''b'' STR ''int'' is_b_C
                      , Chanrep STR ''c'' STR ''bool'' is_c_C
                      , Chanrep STR ''d'' STR ''bool'' is_d_C ]"
instance 
  apply (intro_classes)
  apply (wf_chantyperep disc: c1.disc c1.exhaust_disc def: chantyperep_c1_def)
  done

end

lemma "prism_chanrep a = Chanrep STR ''a'' STR ''int'' is_a_C"
  oops

end