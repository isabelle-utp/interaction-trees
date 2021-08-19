section \<open> Failures Divergences Semantics \<close>

theory ITree_FDSem
  imports ITree_CSP
begin

subsection \<open> Preliminaries \<close>

datatype ('e, 's) event = Ev (of_Ev: 'e) | Term 's

abbreviation "\<Sigma> \<equiv> range Ev"

adhoc_overloading
  tick Term

type_synonym ('e, 's) trace = "('e, 's) event list"
type_synonym ('e, 's) refusal = "('e, 's) event set"

lemma map_Ev_eq_iff [simp]: "map Ev xs = map Ev ys \<longleftrightarrow> xs = ys"
  by (metis event.inject(1) list.inj_map_strong)

lemma of_Ev_Ev [simp]: "(of_Ev \<circ> Ev) = id"
  by (auto)

lemma map_Ev_of_Ev [simp]: "set tr \<subseteq> range Ev \<Longrightarrow> map (Ev \<circ> of_Ev) tr = tr"
  by (metis (mono_tags, lifting) comp_def event.collapse(1) event.disc(1) map_idI rangeE subset_code(1))

lemma trace_EvE [elim]: "\<lbrakk> set tr \<subseteq> range Ev; \<And> tr'. tr = map Ev tr' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis map_Ev_of_Ev map_map)

lemma map_of_Ev_append [simp]: "set tr \<subseteq> range Ev \<Longrightarrow> map of_Ev tr = tr\<^sub>1 @ tr\<^sub>2 \<longleftrightarrow> tr = (map Ev tr\<^sub>1 @ map Ev tr\<^sub>2)"
  by (auto)

lemma trace_last_Ev [simp]: "s @ [a] = map Ev tr \<longleftrightarrow> (tr \<noteq> [] \<and> s = map Ev (butlast tr) \<and> a = Ev (last tr))"
  by (auto simp add: snoc_eq_iff_butlast map_butlast last_map)

lemma Ev_subset_image [simp]: "(Ev ` A) \<subseteq> (Ev ` B) \<longleftrightarrow> A \<subseteq> B"
  by auto

lemma Ev_in_Ev_image [simp]: "Ev x \<in> Ev ` A \<longleftrightarrow> x \<in> A"
  by auto

text \<open> Roscoe's multi-step transition relation including termination events. We chose to have a
  process become @{const deadlock} after terminating. \<close>

definition mstep_to :: "('e, 's) itree \<Rightarrow> ('e, 's) trace \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" ("_ \<Midarrow>_\<Rightarrow> _" [55, 0, 55] 55)
  where "P \<Midarrow>tr\<Rightarrow> P' \<equiv> ((set tr \<subseteq> range Ev \<and> P \<midarrow>map of_Ev tr\<leadsto> P') \<or> 
                        (\<exists> tr' x. tr = (map Ev tr') @ [\<checkmark>(x)] \<and> P \<midarrow>tr'\<leadsto> Ret x \<and> P' = deadlock))"

lemma mstep_termE [elim]: 
  "\<lbrakk> P \<Midarrow>tr @ [\<checkmark>(v)]\<Rightarrow> P'; \<And> tr'. \<lbrakk> tr = map Ev tr'; P \<midarrow>tr'\<leadsto> Ret v; P' = deadlock \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (auto simp add: mstep_to_def)

lemma mstep_stabilises: "\<lbrakk> P \<Midarrow>tr\<Rightarrow> P'; tr \<noteq> [] \<rbrakk> \<Longrightarrow> stabilises P"
  apply (auto simp add: mstep_to_def stabilises_traceI)
  apply (meson stabilises_traceI)
  apply (metis diverge_no_Ret_trans diverges_then_diverge)
  done

definition initials :: "('e, 's) itree \<Rightarrow> ('e, 's) event set" ("\<I>") where
"\<I>(P) = {e. \<exists> P'. P \<Midarrow>[e]\<Rightarrow> P'}"

lemma initials_Vis: "\<I>(Vis F) = Ev ` pdom F"
  by (auto simp add: initials_def mstep_to_def)

lemma initials_Ret: "\<I>(Ret x) = {\<checkmark> x}"
  by (auto simp add: initials_def mstep_to_def)

lemma initials_Sil: "\<I>(Sil P) = \<I>(P)"
  apply (auto simp add: initials_def mstep_to_def)
  apply (metis itree.distinct(5) trace_of_Sils trace_to_SilE trace_to_single_iff)
  apply blast
  done

subsection \<open> Traces \<close>

definition traces :: "('e, 's) itree \<Rightarrow> ('e, 's) trace set" where
"traces P = {map Ev tr | tr. \<exists> P'. P \<midarrow>tr\<leadsto> P'} \<union> {map Ev tr @ [\<checkmark>(v)] | tr v. P \<midarrow>tr\<leadsto> Ret v}"

lemma wbisim_eq_traces: "P \<approx> Q \<Longrightarrow> traces(P) = traces(Q)"
  apply (auto simp add: traces_def)
  apply (metis wbisim_step)
  apply (metis (no_types, hide_lams) wbisim_step_terminate)
  apply (metis (no_types, lifting) wbisim_step wbisim_sym)
  apply (metis (mono_tags, lifting) wbisim_step_terminate wbisim_sym)
  done

lemma trace_alt_def: "traces P = {s. \<exists> Q. P \<Midarrow>s\<Rightarrow> Q}"
  by (auto simp add: traces_def mstep_to_def)

definition straces :: "('e, 's) htree \<Rightarrow> ('s \<Rightarrow> ('e, 's) trace set)" ("traces\<^sub>s") where
"straces K = (\<lambda> s. traces (K s))"

lemma Nil_in_traces [simp]: "[] \<in> traces P"
  by (auto simp add: traces_def)

lemma traces_prefix_in_Ev: "tr @ [\<checkmark>(v)] \<in> traces(P) \<Longrightarrow> set tr \<subseteq> range Ev"
  by (auto simp add: traces_def)

lemma term_trace_iff [simp]: "tr @ [\<checkmark>(v)] \<in> traces(P) \<longleftrightarrow> (set tr \<subseteq> range Ev \<and> P \<midarrow>map of_Ev tr\<leadsto> Ret v)"
  by (auto simp add: traces_def map_idI)

lemma in_tracesI1:
  assumes "P \<midarrow>tr\<leadsto> P'" "t = map Ev tr"
  shows "t \<in> traces(P)"
  using assms traces_def by fastforce

lemma in_tracesE [elim]:
  assumes
  "tr \<in> traces P"
  "\<And> P' tr'. \<lbrakk> tr = map Ev tr'; P \<midarrow>tr'\<leadsto> P' \<rbrakk> \<Longrightarrow> R"
  "\<And> P' tr' v. \<lbrakk> tr = map Ev tr' @ [\<checkmark>(v)]; P \<midarrow>tr'\<leadsto> Ret v \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms by (auto simp add: traces_def)

lemma not_in_traces [simp]: "set tr \<subseteq> range Ev \<Longrightarrow> tr \<notin> traces(P) \<longleftrightarrow> \<not> (\<exists> P'. P \<midarrow>map of_Ev tr\<leadsto> P')"
  by (simp add: traces_def, auto)

lemma traces_single_Term: "[\<checkmark> s] \<in> traces(P) \<Longrightarrow> \<exists> n. P = Sils n (Ret s)"
  by (auto simp add: traces_def)

lemma traces_Ret: "traces (Ret x) = {[], [\<checkmark>(x)]}"
  by (auto simp add: traces_def)

lemma traces_Tau: "traces (Sil P) = traces P"
  by (force simp add: traces_def)

lemma traces_Vis: "traces (Vis F) = {[]} \<union> {Ev a # tr | a tr. a \<in> pdom(F) \<and> tr \<in> traces(F a)}"
  apply (auto elim!: in_tracesE trace_to_VisE)
  apply (auto simp add: traces_def)
  apply (metis list.map(2) trace_to_Vis)
  apply (metis list.simps(9) trace_to_Vis)
  done
  
lemma traces_diverge: "traces diverge = {[]}"
  by (auto simp add: traces_def dest: trace_of_divergent)

lemma traces_bind: 
  "traces (P \<bind> Q) = 
  (traces(P) \<inter> lists (range Ev)) 
  \<union> {tr\<^sub>1 @ tr\<^sub>2 | tr\<^sub>1 tr\<^sub>2. \<exists> v. tr\<^sub>1 @ [\<checkmark>(v)] \<in> traces(P) \<and> tr\<^sub>2 \<in> traces(Q v)}"
  apply (auto elim!: in_tracesE trace_to_bindE bind_RetE')
  apply (auto simp add: traces_def)
  apply (metis (no_types, lifting) Nil_is_map_conv append_Nil2 image_subset_iff list.set_map map_of_Ev_append range_eqI)
  apply (smt (z3) Ev_subset_image UNIV_I bind_RetE list.set_map list.simps(8) map_of_Ev_append self_append_conv2 subsetI trace_to_Nil)
  apply (metis (no_types, hide_lams) List.map.id append.simps(1) id_apply image_subset_iff list.set_map list.simps(8) map_map of_Ev_Ev rangeI trace_to_Nil)
  apply (metis (mono_tags, lifting) Ev_subset_image append.right_neutral list.set_map list.simps(8) map_of_Ev_append top_greatest)
  apply (metis (no_types, lifting) append.right_neutral list.set_map list.simps(8) map_of_Ev_append subset_image_iff top_greatest)
  apply (meson trace_to_bind_left)
  apply (metis (no_types, lifting) map_Ev_of_Ev map_append map_map trace_to_bind)
  apply (metis (no_types, lifting) map_Ev_of_Ev map_append map_map trace_to_bind)
  done

lemma T1a [simp]: "traces(P) \<noteq> {}"
  by (auto simp add: traces_def)

lemma T1b: 
  assumes "t\<^sub>1 @ t\<^sub>2 \<in> traces(P)"
  shows "t\<^sub>1 \<in> traces(P)"
proof (cases "t\<^sub>2 = []")
  case True
  then show ?thesis using assms by simp
next
  case False
  note t\<^sub>2 = this
  then show ?thesis
  using assms proof (erule_tac in_tracesE)
    fix P' tr 
    assume a: "t\<^sub>1 @ t\<^sub>2 = map Ev tr" "P \<midarrow>tr\<leadsto> P'"
    then obtain P'' where "P \<midarrow>map of_Ev t\<^sub>1\<leadsto> P''"
      by (metis UNIV_I append_Nil2 list.set_map map_append map_of_Ev_append subsetI subset_image_iff trace_to_appendE)
    with a show ?thesis
      by (metis append_eq_map_conv in_tracesI1 trace_to_appendE)
  next
    fix P' tr v
    assume a: "t\<^sub>1 @ t\<^sub>2 = map Ev tr @ [\<checkmark> v]" "P \<midarrow>tr\<leadsto> Ret v"
    hence "(tr = map of_Ev (butlast (t\<^sub>1 @ t\<^sub>2)))"
      by (metis append_Nil2 assms butlast_snoc list.simps(8) map_of_Ev_append traces_prefix_in_Ev)
    hence P: "P \<midarrow>map of_Ev (butlast (t\<^sub>1 @ t\<^sub>2)) \<leadsto> Ret v"
      using a(2) by force
    then have "\<exists> P''. P \<midarrow>map of_Ev t\<^sub>1\<leadsto> P''"
    proof (cases "t\<^sub>1 = []")
      case True
      thus ?thesis by auto
    next
      case False
      with P t\<^sub>2 show ?thesis
        by (force elim:trace_to_appendE simp add: butlast_append)
    qed
    thus ?thesis
      by (metis (no_types, hide_lams) UNIV_I a(1) butlast_append butlast_snoc in_tracesI1 le_sup_iff list.set_map map_Ev_of_Ev map_map set_append subsetI subset_image_iff t\<^sub>2)
  qed
qed

lemmas T1 = T1a T1b

subsection \<open> Divergences \<close>

definition "divergences P = {s @ t | s t. set s \<subseteq> range Ev \<and> set t \<subseteq> range Ev \<and> (\<exists> Q. P \<Midarrow>s\<Rightarrow> Q \<and> Q\<Up>)}"

lemma divergences_alt_def: 
  "divergences P = {map Ev (s @ t) | s t. (\<exists> Q. P \<midarrow>s\<leadsto> Q \<and> Q\<Up>)}"
  apply (auto elim!: trace_EvE simp add: divergences_def mstep_to_def)
  apply blast
   apply (metis Nil_is_map_conv event.distinct(1) last_map snoc_eq_iff_butlast)
  apply (force)
  done

lemma in_divergenceE [elim]:
  assumes
  "tr \<in> divergences P"
  "\<And> tr' s. \<lbrakk> tr = map Ev (tr' @ s); P \<midarrow>tr'\<leadsto> diverge \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms by (auto simp add: divergences_alt_def diverges_then_diverge)

lemma in_divergence_tranI: "P \<midarrow>tr\<leadsto> diverge \<Longrightarrow> map Ev tr \<in> divergences(P)"
  by (force simp add: divergences_alt_def)

lemma D1: 
  assumes "s \<in> divergences P" "t \<in> lists (range Ev)"
  shows "s @ t \<in> divergences P"
proof -
  obtain tr s' where "s = map Ev (tr @ s')" "P \<midarrow>tr\<leadsto> diverge"
    using assms(1) by blast
  with assms(2) show ?thesis
    apply (auto simp add: divergences_def mstep_to_def)
    apply (rule_tac x="map Ev tr" in exI)
    apply (force)
    done
qed

lemma D1_prefix: "\<lbrakk> s \<in> divergences P; set t \<subseteq> range Ev; s \<le> t \<rbrakk> \<Longrightarrow> t \<in> divergences P"
  by (metis (no_types, lifting) D1 Prefix_Order.prefixE in_listsI le_sup_iff set_append subset_code(1))

lemma no_divergences_then_div_free: "divergences P = {} \<Longrightarrow> div_free P"
  by (auto simp add: divergences_alt_def)
     (metis div_free_is_no_divergence no_divergence)

lemma div_free_iff_divergences_empty: "div_free P \<longleftrightarrow> divergences P = {}"
  by (metis div_free_is_no_divergence diverges_diverge ex_in_conv in_divergenceE no_divergence no_divergences_then_div_free)
  
lemma wbisim_le_divergences: 
  assumes "P \<approx> Q"
  shows "divergences(P) \<subseteq> divergences(Q)"
  using assms
  by (auto simp add: divergences_alt_def)
     (metis diverge_wbisim1 diverges_then_diverge wbisim_step)

lemma wbisim_eq_divergences: 
  assumes "P \<approx> Q"
  shows "divergences(P) = divergences(Q)"
  by (metis antisym_conv assms wbisim_le_divergences wbisim_sym)

definition divergence_strict_traces :: "('e, 's) itree \<Rightarrow> ('e, 's) trace set" ("traces\<^sub>\<bottom>") where
"divergence_strict_traces P = traces P \<union> divergences P"

lemma F1a: "traces\<^sub>\<bottom>(P) \<noteq> {}"
  by (simp add: divergence_strict_traces_def)

lemma non_divergent_prefix:
  assumes "t\<^sub>1 @ t\<^sub>2 \<in> divergences P" "t\<^sub>1 \<notin> divergences P" 
  shows "t\<^sub>1 \<in> traces P"
proof -
  obtain tr s where tr: "t\<^sub>1 @ t\<^sub>2 = map Ev (tr @ s)" "P \<midarrow>tr\<leadsto> diverge"
    using assms(1) by blast
  hence t1: "set t\<^sub>1 \<subseteq> range Ev"
    by (metis Ev_subset_image le_sup_iff list.set_map set_append subset_UNIV)
  hence "\<not> (t\<^sub>1 \<ge> map Ev tr)"
    by (meson D1_prefix assms(2) in_divergence_tranI tr(2))
  hence "t\<^sub>1 < map Ev tr"
    by (smt (z3) Prefix_Order.prefix_prefix append_eq_append_conv2 less_list_def map_append order_refl tr(1))
  thus ?thesis
    by (metis Prefix_Order.strict_prefixE' T1b in_tracesI1 tr(2))
qed

lemma F1b: "t\<^sub>1 @ t\<^sub>2 \<in> traces\<^sub>\<bottom>(P) \<Longrightarrow> t\<^sub>1 \<in> traces\<^sub>\<bottom>(P)"
  by (auto simp add: divergence_strict_traces_def non_divergent_prefix, meson T1b)

lemma divergences_diverge: "divergences diverge = lists (range Ev)"
  by (auto simp add: divergences_alt_def)
     (metis diverges_diverge map_append self_append_conv2 subsetI trace_EvE trace_to_Nil)

lemma divergences_Ret: "divergences (Ret x) = {}"
  by (simp add: divergences_alt_def)

subsection \<open> Failures \<close>

text \<open> A failure is recorded when there is a trace leading to a stable interaction tree. At this
  point, the refusal is calculated. \<close>

definition refuses :: "('e, 's) itree \<Rightarrow> ('e, 's) refusal \<Rightarrow> bool" (infix "ref" 65) where
"refuses P B = ((\<exists> F. P = Vis F \<and> B \<inter> Ev ` pdom F = {}) \<or> (\<exists> x. P = Ret x \<and> \<checkmark>(x) \<notin> B))"

lemma stable_refuses [simp]: "P ref A \<Longrightarrow> stable P"
  by (auto simp add: refuses_def)

lemma Ret_refuses [simp]: "Ret x ref B \<longleftrightarrow> \<checkmark>(x) \<notin> B"
  by (simp add: refuses_def)

lemma Vis_refuses [simp]: "Vis F ref B \<longleftrightarrow> B \<inter> Ev ` pdom F = {}"
  by (simp add: refuses_def)

lemma Sil_refuses [simp]: "Sil P ref B = False"
  by (simp add: refuses_def)

lemma refuses_down_closed: "\<lbrakk> P ref X; Y \<subseteq> X \<rbrakk> \<Longrightarrow> P ref Y"
  by (force simp add: refuses_def)

definition failure_of :: "('e list \<times> 'e set) \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" where
"failure_of = (\<lambda> (tr, E) P. \<exists> P'. P \<midarrow>tr\<leadsto> P' \<and> is_Vis P' \<and> E \<subseteq> (- pdom (un_Vis P')))"

lemma Vis_trace_to: "Vis F \<midarrow>tr\<leadsto> P \<longleftrightarrow> ((tr = [] \<and> P = Vis F) \<or> (\<exists> a tr'. a \<in> pdom(F) \<and> tr = a # tr' \<and> (F a) \<midarrow>tr'\<leadsto> P))"
  by (auto)

definition failures :: "('e, 's) itree \<Rightarrow> (('e, 's) trace \<times> ('e, 's) refusal) set" where
"failures P = {(s, X). \<exists> Q. P \<Midarrow>s\<Rightarrow> Q \<and> Q ref X} \<union> {(s @ [\<checkmark>(v)], X) | s v X. \<exists> Q. P \<Midarrow>s @ [\<checkmark>(v)]\<Rightarrow> Q}"

lemma failure_simpl_def: "failures P = {(s, X). \<exists> Q. P \<Midarrow>s\<Rightarrow> Q \<and> Q ref X}"
  by (force simp add: failures_def refuses_def deadlock_def)

lemma in_failuresE [elim]:
  assumes
  "f \<in> failures P"
  \<comment> \<open> The process reaches a visible choice, and is refusing all subsets of possible events \<close>
  "\<And> F B T tr. \<lbrakk> f = (map Ev tr, B); P \<midarrow>tr\<leadsto> Vis F; B \<inter> Ev ` pdom F = {} \<rbrakk> \<Longrightarrow> R"
  \<comment> \<open> The process reaches a termination event, and is refusing all non-termination events \<close>
  "\<And> x B T tr. \<lbrakk> f = (map Ev tr, B - {\<checkmark>(x)}); P \<midarrow>tr\<leadsto> Ret x \<rbrakk> \<Longrightarrow> R"
  \<comment> \<open> The process terminates; technically similar to the previous one. \<close>
  "\<And> x B T tr. \<lbrakk> f = (map Ev tr @ [\<checkmark> x], B); P \<midarrow>tr\<leadsto> Ret x \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms 
  by (auto simp add: failures_def refuses_def mstep_to_def deadlock_def)
     (metis Diff_insert_absorb map_Ev_of_Ev map_map)

lemma in_failuresI1: "\<lbrakk> P \<midarrow>tr\<leadsto> Vis F; B \<inter> Ev ` pdom(F) = {} \<rbrakk> \<Longrightarrow> (map Ev tr, B) \<in> failures P"
  by (auto simp add: failures_def mstep_to_def)

lemma in_failuresI2: "P \<midarrow>tr\<leadsto> Ret x \<Longrightarrow> (map Ev tr, B - {\<checkmark> x}) \<in> failures P"
  by (auto simp add: failures_def mstep_to_def)

lemma in_failures_iff:
  "(tr, B) \<in> failures P \<longleftrightarrow> 
        (\<exists> F tr'. tr = map Ev tr' \<and> P \<midarrow>tr'\<leadsto> Vis F \<and> B \<inter> Ev ` pdom(F) = {})
        \<or> (\<exists> x tr'. tr = map Ev tr' \<and> \<checkmark> x \<notin> B \<and> P \<midarrow>tr'\<leadsto> Ret x)
        \<or> (\<exists> x tr'. tr = map Ev tr' @ [\<checkmark> x] \<and> P \<midarrow>tr'\<leadsto> Ret x)"
  by (auto simp add: failures_def mstep_to_def refuses_def)
     (metis map_Ev_of_Ev map_map, blast+)

lemma failures_term_iff: 
  "(tr @ [\<checkmark>(v)], E) \<in> failures(P) \<longleftrightarrow> (\<exists> Q. P \<Midarrow>tr @ [\<checkmark>(v)]\<Rightarrow> Q)"
  by (auto simp add: failures_def)

lemma failures_term_Ev_iff: 
  "(map Ev tr @ [\<checkmark>(v)], E) \<in> failures(P) \<longleftrightarrow> P \<midarrow>tr\<leadsto> Ret v"
  by (auto simp add: failures_def mstep_to_def)

lemma T2: "(s, X) \<in> failures(P) \<Longrightarrow> s \<in> traces(P)"
  by force

lemma F2: "\<lbrakk> (s, X) \<in> failures(P); Y \<subseteq> X \<rbrakk> \<Longrightarrow> (s, Y) \<in> failures(P)"
  by (auto simp add: failures_def mstep_to_def, meson refuses_down_closed)

lemma F3: "\<lbrakk> (s, X) \<in> failures(P); Y \<inter> {x. s @ [x] \<in> traces(P)} = {} \<rbrakk> \<Longrightarrow> (s, X \<union> Y) \<in> failures(P)"
  apply (auto simp add: in_failures_iff traces_def set_eq_iff)
  apply (rename_tac F tr')
   apply (drule_tac x="F" in spec)
  apply (auto)
  apply (rename_tac F tr' a)
  apply (drule_tac x="Ev a" in spec)
  apply (auto)
  apply (metis Vis_Cons_trns butlast_snoc snoc_eq_iff_butlast trace_to_ConsE trace_to_Nil trace_to_trans)
  done

lemma wbisim_refusals_eq: "\<lbrakk> P \<approx> Q; stable P; stable Q \<rbrakk> \<Longrightarrow> P ref A \<longleftrightarrow> Q ref A"
  apply (auto simp add: refuses_def elim!: wbisim_VisE)
  apply (metis Vis_Sils is_Ret_Sils is_Vis_Sils itree.exhaust_disc)
  apply (metis itree.discI(2) wbisim.cases wbisim_RetE)
  apply (metis (mono_tags, lifting) Vis_Sils is_Ret_Sils is_Vis_Sils itree.exhaust_disc wbisim_Vis_eq wbisim_sym)
  apply (metis itree.discI(2) wbisim.cases wbisim_RetE wbisim_sym)
  done

lemma wbisim_le_failures: 
  assumes "P \<approx> Q"
  shows "failures(P) \<subseteq> failures(Q)"
proof (safe)
  fix s X
  assume "(s, X) \<in> failures P"
  thus "(s, X) \<in> failures Q"
    apply (auto simp add: in_failures_iff)
    apply (smt (verit, best) append.right_neutral assms trace_of_Sils trace_to_trans wbisim_VisE wbisim_step)
    apply (metis (no_types, lifting) assms wbisim_step_terminate)
    apply (metis assms wbisim_step_terminate)
  done
qed

lemma wbisim_eq_failures: 
  assumes "P \<approx> Q"
  shows "failures(P) = failures(Q)"
  by (metis antisym_conv assms wbisim_le_failures wbisim_sym)

definition stable_failures :: "('e, 's) itree \<Rightarrow> (('e, 's) trace \<times> ('e, 's) refusal) set" ("failures\<^sub>\<bottom>") where
"stable_failures P = failures(P) \<union> {(s, X). s \<in> divergences(P) \<and> X \<subseteq> range Ev}"

lemma diverge_no_failures [dest]: "failure_of t diverge \<Longrightarrow> False"
  apply (simp add: failure_of_def prod.case_eq_if)
  apply (auto)
  done

lemma failures_diverge: "failures diverge = {}"
  by (auto simp add: failures_def refuses_def mstep_to_def)

lemma failures_Sil:
  "failures (Sil P) = failures P"
  by (simp add: failures_def mstep_to_def, auto)

lemma failures_Ret: 
  "failures (Ret v) = {([], X) | X. \<checkmark>(v) \<notin> X} \<union> {([\<checkmark>(v)], X) | X. True}"
  by (simp add: failures_def mstep_to_def, safe, simp_all)

lemma failures_Vis:
  "failures (Vis F) = {([], X) | X. X \<inter> Ev ` pdom F = {}} 
                      \<union> {(Ev a # tr, X) | tr a X. a \<in> pdom(F) \<and> (tr, X) \<in> failures(F a)}"
  apply (simp add: failures_def mstep_to_def Vis_trace_to)
  apply (safe, simp_all)
  apply force
  apply blast
  apply blast
  apply blast
  apply (metis list.simps(9) option.sel)
  apply (metis list.simps(9) option.sel)
  done

lemma failures_deadlock: "failures deadlock = {([], X) | X. True}"
  by (auto simp add: deadlock_def failures_Vis)

lemma failures_inp:
  "wb_prism c \<Longrightarrow>
   failures (inp_in c A) = 
    {([], E) | E. \<forall> x\<in>A. Ev (build\<^bsub>c\<^esub> x) \<notin> E} 
    \<union> {([Ev (build\<^bsub>c\<^esub> x)], E) | E x. x \<in> A \<and> \<checkmark> () \<notin> E}
    \<union> {([Ev (build\<^bsub>c\<^esub> x), \<checkmark> ()], E) | E x. x \<in> A}"
  by (simp add: inp_in_where_def failures_Vis failures_Ret, safe)
     (auto simp add: wb_prism.range_build failures_Ret)  
  
lemma dom_bind [simp]: "Map.dom (\<lambda> x. P x \<bind> Q) = {x \<in> Map.dom P. the(P x) \<in> Map.dom Q}"
  by (auto)

lemma refuses_Term_iff: "Q ref (B \<union> range \<checkmark>) \<longleftrightarrow> (\<exists>F. Q = Vis F \<and> B \<inter> Ev ` pdom F = {})"
  by (auto simp add: refuses_def)

lemma failures_Term_iff:
  "(map Ev tr, B \<union> range \<checkmark>) \<in> failures P \<longleftrightarrow> (\<exists> F. P \<midarrow>tr\<leadsto> Vis F \<and> B \<inter> Ev ` pdom F = {})"
  by (auto simp add: failures_def mstep_to_def refuses_Term_iff)
     (metis event.simps(4) trace_last_Ev)+
  
text \<open> Refusing all termination events \<close>

lemma "(tr, B \<union> range \<checkmark>) \<in> failures P \<longleftrightarrow> 
        (\<exists> F tr'. tr = map Ev tr' \<and> P \<midarrow>tr'\<leadsto> Vis F \<and> B \<inter> Ev ` pdom(F) = {})
        \<or> (\<exists> x tr'. tr = map Ev tr' @ [\<checkmark> x] \<and> P \<midarrow>tr'\<leadsto> Ret x)"
  apply (auto simp add: failures_def mstep_to_def refuses_def)
  apply (metis inf_sup_distrib2 map_Ev_of_Ev map_map sup_eq_bot_iff)
  apply (metis Vis_refuses refuses_Term_iff)
  done

lemma failures_bind: 
  "failures (P \<bind> Q) = 
    {(s, X). set s \<subseteq> range Ev \<and> (s, X \<union> (range Term)) \<in> failures(P)}
    \<union> {(s @ t, X) | s t X. \<exists> v. s @ [\<checkmark>(v)] \<in> traces(P) \<and> (t, X) \<in> failures(Q v)}"
  apply (rule set_eqI)
  apply (clarify)
  apply (simp add: in_failures_iff)
  apply (auto elim!: trace_to_bindE bind_VisE' bind_RetE')
              apply (meson Vis_refuses refuses_Term_iff)
             apply (metis (no_types, hide_lams) List.map.id append.right_neutral id_apply image_subset_iff list.set_map list.simps(8) map_map of_Ev_Ev rangeI trace_to_Nil)
            apply (metis (no_types, lifting) image_subset_iff list.set_map map_Ev_eq_iff map_Ev_of_Ev map_map rangeI)
           apply (smt (verit, del_insts) append.right_neutral list.set_map map_append map_of_Ev_append subset_image_iff top_greatest trace_to_Nil)
          apply (metis (no_types, hide_lams) append.right_neutral list.set_map map_append map_of_Ev_append subset_image_iff top_greatest)
         apply (metis (no_types, hide_lams) append_Nil list.set_map list.simps(8) map_of_Ev_append subset_image_iff top_greatest trace_to_Nil)
        apply (metis (no_types, hide_lams) append_Nil list.set_map list.simps(8) map_of_Ev_append subset_image_iff top_greatest trace_to_Nil)
       apply (metis (no_types, hide_lams) append.right_neutral list.set_map list.simps(8) map_of_Ev_append subset_image_iff top_greatest)
      apply (metis (no_types, hide_lams) Ev_subset_image append_Nil list.set_map map_append map_of_Ev_append top_greatest)
     apply (rename_tac b F tr')
     apply (drule_tac x="map_pfun (\<lambda> x. bind_itree x Q) F" in spec)
     apply (simp)
     apply (metis Int_Un_distrib2 Un_Int_eq(1) bind_Vis disjoint_iff trace_to_bind_left)
    apply (metis (no_types, lifting) map_Ev_of_Ev map_append map_map trace_to_bind)+
  done

lemma "failures(Ret x) = failures(Vis F) \<Longrightarrow> False"
  by (simp add: failures_Ret failures_Vis, auto)

lemma mstep_to_term: "P \<Midarrow>[\<checkmark> v]\<Rightarrow> P' \<longleftrightarrow> (\<exists> n. P = Sils n (Ret v) \<and> P' = deadlock)"
  by (metis append_Nil map_is_Nil_conv mstep_termE mstep_to_def trace_of_Sils trace_to_NilE)

lemma 
  assumes "P \<Midarrow>[a]\<Rightarrow> P'" "a \<notin> \<I>(P)" "is_Vis Q"
  shows "P \<box> Q \<Midarrow>[a]\<Rightarrow> P'"
proof -
  have "stabilises P"
    by (meson assms(1) mstep_stabilises not_Cons_self2)
  then obtain n P'' where P'': "P = Sils n P''" "stable P''"
    by (metis stabilises_def)
  have "P'' \<box> Q \<Midarrow>[a]\<Rightarrow> P'"
  proof (cases P'')
    case (Ret x1)
    then show ?thesis oops

 (*
    next
    case (Sil x2)
    then show ?thesis
      using P'' by force
  next
    case (Vis F)
    with assms(1) P'' obtain e where "a = Ev e" "e \<in> pdom F"
      by (auto simp add: mstep_to_def domIff)
    with assms P'' show ?thesis
      apply (simp)
  oops
*)

lemma 
  assumes "\<I>(P) \<inter> \<I>(Q) = {}"
  shows "failures(P \<box> Q) = {([], X) | X. ([], X) \<in> failures(P) \<inter> failures(Q)}
                         \<union> {(s, X). (s, X) \<in> failures P \<union> failures Q \<and> s \<noteq> []}
                         \<union> {([], X) | X. X \<subseteq> range Ev \<and> (\<exists> v. [\<checkmark> v] \<in> traces(P) \<union> traces(Q))}"
  oops

subsection \<open> Determinism \<close>

definition "deterministic P = (divergences P = {} \<and> (\<forall> s a. s @ [a] \<in> traces(P) \<longrightarrow> (s, {a}) \<notin> failures(P)))"

text \<open> Interaction trees satisfy the CSP definition of determinism. \<close>

lemma div_free_is_determinsitic:
  "div_free P \<Longrightarrow> deterministic P"
  apply (auto simp add: deterministic_def divergences_def traces_def failures_def mstep_to_def refuses_def termination_determinsitic)
  apply (metis div_free_diverge diverges_diverge diverges_implies_equal trace_to_div_free)
  apply (simp add: domD trace_to_determinstic_choice)
  apply (metis event.simps(4) last_map list.simps(8) snoc_eq_iff_butlast)
  apply (metis append_butlast_last_id is_Ret_def trace_to_Ret_end)
  apply (metis Cons_eq_map_D append_eq_map_conv event.simps(4))
  apply (metis Nil_is_append_conv Nil_is_map_conv event.simps(4) last_map last_snoc not_Cons_self2)
  apply (meson trace_to_Ret_excl_Vis)
  apply (metis event.simps(4) trace_last_Ev)+  
  done

end