section \<open> Circus Interaction Tree Semantics \<close>

theory ITree_Circus
  imports "ITree_Deadlock" "Optics.Optics" "Shallow-Expressions.Shallow_Expressions"
begin

subsection \<open> Preliminaries \<close>

datatype ('e, 's) event = Ev (of_Ev: 'e) | Term 's ("\<cmark>")

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
                        (\<exists> tr' x. tr = (map Ev tr') @ [\<cmark>(x)] \<and> P \<midarrow>tr'\<leadsto> Ret x \<and> P' = deadlock))"

lemma mstep_termE [elim]: 
  "\<lbrakk> P \<Midarrow>tr @ [\<cmark>(v)]\<Rightarrow> P'; \<And> tr'. \<lbrakk> tr = map Ev tr'; P \<midarrow>tr'\<leadsto> Ret v; P' = deadlock \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
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

lemma initials_Ret: "\<I>(Ret x) = {\<cmark> x}"
  by (auto simp add: initials_def mstep_to_def)

lemma initials_Sil: "\<I>(Sil P) = \<I>(P)"
  apply (auto simp add: initials_def mstep_to_def)
  apply (metis itree.distinct(5) trace_of_Sils trace_to_SilE trace_to_single_iff)
  apply blast
  done

subsection \<open> Traces \<close>

definition traces :: "('e, 's) itree \<Rightarrow> ('e, 's) trace set" where
"traces P = {map Ev tr | tr. \<exists> P'. P \<midarrow>tr\<leadsto> P'} \<union> {map Ev tr @ [\<cmark>(v)] | tr v. P \<midarrow>tr\<leadsto> Ret v}"

lemma trace_alt_def: "traces P = {s. \<exists> Q. P \<Midarrow>s\<Rightarrow> Q}"
  by (auto simp add: traces_def mstep_to_def)

definition straces :: "('e, 's) ktree \<Rightarrow> ('s \<Rightarrow> ('e, 's) trace set)" ("traces\<^sub>s") where
"straces K = (\<lambda> s. traces (K s))"

lemma Nil_in_traces [simp]: "[] \<in> traces P"
  by (auto simp add: traces_def)

lemma traces_prefix_in_Ev: "tr @ [\<cmark>(v)] \<in> traces(P) \<Longrightarrow> set tr \<subseteq> range Ev"
  by (auto simp add: traces_def)

lemma term_trace_iff [simp]: "tr @ [\<cmark>(v)] \<in> traces(P) \<longleftrightarrow> (set tr \<subseteq> range Ev \<and> P \<midarrow>map of_Ev tr\<leadsto> Ret v)"
  by (auto simp add: traces_def map_idI)

lemma in_tracesI1:
  assumes "P \<midarrow>tr\<leadsto> P'" "t = map Ev tr"
  shows "t \<in> traces(P)"
  using assms traces_def by fastforce

lemma in_tracesE [elim]:
  assumes
  "tr \<in> traces P"
  "\<And> P' tr'. \<lbrakk> tr = map Ev tr'; P \<midarrow>tr'\<leadsto> P' \<rbrakk> \<Longrightarrow> R"
  "\<And> P' tr' v. \<lbrakk> tr = map Ev tr' @ [\<cmark>(v)]; P \<midarrow>tr'\<leadsto> Ret v \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms by (auto simp add: traces_def)

lemma not_in_traces [simp]: "set tr \<subseteq> range Ev \<Longrightarrow> tr \<notin> traces(P) \<longleftrightarrow> \<not> (\<exists> P'. P \<midarrow>map of_Ev tr\<leadsto> P')"
  by (simp add: traces_def, auto)

lemma traces_single_Term: "[\<cmark> s] \<in> traces(P) \<Longrightarrow> \<exists> n. P = Sils n (Ret s)"
  by (auto simp add: traces_def)

lemma traces_Ret: "traces (Ret x) = {[], [\<cmark>(x)]}"
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
  \<union> {tr\<^sub>1 @ tr\<^sub>2 | tr\<^sub>1 tr\<^sub>2. \<exists> v. tr\<^sub>1 @ [\<cmark>(v)] \<in> traces(P) \<and> tr\<^sub>2 \<in> traces(Q v)}"
  apply (auto elim!: in_tracesE trace_to_bindE)
  apply (auto simp add: traces_def)
  apply (metis (no_types, lifting) Nil_is_map_conv append_Nil2 image_subset_iff list.set_map map_of_Ev_append range_eqI)
  apply (metis bind_RetE)
  apply (metis (no_types, lifting) append.right_neutral list.set_map list.simps(8) map_of_Ev_append subset_image_iff top_greatest)
  apply (metis append_Nil2 image_subset_iff list.set_map map_append map_of_Ev_append range_eqI)
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
    assume a: "t\<^sub>1 @ t\<^sub>2 = map Ev tr @ [\<cmark> v]" "P \<midarrow>tr\<leadsto> Ret v"
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
"refuses P B = ((\<exists> F. P = Vis F \<and> B \<inter> Ev ` pdom F = {}) \<or> (\<exists> x. P = Ret x \<and> \<cmark>(x) \<notin> B))"

lemma Ret_refuses [simp]: "Ret x ref B \<longleftrightarrow> \<cmark>(x) \<notin> B"
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
"failures P = {(s, X). \<exists> Q. P \<Midarrow>s\<Rightarrow> Q \<and> Q ref X} \<union> {(s @ [\<cmark>(v)], X) | s v X. \<exists> Q. P \<Midarrow>s @ [\<cmark>(v)]\<Rightarrow> Q}"

lemma in_failuresE [elim]:
  assumes
  "f \<in> failures P"
  \<comment> \<open> The process reaches a visible choice, and is refusing all subsets of possible events \<close>
  "\<And> F B T tr. \<lbrakk> f = (map Ev tr, B); P \<midarrow>tr\<leadsto> Vis F; B \<inter> Ev ` pdom F = {} \<rbrakk> \<Longrightarrow> R"
  \<comment> \<open> The process reaches a termination event, and is refusing all non-termination events \<close>
  "\<And> x B T tr. \<lbrakk> f = (map Ev tr, B - {\<cmark>(x)}); P \<midarrow>tr\<leadsto> Ret x \<rbrakk> \<Longrightarrow> R"
  \<comment> \<open> The process terminates; technically similar to the previous one. \<close>
  "\<And> x B T tr. \<lbrakk> f = (map Ev tr @ [\<cmark> x], B); P \<midarrow>tr\<leadsto> Ret x \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms 
  by (auto simp add: failures_def refuses_def mstep_to_def deadlock_def)
     (metis Diff_insert_absorb map_Ev_of_Ev map_map)

lemma in_failuresI1: "\<lbrakk> P \<midarrow>tr\<leadsto> Vis F; B \<inter> Ev ` pdom(F) = {} \<rbrakk> \<Longrightarrow> (map Ev tr, B) \<in> failures P"
  by (auto simp add: failures_def mstep_to_def)

lemma in_failuresI2: "P \<midarrow>tr\<leadsto> Ret x \<Longrightarrow> (map Ev tr, B - {\<cmark> x}) \<in> failures P"
  by (auto simp add: failures_def mstep_to_def)

lemma in_failures_iff:
  "(tr, B) \<in> failures P \<longleftrightarrow> 
        (\<exists> F tr'. tr = map Ev tr' \<and> P \<midarrow>tr'\<leadsto> Vis F \<and> B \<inter> Ev ` pdom(F) = {})
        \<or> (\<exists> x tr'. tr = map Ev tr' \<and> \<cmark> x \<notin> B \<and> P \<midarrow>tr'\<leadsto> Ret x)
        \<or> (\<exists> x tr'. tr = map Ev tr' @ [\<cmark> x] \<and> P \<midarrow>tr'\<leadsto> Ret x)"
  by (auto simp add: failures_def mstep_to_def refuses_def)
     (metis map_Ev_of_Ev map_map, blast+)

lemma failures_term_iff: 
  "(tr @ [\<cmark>(v)], E) \<in> failures(P) \<longleftrightarrow> (\<exists> Q. P \<Midarrow>tr @ [\<cmark>(v)]\<Rightarrow> Q)"
  by (auto simp add: failures_def)

lemma failures_term_Ev_iff: 
  "(map Ev tr @ [\<cmark>(v)], E) \<in> failures(P) \<longleftrightarrow> P \<midarrow>tr\<leadsto> Ret v"
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
  "failures (Ret v) = {([], X) | X. \<cmark>(v) \<notin> X} \<union> {([\<cmark>(v)], X) | X. True}"
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

lemma dom_bind [simp]: "Map.dom (\<lambda> x. P x \<bind> Q) = {x \<in> Map.dom P. the(P x) \<in> Map.dom Q}"
  by (auto)

lemma refuses_Term_iff: "Q ref (B \<union> range \<cmark>) \<longleftrightarrow> (\<exists>F. Q = Vis F \<and> B \<inter> Ev ` pdom F = {})"
  by (auto simp add: refuses_def)

lemma failures_Term_iff:
  "(map Ev tr, B \<union> range \<cmark>) \<in> failures P \<longleftrightarrow> (\<exists> F. P \<midarrow>tr\<leadsto> Vis F \<and> B \<inter> Ev ` pdom F = {})"
  by (auto simp add: failures_def mstep_to_def refuses_Term_iff)
     (metis event.simps(4) trace_last_Ev)+
  
text \<open> Refusing all termination events \<close>

lemma "(tr, B \<union> range \<cmark>) \<in> failures P \<longleftrightarrow> 
        (\<exists> F tr'. tr = map Ev tr' \<and> P \<midarrow>tr'\<leadsto> Vis F \<and> B \<inter> Ev ` pdom(F) = {})
        \<or> (\<exists> x tr'. tr = map Ev tr' @ [\<cmark> x] \<and> P \<midarrow>tr'\<leadsto> Ret x)"
  apply (auto simp add: failures_def mstep_to_def refuses_def)
  apply (metis inf_sup_distrib2 map_Ev_of_Ev map_map sup_eq_bot_iff)
  apply (metis Vis_refuses refuses_Term_iff)
  done

lemma failures_bind: 
  "failures (P \<bind> Q) = 
    {(s, X). set s \<subseteq> range Ev \<and> (s, X \<union> (range Term)) \<in> failures(P)}
    \<union> {(s @ t, X) | s t X. \<exists> v. s @ [\<cmark>(v)] \<in> traces(P) \<and> (t, X) \<in> failures(Q v)}"
  apply (rule set_eqI)
  apply (clarify)
  apply (simp add: in_failures_iff)
  apply (auto elim!: trace_to_bindE bind_VisE')
            apply (meson Vis_refuses refuses_Term_iff)
           apply (metis (no_types, lifting) image_subset_iff list.set_map map_Ev_eq_iff map_Ev_of_Ev map_map rangeI)
          apply (meson bind_RetE')
         apply (metis (no_types, hide_lams) append_Nil2 image_subset_iff list.set_map list.simps(8) map_of_Ev_append rangeI)
        apply (metis bind_RetE)
       apply (metis Ev_subset_image UNIV_I append.right_neutral list.set_map map_append map_of_Ev_append subsetI)
      apply (metis Ev_subset_image UNIV_I append_Nil2 list.set_map map_append map_of_Ev_append subsetI)
     apply (rename_tac b F tr')
     apply (drule_tac x="map_pfun (\<lambda> x. bind_itree x Q) F" in spec)
     apply (simp)
     apply (metis Int_Un_distrib2 Un_Int_eq(1) bind_Vis disjoint_iff trace_to_bind_left)
    apply (metis (no_types, lifting) map_Ev_of_Ev map_append map_map trace_to_bind)+
  done

lemma "failures(Ret x) = failures(Vis F) \<Longrightarrow> False"
  by (simp add: failures_Ret failures_Vis, auto)

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

subsection \<open> Main Operators \<close>

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

lemma "test (\<lambda> s. False) = Stop"
  by (simp add: test_def)

definition assigns :: "'s subst \<Rightarrow> ('e, 's) ktree" where
"assigns \<sigma> = (\<lambda> s. Ret (\<sigma> s))"

syntax
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  ("'(_') := '(_')")  
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=" 62)
  "_mk_usubst"      :: "svids \<Rightarrow> uexprs \<Rightarrow> 's subst"

translations
  "_assignment xs vs" => "CONST assigns (_mk_usubst [\<leadsto>] xs vs)"
  "_assignment x v" <= "CONST assigns (CONST subst_upd id\<^sub>s x v)"

corec loop :: "('e, 'r) ktree \<Rightarrow> ('e, 'r) ktree" where
"loop P e = Sil (P e \<bind> loop P)"

definition inp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 'a) itree" where
"inp c = Vis (pfun_of_map (\<lambda> e. match\<^bsub>c\<^esub> e \<bind> Some \<circ> Ret))"

definition inp_in :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a list \<Rightarrow> ('e, 'a) itree" where
"inp_in c B = Vis (pfun_of_alist [(build\<^bsub>c\<^esub> v, Ret v). v \<leftarrow> B])"

lemma traces_inp: "wb_prism c \<Longrightarrow> traces (inp c) = {[]} \<union> {[Ev (build\<^bsub>c\<^esub> v)] | v. True} \<union> {[Ev (build\<^bsub>c\<^esub> v), \<cmark> v] | v. True}" 
  apply (simp add: inp_def traces_Vis traces_Ret)
  apply (auto simp add: inp_def bind_eq_Some_conv traces_Ret domIff pdom.abs_eq  elim!: in_tracesE trace_to_VisE)
   apply (metis (no_types, lifting) wb_prism_def)
  apply (force simp add: traces_Ret)
  done 

definition input :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 's) ktree) \<Rightarrow> ('e, 's) ktree" where
"input c P = (\<lambda> s. inp c \<bind> (\<lambda> x. P x s))"

syntax "_input" :: "id \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic" ("_?'(_') \<rightarrow> _" [90, 0, 91] 91)
translations "c?(x) \<rightarrow> P" == "CONST input c (\<lambda> x. P)"

definition outp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a \<Rightarrow> ('e, unit) itree" where
"outp c v = Vis (pfun_of_alist [(build\<^bsub>c\<^esub> v, Ret())])"

definition "output" :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a \<Rightarrow> ('e, 's) ktree \<Rightarrow> ('e, 's) ktree" where
"output c e P = (\<lambda> s. outp c e \<then> Ret s)"

syntax "_output" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_!'(_') \<rightarrow> _" [90, 0, 91] 91)
translations "c!(e) \<rightarrow> P" == "CONST output c e P"

definition map_prod :: "('a \<Zpfun> 'b) \<Rightarrow> ('a \<Zpfun> 'b) \<Rightarrow> ('a \<Zpfun> 'b)" (infixl "\<odot>" 100) where
"map_prod f g = (pdom(g) \<Zndres> f) + (pdom(f) \<Zndres> g)"

lemma map_prod_commute: "x \<odot> y = y \<odot> x"
  apply (auto simp add: fun_eq_iff map_prod_def option.case_eq_if)
  apply (metis Compl_iff IntD1 IntD2 pdom_pdom_res pfun_plus_commute_weak)
  done

lemma map_prod_empty [simp]: "x \<odot> {}\<^sub>p = x" "{}\<^sub>p \<odot> x = x"
  by (simp_all add: map_prod_def)

code_datatype pfun_of_alist pfun_of_map

lemma map_prod_merge: 
  "f(x \<mapsto> v)\<^sub>p \<odot> g = 
  (if (x \<notin> pdom(g)) then (f \<odot> g)(x \<mapsto> v)\<^sub>p else {x} \<Zndres> (f \<odot> g))"
  by (auto simp add: map_prod_def)
     (metis (no_types, hide_lams) Compl_Un insert_absorb insert_is_Un)

definition seq :: "('e, 's) ktree \<Rightarrow> ('e, 's) ktree \<Rightarrow> ('e, 's) ktree" where
"seq P Q = (\<lambda> s. P s \<bind> Q)"

text \<open> This is like race-free behaviour \<close>

primcorec choice :: "('e, 'a) itree \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'a) itree" (infixl "\<diamond>" 59) where
"choice P Q =
   (case (P, Q) of 
      (Vis F, Vis G) \<Rightarrow> Vis (F \<odot> G) |
      (Sil P', _) \<Rightarrow> Sil (choice P' Q) |
      (_, Sil Q') \<Rightarrow> Sil (choice P Q') |
      (Ret x, Ret y) \<Rightarrow> if (x = y) then Ret x else Vis {}\<^sub>p | 
      (Ret v, Vis _)   \<Rightarrow> Ret v | \<comment> \<open> Needs more thought \<close>
      (Vis _, Ret v)   \<Rightarrow> Ret v
   )"

lemma choice_diverge: "choice diverge P = diverge"
  by (coinduction arbitrary: P, auto, metis diverge.code itree.simps(11))

text \<open> External Choice test cases \<close>

lemma choice_Sils: "choice (Sils m P) Q = Sils m (choice P Q)"
  by (induct m, simp_all add: choice.code)

lemma choice_Sil_stable: "stable P \<Longrightarrow> choice P (Sil Q) = Sil (choice P Q)"
  by (cases P, simp_all add: choice.code)

lemma choice_Sils_stable: "stable P \<Longrightarrow> choice P (Sils m Q) = Sils m (choice P Q)"
  by (induct m, simp_all add: choice_Sil_stable)

lemma choice_Sils': "choice P (Sils m Q) = Sils m (choice P Q)"
proof (cases "divergent P")
  case True
  then show ?thesis
    by (metis Sils_diverge choice_diverge diverges_then_diverge) 
next
  case False
  then obtain n P' where "Sils n P' = P" "stable P'"
    using stabilises_def by blast
  then show ?thesis
    by (metis Sils_Sils add.commute choice_Sils choice_Sils_stable)
qed

lemma 
  assumes "P \<Midarrow>[a]\<Rightarrow> P'" "\<I>(P) \<inter> \<I>(Q) = {}" "is_Vis Q"
  shows "P \<diamond> Q \<Midarrow>[a]\<Rightarrow> P'"
proof -
  have "stabilises P"
    by (meson assms(1) mstep_stabilises not_Cons_self2)
  then obtain n P'' where P'': "P = Sils n P''" "stable P''"
    by (metis stabilises_def)
  have "P'' \<diamond> Q \<Midarrow>[a]\<Rightarrow> P'"
  proof (cases P'')
    case (Ret x1)
    then show ?thesis sorry
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

lemma 
  assumes "\<I>(P) \<inter> \<I>(Q) = {}"
  shows "failures(P \<diamond> Q) = {([], X) | X. ([], X) \<in> failures(P) \<inter> failures(Q)}
                         \<union> {(s, X). (s, X) \<in> failures P \<union> failures Q \<and> s \<noteq> []}
                         \<union> {([], X) | X. X \<subseteq> range Ev \<and> (\<exists> v. [\<cmark> v] \<in> traces(P) \<union> traces(Q))}"
  oops

  term "{X \<mapsto> Ret a}\<^sub>p"

lemma "X \<noteq> Y \<Longrightarrow> choice (Vis {X \<mapsto> Ret a}\<^sub>p) (Vis {Y \<mapsto> Ret b}\<^sub>p) = 
       Vis {X \<mapsto> Ret a, Y \<mapsto> Ret b}\<^sub>p"
  by (auto simp add: choice.code map_prod_merge pfun_upd_comm)

lemma "choice (Vis {X \<mapsto> Ret a}\<^sub>p) (Vis {X \<mapsto> Ret b}\<^sub>p) = 
       deadlock"
  by (simp add: choice.code deadlock_def map_prod_merge)

lemma "X \<noteq> Y \<Longrightarrow> choice (Sil (Vis {X \<mapsto> Ret a}\<^sub>p)) (Sil (Vis {Y \<mapsto> Ret b}\<^sub>p)) = 
       Sil (Sil (Vis {X \<mapsto> Ret a, Y \<mapsto> Ret b}\<^sub>p))"
  by (simp add: choice.code map_prod_merge pfun_upd_comm)

text \<open> This requires weak bisimulation \<close>

lemma "\<And> P. (X = choice P P \<and> Y = P) \<or> (X = Y) \<Longrightarrow> X = Y"
  apply (coinduction arbitrary: X Y)
  apply (auto simp add: itree.case_eq_if itree.distinct_disc(1))
  oops

lemma trace_of_deadlock: "deadlock \<midarrow>t\<leadsto> P \<Longrightarrow> (t, P) = ([], deadlock)"
  by (auto simp add: deadlock_def)

lemma is_Sil_choice: "is_Sil (choice P Q) = (is_Sil P \<or> is_Sil Q)"
  using itree.exhaust_disc by (auto)

lemma stable_deadlock [simp]: "stable deadlock"
  by (simp add: deadlock_def)

lemma choice_deadlock [simp]: "choice deadlock P = P"
proof (coinduction arbitrary: P rule: itree_strong_coind)
  case wform
then show ?case
  by (simp add: deadlock_def) 
next
  case (Ret x y)
  then show ?case
    by (metis (no_types, lifting) choice.simps(4) deadlock_def is_Vis_def itree.disc(1) itree.sel(1) itree.simps(12) prod.sel(1) snd_conv) 
next
  case (Sil P' Q' P)
  then show ?case
    by (smt choice.simps(5) deadlock_def fst_conv itree.case_eq_if itree.disc(6) itree.disc(9) itree.discI(2) itree.sel(2) itree.simps(11) snd_conv)
next
  case Vis
  then show ?case
    by (metis choice.simps(6) deadlock_def itree.disc(9) itree.sel(3) itree.simps(12) map_prod_empty(2) prod.sel(1) snd_conv) 
qed

lemma choice_deadlock' [simp]: "choice P deadlock = P"
proof (coinduction arbitrary: P rule: itree_strong_coind)
  case wform
  then show ?case
  by (simp add: deadlock_def) 
next
  case Ret
  then show ?case
    by (metis (no_types, lifting) choice.simps(4) deadlock_def itree.case_eq_if itree.disc(1) itree.disc(9) itree.sel(1) prod.sel(1) snd_conv stable_deadlock) 
next
  case Sil
  then show ?case
    by (metis choice.sel(2) itree.disc(5) itree.sel(2) itree.simps(11) prod.sel(1))
next
  case Vis
  then show ?case
    by (metis choice.simps(6) deadlock_def itree.disc(9) itree.sel(3) itree.simps(12) map_prod_empty(1) prod.sel(1) snd_conv)
qed

lemma choice_Sil': "choice P (Sil Q) = choice (Sil P) Q"
proof (coinduction arbitrary: P Q rule: itree_strong_coind)
case wform
  then show ?case
    by (meson is_Sil_choice itree.disc(2) itree.disc(8) itree.distinct_disc(1) itree.distinct_disc(6) itree.exhaust_disc)
next
  case Ret
  then show ?case
    by (metis is_Sil_choice itree.disc(4) itree.disc(5)) 
next
  case (Sil P Q P' Q')
  then show ?case
    by (metis (no_types, lifting) choice.sel(2) choice_Sil_stable itree.collapse(2) itree.disc(5) itree.sel(2) itree.simps(11) prod.sel(1))    
next
  case Vis
  then show ?case
    by (metis is_Sil_choice itree.disc(5) itree.disc(6)) 
qed

lemma choice_unstable: "unstable P \<Longrightarrow> choice P Q = Sil (choice (un_Sil P) Q)"
  by (metis (no_types, lifting) choice.ctr(2) itree.collapse(2) itree.simps(11) prod.sel(1))

lemma choice_unstable': "unstable Q \<Longrightarrow> choice P Q = Sil (choice P (un_Sil Q))"
  by (metis choice_Sil' choice_Sil_stable choice_unstable itree.collapse(2))

lemma choice_commutative:
  "choice P Q = choice Q P"
proof (coinduction arbitrary: P Q rule: itree_coind)
  case wform
  then show ?case
    by (metis choice.disc_iff(1) choice.simps(3) is_Sil_choice prod.sel(1) snd_conv)
next
  case Ret
  then show ?case
    by (smt choice.disc_iff(1) choice.simps(3) choice.simps(4) itree.case_eq_if itree.disc(7) itree.sel(1) prod.sel(1) snd_conv un_Ret_def)
next
  case (Sil P Q P' Q')
  then show ?case
  proof (cases "unstable P'")
    case True
    with Sil have "P = choice (un_Sil P') Q'" "Q = choice Q' (un_Sil P')"
      by (simp_all add: choice_unstable choice_unstable')
    thus ?thesis
      by blast
  next
    case False
      then show ?thesis
        by (metis Sil(1) Sil(2) choice_Sil_stable choice_deadlock' choice_unstable is_Sil_choice itree.discI(2) itree.sel(2))
  qed
next
  case Vis
  then show ?case
    apply (auto)
    apply (smt choice.simps(3) choice.simps(6) itree.case_eq_if itree.disc(9) itree.sel(3) map_prod_commute prod.sel(1) snd_conv)
     apply (smt choice.simps(3) choice.simps(6) itree.case_eq_if itree.disc(9) itree.sel(3) map_prod_commute prod.sel(1) snd_conv)
(*
    apply (subgoal_tac "G x = Some y")
    apply (metis choice_deadlock choice_deadlock' option.sel)
    apply (smt choice.simps(3) choice.simps(6) itree.case_eq_if itree.disc(9) itree.sel(3) map_prod_commute prod.sel(1) snd_conv)
    done
*)
    oops

datatype (discs_sels) ('a, 'b) andor = Left 'a | Right 'b | Both "'a \<times> 'b"

term case_andor

term map2

term map_pfun

(* Use combine to achieve *)

definition scomp :: "('a \<Zpfun> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<Zpfun> 'c) \<Rightarrow> ('a \<Zpfun> ('b, 'c) andor)" where
"scomp f A g = 
  map_pfun Both (A \<Zdres> pfuse f g) + map_pfun Left ((A \<union> pdom(g)) \<Zndres> f) + map_pfun Right ((A \<union> pdom(f)) \<Zndres> g)"

(*
pfun_of_map (\<lambda> x. case (pfun_lookup f x, pfun_lookup g x) of
                                 (Some P, Some Q) \<Rightarrow> 
                                    (if (x \<in> A) then Some (Both (P, Q)) else None) |
                                 (Some P, None) \<Rightarrow> (if (x \<notin> A) then Some (Left P) else None) |
                                 (None, Some Q) \<Rightarrow> (if (x \<notin> A) then Some (Right Q) else None) |
                                 _ \<Rightarrow> None)"
*)

corec par :: "('e, 'a) itree \<Rightarrow> 'e set \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'a) itree" where
"par P A Q =
   (case (P, Q) of 
      (Vis F, Vis G) \<Rightarrow> 
        Vis (map_pfun (case_andor (\<lambda> P'. par P' A (Vis G)) (\<lambda> Q'. par (Vis F) A Q') (\<lambda> (P', Q'). par P' A Q')) 
                      (scomp F A G)) |
      (Sil P', _) \<Rightarrow> Sil (par P' A Q) |
      (_, Sil Q') \<Rightarrow> Sil (par P A Q') |
      (Ret x, Ret y) \<Rightarrow> if (x = y) then Ret x else Vis {}\<^sub>p | 
      (Ret v, Vis _)   \<Rightarrow> Ret v | \<comment> \<open> Needs more thought \<close>
      (Vis _, Ret v)   \<Rightarrow> Ret v
   )"

corec hide :: "('e, 'a) itree \<Rightarrow> 'e set \<Rightarrow> ('e, 'a) itree" where
"hide P A = 
  (case P of
    Vis F \<Rightarrow> if (card (A \<inter> pdom(F)) = 1) then Sil (hide (F (the_elem (A \<inter> pdom(F)))) A) 
             else if (A \<inter> pdom(F)) = {} then Vis (map_pfun (\<lambda> X. hide X A) F)
             else deadlock |
    Sil P \<Rightarrow> Sil (hide P A) |
    Ret x \<Rightarrow> Ret x)"

definition extchoice :: "('e, 's) ktree \<Rightarrow> ('e, 's) ktree \<Rightarrow> ('e, 's) ktree" (infixl "\<box>" 59) where
"extchoice P Q \<equiv> (\<lambda> s. choice (P s) (Q s))"

lemma extchoice_Stop: "Stop \<box> P = P"
  by (auto simp add: extchoice_def fun_eq_iff)

lemma extchoice_Div: "Div \<box> P = Div"
  by (simp add: choice_diverge extchoice_def)


subsection \<open> Examples \<close>

chantype Chan =
  Input :: integer
  Output :: integer
  State :: "integer list"

corec speak :: "('e, 's) itree" where
"speak = Vis (map_pfun (\<lambda> _. Sil speak) pId)"

lemma "div_free speak"
  (* We need to find the right pattern to find divergence freedom using Tarki theorem *)
  apply (coinduct rule: div_free_coind[where \<phi>="\<lambda> x. \<exists> n. x = Sils n speak"])
  (* We need to show two things: (1) the our target process fits the pattern, and
  (2) that it is a prefixed-point. *)
  apply (rule_tac x="0" in exI)
  apply (simp)
  apply (auto)
  apply (induct_tac n)
  apply (simp)
  apply (subst speak.code) back
   apply (rule vis_stbs)
   apply (simp add: pfun.set_map)
  apply (rule_tac x="1" in exI, simp)
  apply (simp)
  apply (rule sil_stbs)
  apply (simp)
  done

definition "echo = loop (\<lambda>_. do { i \<leftarrow> inp Input; outp Output i })"

lemma "echo () \<midarrow>[build\<^bsub>Input\<^esub> 1, build\<^bsub>Output\<^esub> 1]\<leadsto> echo ()"
  apply (subst echo_def)
  apply (subst loop.code)
  apply (subst echo_def[THEN sym])
  apply (rule trace_to_Sil)
  apply (simp add: inp_def)
  apply (subst bind_itree.code)
  oops

definition "buffer = 
  loop (\<lambda> s. choice (do { i \<leftarrow> inp_in Input [0,1,2,3]; Ret (s @ [i]) }) 
                    (choice (do { test (\<lambda> s. length s > 0) s;  
                                  outp Output (hd s); 
                                  Ret (tl s)
                                })
                            (do { outp State s; Ret s })
       ))"

definition "mytest = loop (Input?(i) \<rightarrow> (\<lambda> s. Ret (s @ [i])) \<box> Stop)"

definition "bitree = loop (\<lambda> s. inp_in Input [0,1,2,3] \<bind> outp Output)"

chantype schan = 
  a :: unit b :: unit c :: unit

(*
definition "partest = 
  (\<lambda> s. par (loop (\<lambda> s. (do { outp a (); outp b (); Ret () })) s) {build\<^bsub>b\<^esub> ()} 
        (loop (\<lambda> s. (do { outp b (); outp c (); Ret () })) s)) "
*)

definition "partest = 
  (\<lambda> s. hide
        (par (loop (\<lambda> s. (do { outp a (); outp b (); Ret () })) s) {build\<^bsub>b\<^esub> ()} 
             (loop (\<lambda> s. (do { outp b (); outp c (); Ret () })) s)) {build\<^bsub>b\<^esub> ()})" 


subsection \<open> Code Generation \<close>

export_code mytest bitree buffer partest diverge deadlock in Haskell module_name ITree_Examples (string_classes)

end