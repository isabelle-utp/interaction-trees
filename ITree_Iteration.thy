theory ITree_Iteration
  imports ITree_Divergence
begin

subsection \<open> Strong Traces \<close>

inductive strace_to :: "('a, 'b) itree \<Rightarrow> 'a option list \<Rightarrow> ('a, 'b) itree \<Rightarrow> bool" ("_ \<midarrow>_\<rightarrow> _" [55, 0, 55] 55) where
strace_to_Nil [intro!]: "P \<midarrow>[]\<rightarrow> P" | 
strace_to_Sil [intro!]: "P \<midarrow>tr\<rightarrow> P' \<Longrightarrow> Sil P \<midarrow>None # tr\<rightarrow> P'" |
strace_to_Vis [intro!]: "\<lbrakk> e \<in> pdom F; F e \<midarrow>tr\<rightarrow> P' \<rbrakk> \<Longrightarrow> Vis F \<midarrow>Some e # tr\<rightarrow> P'"

inductive_cases
  strace_NilE [elim!]: "P \<midarrow>[]\<rightarrow> P'" and
  strace_singleE [elim!]: "P \<midarrow>[e]\<rightarrow> P'" and
  strace_Cons_NoneE [elim!]: "P \<midarrow>None # tr\<rightarrow> P'" and
  strace_Cons_SomeE [elim!]: "P \<midarrow>Some e # tr\<rightarrow> P'" and
  strace_SilE [elim!]: "\<tau> P \<midarrow>tr\<rightarrow> P'" and
  strace_RetE [elim!]: "\<checkmark> x \<midarrow>tr\<rightarrow> P"

lemma strace_to_Sils [intro!]: "P \<midarrow>tr\<rightarrow> P' \<Longrightarrow> Sils n P \<midarrow>(replicate n None) @ tr\<rightarrow> P'"
  by (induct n, auto)

lemma trace_then_strace:
  assumes "P \<midarrow>tr\<leadsto> P'"
  shows "(\<exists> tr'. P \<midarrow>tr'\<rightarrow> P' \<and> tr = [x. Some x \<leftarrow> tr'])"
using assms proof (induct tr arbitrary: P)
  case Nil
  then obtain n where "P = Sils n P'"
    by (meson trace_to_NilE)
  then show ?case
    using strace_to_Nil strace_to_Sils by fastforce
next
  case (Cons a tr)
  then obtain n F where P: "P = Sils n (Vis F)" "a \<in> pdom(F)"
    by (meson trace_to_ConsE trace_to_singleE)
  moreover then obtain tr' where tr': "F a \<midarrow>tr'\<rightarrow> P'" "tr = [x. Some x \<leftarrow> tr']"
    using Cons.hyps Cons.prems by auto
  ultimately show ?case
    by (rule_tac x="replicate n None @ Some a # tr'" in exI, auto)
qed

lemma strace_then_trace:
  assumes "P \<midarrow>tr\<rightarrow> P'" 
  shows "P \<midarrow>[x. Some x \<leftarrow> tr]\<leadsto> P'"
using assms by (induct rule: strace_to.induct, auto)

lemma strace_to_ConsE:
  assumes "P \<midarrow>x # xs\<rightarrow> Q" 
  obtains P' where "P \<midarrow>[x]\<rightarrow> P'" "P' \<midarrow>xs\<rightarrow> Q"
  using assms 
proof -
  have "\<And> tr. P \<midarrow>tr\<rightarrow> Q \<Longrightarrow> tr \<noteq> [] \<longrightarrow> (\<exists>P'. P \<midarrow>[hd tr]\<rightarrow> P' \<and> P' \<midarrow>tl tr\<rightarrow> Q)"
  proof -
    fix tr
    assume "P \<midarrow>tr\<rightarrow> Q"
    thus "tr \<noteq> [] \<longrightarrow> (\<exists>P'. P \<midarrow>[hd tr]\<rightarrow> P' \<and> P' \<midarrow>tl tr\<rightarrow> Q)"
      by (induct rule: strace_to.induct, auto)
  qed
  thus ?thesis
    by (metis assms list.distinct(1) list.sel(1) list.sel(3) that)
qed

lemma strace_to_bindE [elim, consumes 1, case_names left right, induct pred: "HOL.eq"]:
  assumes 
    "(P \<bind> Q) \<midarrow>tr\<rightarrow> Q'"
    "\<And> P'. \<lbrakk> P \<midarrow>tr\<rightarrow> P'; Q' = (P' \<bind> Q) \<rbrakk> \<Longrightarrow> thesis"
    "\<And> x tr\<^sub>1 tr\<^sub>2. \<lbrakk> P \<midarrow>tr\<^sub>1\<rightarrow> Ret x; Q x \<midarrow>tr\<^sub>2\<rightarrow> Q'; tr = tr\<^sub>1 @ tr\<^sub>2 \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
  using assms proof (induct tr arbitrary: P Q Q')
  case Nil
  then show ?case by (auto elim: strace_NilE)
next
  case (Cons e tr)
  from Cons(2) obtain PQ' where "(P \<bind> Q) \<midarrow>[e]\<rightarrow> PQ'" "PQ' \<midarrow>tr\<rightarrow> Q'"
    by (meson strace_to_ConsE)
  then show ?case
    thm Cons
    using Cons.prems(2,3) apply (auto elim!: bind_SilE bind_VisE Cons(1))
    apply (metis append_Cons strace_to_Sil)
    apply (metis append_Nil strace_to_Nil strace_to_Sil)
    using Cons.prems(2) apply blast
    apply (metis append_Cons strace_to_Vis)
    apply (metis Cons.prems(1) append_Nil bind_Ret strace_to_Nil)
    done
qed

subsection \<open> Power \<close>

overloading
  itreepow \<equiv> "compow :: nat \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree"
begin

fun itreepow :: "nat \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
"itreepow 0 P = Ret" |
"itreepow (Suc n) P = P ;; itreepow n P"

end

subsection \<open> Chains \<close>

locale itree_chain =
  fixes P :: "('e, 's) htree" \<comment> \<open> The loop body \<close>
  and s s' :: "'s" \<comment> \<open> Initial and final state \<close>
  and chn :: "('e list \<times> 's) list" \<comment> \<open> The chain \<close>
  assumes length_chain: "length chn > 0" 
  and last_st: "snd (last chn) = s'"
  and chain_start: "P s \<midarrow>fst (hd chn)\<leadsto> Ret (snd (hd chn))"
  and chain_iter: "\<forall> i < length chn - 1. P (snd (chn ! i)) \<midarrow>fst (chn ! (i + 1))\<leadsto> Ret (snd (chn ! (i + 1)))"

lemma itree_chain_ConsI:
  assumes "itree_chain P s\<^sub>0 s' chn" "P s \<midarrow>es\<leadsto> \<checkmark> s\<^sub>0"
  shows "itree_chain P s s' ((es, s\<^sub>0) # chn)"
proof -
  interpret ichain: itree_chain P s\<^sub>0 s' chn
    by (simp add: assms)
  show ?thesis
    apply (unfold_locales, auto simp add: ichain.last_st assms(2))
    using ichain.length_chain apply blast
    apply (metis (no_types, lifting) add.commute add_diff_inverse_nat add_less_cancel_left hd_conv_nth ichain.chain_iter ichain.chain_start ichain.length_chain length_greater_0_conv less_one neq0_conv nth_Cons' snd_conv)
    done
qed
  
subsection \<open> Iteration \<close>

text \<open> For now we support only basic tail-recursive iteration. \<close>

corec iterate :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
"iterate b P s = (if (b s) then (P s \<bind> (\<tau> \<circ> (iterate b P))) else Ret s)"

abbreviation "loop \<equiv> iterate (\<lambda> s. True)"

abbreviation "iter P \<equiv> loop (\<lambda> _. P) ()"

lemma iterate_cond_false [simp]:
  "\<not> (b s) \<Longrightarrow> iterate b P s = Ret s"
  by (simp add: iterate.code)

lemma iterate_body_nonterminates:
  assumes "nonterminates (P s)" "b s"
  shows "nonterminates (iterate b P s)"
  by (simp add: assms iterate.code)

lemma loop_unfold: "loop P = P ;; (\<tau> \<circ> loop P)"
  by (simp add: seq_itree_def kleisli_comp_def fun_eq_iff iterate.code)

lemma loop_Ret: "loop Ret = (\<lambda> s. diverge)"
  by (metis Sil_nfp_stabilises bind_Ret comp_apply diverges_then_diverge iterate.code)

lemma iterate_Ret_dest:
  "Ret x = iterate b P s \<Longrightarrow> (\<not> (b s) \<and> x = s)"
  apply (cases "P s")
  apply (metis bind_Ret comp_apply iterate.code itree.distinct(1) itree.sel(1))
  apply (metis bind_itree.disc_iff(1) iterate.code itree.disc(2) itree.discI(1) itree.inject(1))
  apply (metis bind_Vis iterate.code itree.distinct(3) itree.inject(1))
  done

lemma iterate_RetE:
  assumes "iterate b P s = Ret x" "\<lbrakk> \<not> (b s); x = s \<rbrakk> \<Longrightarrow> Q"
  shows Q
  by (metis assms iterate_Ret_dest)

lemma iterate_RetE':
  assumes "Ret x = iterate b P s" "\<lbrakk> \<not> (b s); x = s \<rbrakk> \<Longrightarrow> Q"
  shows Q
  by (metis assms iterate_Ret_dest)

lemma iterate_Sil_dest: 
  "\<tau> P' = iterate b P s \<Longrightarrow> (b s \<and> ((\<exists> s'. P s = Ret s' \<and> P' = iterate b P s') \<or> (\<exists> P''. P s = \<tau> P'' \<and> P' = (P'' \<bind> \<tau> \<circ> iterate b P))))"
  apply (cases "P s")
  apply (simp_all)
  apply (metis bind_Ret comp_apply iterate.code itree.distinct(1) itree.sel(2))
  apply (metis bind_Sil iterate.code itree.distinct(1) itree.inject(2))
  apply (metis bind_Vis iterate.code itree.distinct(1) itree.distinct(5))
  done

lemma iterate_SilE:
  assumes "\<tau> P = iterate b Q s"
    "\<And> s'. \<lbrakk> b s; Q s = Ret s'; P = iterate b Q s' \<rbrakk> \<Longrightarrow> R"
    "\<And> P'. \<lbrakk> b s; Q s = \<tau> P' \<and> P = (P' \<bind> \<tau> \<circ> iterate b Q) \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms iterate_Sil_dest)

lemma iterate_Vis_dest:
  "Vis F = iterate b Q s \<Longrightarrow> b s \<and> (\<exists> G. Q s = Vis G \<and> F = (map_pfun (\<lambda> x. bind_itree x (\<tau> \<circ> iterate b Q)) G))"
  apply (cases "Q s")
  apply (simp_all)
  apply (metis bind_Ret comp_apply iterate.code itree.simps(7) itree.simps(9))
  apply (metis bind_Sil iterate.code itree.distinct(3) itree.distinct(5))
  apply (metis bind_Vis iterate.code itree.inject(3) itree.simps(7))
  done

lemma iterate_VisE:
  assumes "Vis F = iterate b Q s"
    "\<And> G. \<lbrakk> b s; Q s = Vis G; F = (map_pfun (\<lambda> x. bind_itree x (\<tau> \<circ> iterate b Q)) G) \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms(1) assms(2) iterate_Vis_dest)

lemma itree_chan_singleton_dest [dest!]: 
  assumes "itree_chain P s s' [x]" 
  shows "P s \<midarrow>fst x\<leadsto> \<checkmark> s' \<and> snd x = s'"
proof -
  interpret chn: itree_chain P s s' "[x]"
    by (simp add: assms)
  from chn.chain_start show ?thesis
    using chn.last_st by auto
qed

lemma itree_chain_Cons_dest:
  assumes "itree_chain P s s' ((es\<^sub>1, s\<^sub>0) # chn)" "length chn > 0"
  shows "itree_chain P s\<^sub>0 s' chn"
proof -
  interpret chn: itree_chain P s s' "(es\<^sub>1, s\<^sub>0) # chn"
    by (simp add: assms)
  from assms(2) show ?thesis
    apply (unfold_locales, auto)
    using chn.last_st apply auto[1]
    using chn.chain_iter hd_conv_nth apply fastforce
    apply (metis (no_types, opaque_lifting) One_nat_def Suc_eq_plus1 Suc_less_eq Suc_pred assms(2) chn.chain_iter diff_Suc_Suc diff_zero list.size(4) nth_Cons_Suc)
    done
qed

lemma iterate_trace_to:
  assumes "P s \<midarrow>es \<leadsto> Ret s'" "b s"
  shows "iterate b P s \<midarrow>es\<leadsto> iterate b P s'"
proof -
  have "(P s \<bind> \<tau> \<circ> iterate b P) \<midarrow>es\<leadsto> (Ret s' \<bind> \<tau> \<circ> iterate b P)"
    by (meson assms(1) trace_to_bind_left)
  thus ?thesis
    by (auto simp add: iterate.code assms)
qed

lemma iterate_term_once:
  assumes "P s \<midarrow>es \<leadsto> Ret s'" "b s" "\<not> b s'"
  shows "iterate b P s \<midarrow>es\<leadsto> Ret s'"
  by (metis assms(1) assms(2) assms(3) iterate.code iterate_trace_to)

lemma iterate_chain_terminates:
  assumes "itree_chain P s s' chn" "b s" "\<forall> i < length chn - 1. b (snd (chn ! i))" "\<not> b s'"
  shows "iterate b P s \<midarrow>concat (map fst chn)\<leadsto> Ret s'"
using assms proof (induct chn arbitrary: s)
  case Nil
  then interpret chn: itree_chain P s s' "[]"
    by simp
  show ?case
    using chn.length_chain by blast    
next
  case (Cons ec chn)
  show ?case
  proof (cases "chn = []")
    case True
    thus ?thesis
      using Cons by (auto, meson iterate_term_once)
  next
    case False
    then interpret chn: itree_chain P s s' "ec # chn"
      by (simp add: Cons.prems(1))
    have chn': "itree_chain P (snd ec) s' chn"
      by (metis Cons.prems(1) False itree_chain_Cons_dest length_greater_0_conv prod.exhaust_sel)
    have "P s \<midarrow>fst ec\<leadsto> Ret (snd ec)"
      using chn.chain_start by auto
    hence "iterate b P s \<midarrow>fst ec\<leadsto> iterate b P (snd ec)"
      by (simp add: Cons.prems(2) iterate_trace_to)
    moreover have "b (snd ec)"
      by (metis Cons.prems(3) chn' itree_chain.length_chain length_tl list.sel(3) nth_Cons_0)
    ultimately show ?thesis
      apply (simp, rule_tac trace_to_trans)
       apply (auto)
      apply (metis Cons.hyps Cons.prems(3) One_nat_def Suc_eq_plus1 Suc_pred assms(4) chn' diff_Suc_1 itree_chain_def list.size(4) not_less_eq nth_Cons_Suc)
      done
  qed
qed

lemma iterate_body_Ret:
  assumes "iterate b P s \<midarrow>[]\<leadsto> Ret s'" "b s"
  obtains s\<^sub>0 where "P s \<midarrow>[]\<leadsto> Ret s\<^sub>0"
  using assms
  by (auto elim!: bind_RetE trace_to_bindE simp add: iterate.code)

lemma iterate_body_countdown:
  assumes "iterate b P s = Sils n (\<checkmark> s')" "b s"
  obtains m s\<^sub>0 where "0 < n" "m \<le> n" "P s = Sils m (Ret s\<^sub>0)" "iterate b P s\<^sub>0 = Sils (n - m - 1) (\<checkmark> s')"
proof -
  from assms obtain m s\<^sub>0 where "m \<le> n" "P s = Sils m (\<checkmark> s\<^sub>0)" "Sil (iterate b P s\<^sub>0) = Sils (n - m) (\<checkmark> s')"
    by (auto elim!: bind_SilsE simp add: iterate.code)
  moreover have "0 < n"
    by (metis Sils.simps(1) assms gr0I iterate_RetE)
  moreover have "iterate b P s\<^sub>0 = Sils (n - m - 1) (\<checkmark> s')"
    by (metis Ret_Sils_iff calculation(3) itree.sel(2) itree.simps(5) un_Sil_Sils)
  ultimately show ?thesis using that by auto
qed

lemma iterate_body_consume:
  assumes "iterate b P s \<midarrow>tr\<leadsto> \<checkmark> s'" "b s"
  obtains tr\<^sub>0 s\<^sub>0 where "tr\<^sub>0 \<le> tr" "P s \<midarrow>tr\<^sub>0\<leadsto> \<checkmark> s\<^sub>0" "iterate b P s\<^sub>0 \<midarrow>tr - tr\<^sub>0\<leadsto> \<checkmark> s'"
  using assms 
  by (auto elim!: trace_to_bindE simp add: iterate.code)
     (metis Prefix_Order.prefixI append_minus)

lemma iterate_body_strong_consume:
  assumes "iterate b P s \<midarrow>tr\<rightarrow> \<checkmark> s'" "b s"
  obtains tr\<^sub>0 s\<^sub>0 where "(tr\<^sub>0 @ [None]) \<le> tr" "P s \<midarrow>tr\<^sub>0\<rightarrow> \<checkmark> s\<^sub>0" "iterate b P s\<^sub>0 \<midarrow>tr - (tr\<^sub>0 @ [None])\<rightarrow> \<checkmark> s'"
proof -
  from assms have "(P s \<bind> \<tau> \<circ> iterate b P) \<midarrow>tr\<rightarrow> \<checkmark> s'"
    by (simp add: iterate.code assms)
  thus ?thesis
  proof (cases rule: strace_to_bindE)
    case (left P')
    then obtain s\<^sub>0 where "P' = \<checkmark> s\<^sub>0" "(\<tau> \<circ> iterate b P) s\<^sub>0 = \<checkmark> s'"
      by auto
    text \<open> It cannot be the case that the left process produced all the trace, because the right
           trace at least contributes one silent event. \<close>
    hence False
      by simp
    thus ?thesis by simp
  next
    case (right s\<^sub>0 tr\<^sub>0 tr\<^sub>1)
    then obtain tr\<^sub>1' where tr\<^sub>1: "tr\<^sub>1 = None # tr\<^sub>1'" "iterate b P s\<^sub>0 \<midarrow>tr\<^sub>1'\<rightarrow> \<checkmark> s'"
      by (auto)
    hence "tr\<^sub>0 @ [None] \<le> tr" "iterate b P s\<^sub>0 \<midarrow>tr - (tr\<^sub>0 @ [None])\<rightarrow> \<checkmark> s'"
      by (simp_all add: right(3) list_concat_minus_list_concat)
    with right(1) tr\<^sub>1 that show ?thesis by auto
  qed
qed

lemma iterate_ncond_prop:
  "\<not> (b s) \<Longrightarrow> ((\<lambda>s. if b s then P s \<bind> (\<lambda>s'. \<tau> (\<checkmark> s')) else \<checkmark> s) ^^ n) s = Ret s"
  by (induct n, auto simp add: seq_itree_def kleisli_comp_def)

lemma iterate_as_power:
  fixes P :: "('e, 's) htree"
  assumes "\<exists> m\<le>n. iterate b P s = Sils m (\<checkmark> s')" "b s"
  shows "iterate b P s = ((\<lambda> s. (if (b s) then (P s \<bind> (\<lambda> s'. \<tau> (Ret s'))) else Ret s)) ^^ n) s"
using assms proof (induct n arbitrary: s)
  case 0
  then show ?case by (meson iterate_body_countdown not_less)
next
  case (Suc n)
  obtain n' where n': "n'\<le>Suc n" "iterate b P s = Sils n' (\<checkmark> s')"
    using Suc.prems(1) by blast
  obtain m s\<^sub>0 where P: "0 < n'" "m \<le> n'" "P s = Sils m (\<checkmark> s\<^sub>0)" "iterate b P s\<^sub>0 = Sils (n' - m - 1) (\<checkmark> s')"
    by (meson Suc.prems(2) iterate_body_countdown n'(2))
  have "iterate b P s = \<tau> (Sils m (iterate b P s\<^sub>0))"
    by (subst iterate.code, simp add: Suc(3) P)
  have le_n: "n' - m - 1 \<le> n"
    using n'(1) by auto
  show ?case
  proof (cases "b s\<^sub>0")
    case True
    hence hyp: "iterate b P s\<^sub>0 = ((\<lambda>s. (if b s then (P s \<bind> (\<lambda> s'. \<tau> (Ret s'))) else \<checkmark> s)) ^^ n) s\<^sub>0"
      using P(4) Suc.hyps le_n by blast
    show ?thesis
      by (simp add: seq_itree_def iterate.code Suc kleisli_comp_def, simp add: P(3) hyp)
  next
    case False
    then show ?thesis 
      by (simp add: seq_itree_def iterate.code Suc kleisli_comp_def P(3) iterate_ncond_prop)
  qed
qed

lemma list_compr_option: "[x. Some x \<leftarrow> tr] = map the (filter (Not \<circ> Option.is_none) tr)"
  by (induct tr, auto simp add: Option.is_none_def)

text \<open> If an iterated ITree terminates then there is a chain of states, punctuated by traces,
  that leads to a state where the condition is not satisfied. \<close>

lemma iterate_term_chain_strong:
  assumes "iterate b P s \<midarrow>tr\<rightarrow> \<checkmark> s'" "b s"
  shows "\<exists> chn. itree_chain P s s' chn 
              \<and> concat (map fst chn) = [e. Some e \<leftarrow> tr] 
              \<and> (\<forall> i < length chn - 1. b (snd (chn ! i)))
              \<and> \<not> b s'"
proof -
  from assms show ?thesis
  proof (induct "length tr" arbitrary: tr s rule: nat_less_induct)
    case 1
    then obtain tr\<^sub>0 s\<^sub>0 where tr\<^sub>0: "(tr\<^sub>0 @ [None]) \<le> tr" "P s \<midarrow>tr\<^sub>0\<rightarrow> \<checkmark> s\<^sub>0" "iterate b P s\<^sub>0 \<midarrow>tr - (tr\<^sub>0 @ [None])\<rightarrow> \<checkmark> s'"
      by (meson iterate_body_strong_consume)
    let ?tr' = "tr - (tr\<^sub>0 @ [None])"
    from 1 tr\<^sub>0 
    have chn_ex:"(\<forall>s\<^sub>0. iterate b P s\<^sub>0 \<midarrow>?tr'\<rightarrow> \<checkmark> s' \<longrightarrow> b s\<^sub>0 \<longrightarrow> 
                  (\<exists>chn. itree_chain P s\<^sub>0 s' chn 
                       \<and> concat (map fst chn) = [e. Some e \<leftarrow> ?tr'] 
                       \<and> (\<forall> i < length chn - 1. b (snd (chn ! i)))
                       \<and> \<not> b s'))"
      by (drule_tac x="length ?tr'" in spec, auto simp add: length_minus_less)
    show ?case
    proof (cases "b s\<^sub>0")
      case True
      then obtain chn 
        where chn: "itree_chain P s\<^sub>0 s' chn" "concat (map fst chn) = [e. Some e \<leftarrow> ?tr']"
                   "\<forall> i < length chn - 1. b (snd (chn ! i))" "\<not> b s'"
        using chn_ex tr\<^sub>0(3) by blast
      then show ?thesis
        apply (rule_tac x="([e. Some e \<leftarrow> tr\<^sub>0], s\<^sub>0) # chn" in exI)
        apply (auto simp add: itree_chain_ConsI strace_then_trace tr\<^sub>0(2))
        apply (smt (verit, del_insts) Prefix_Order.prefixE append.right_neutral append_minus concat.simps(2) concat_append list.simps(9) map_append option.simps(4) tr\<^sub>0(1))
        apply (simp_all add: list_compr_option True nth_Cons' tr\<^sub>0)
        done
    next
      case False
      with tr\<^sub>0(3) have "P s \<midarrow>[e. Some e \<leftarrow> tr]\<leadsto> \<checkmark> s'"
        by (auto simp add: iterate.code)
           (smt (z3) Prefix_Order.prefixE append_Nil2 append_minus concat.simps(2) concat_append list.simps(9) map_append option.simps(4) strace_then_trace tr\<^sub>0(1) tr\<^sub>0(2))
      with False tr\<^sub>0(3) show ?thesis
        by (rule_tac x="[([e. Some e \<leftarrow> tr], s')]" in exI, auto, unfold_locales, auto)
    qed
  qed
qed

lemma iterate_term_chain:
  assumes "iterate b P s \<midarrow>tr\<leadsto> \<checkmark> s'" "b s"
  shows "\<exists> chn. itree_chain P s s' chn 
              \<and> tr = concat (map fst chn) 
              \<and> (\<forall> i < length chn - 1. b (snd (chn ! i)))
              \<and> \<not> b s'"
proof -
  obtain tr\<^sub>0 where tr\<^sub>0: "iterate b P s \<midarrow>tr\<^sub>0\<rightarrow> \<checkmark> s'" "tr = [e. Some e \<leftarrow> tr\<^sub>0]"
    using assms(1) trace_then_strace by blast
  from iterate_term_chain_strong[OF tr\<^sub>0(1), OF assms(2)]
  show ?thesis
    by (auto, metis tr\<^sub>0(2))
qed

lemma iterate_term_chain_iff:
  "iterate b P s \<midarrow>tr\<leadsto> \<checkmark> s' \<longleftrightarrow>
   ((\<not> b s \<and> s = s' \<and> tr = []) \<or>
     (b s \<and> \<not> b s' \<and> (\<exists> chn. itree_chain P s s' chn \<and> tr = concat (map fst chn) 
      \<and> (\<forall> i < length chn - 1. b (snd (chn ! i))))))"
  by (metis Ret_trns iterate_chain_terminates iterate_cond_false iterate_term_chain itree.inject(1))

end