theory ITree_Iteration
  imports ITree_Divergence ITree_Deadlock
begin

subsection \<open> Iteration \<close>

text \<open> For now we support only basic tail-recursive iteration. \<close>

corec iterate :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
"iterate b P s = (if (b s) then (P s \<bind> (\<tau> \<circ> (iterate b P))) else Ret s)"

abbreviation "loop \<equiv> iterate (\<lambda> s. True)"

definition iter :: "('a \<Rightarrow> ('e, 'a + 'b) itree) \<Rightarrow> 'a \<Rightarrow> ('e, 'b) itree" where 
"iter P s = iterate isl (P \<circ> projl) (Inl s) \<bind> Ret \<circ> projr"

lemma iterate_cond_false [simp]:
  "\<not> (b s) \<Longrightarrow> iterate b P s = Ret s"
  by (simp add: iterate.code)

lemma iterate_body_nonterminates:
  assumes "nonterminating (P s)" "b s"
  shows "nonterminating (iterate b P s)"
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

lemma iterate_SilE [elim, consumes 1, case_names initial continue]:
  assumes "\<tau> P = iterate b Q s"
    "\<And> P'. \<lbrakk> b s; Q s = \<tau> P'; P = (P' \<bind> \<tau> \<circ> iterate b Q) \<rbrakk> \<Longrightarrow> R"
    "\<And> s'. \<lbrakk> b s; Q s = Ret s'; P = iterate b Q s' \<rbrakk> \<Longrightarrow> R"
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

lemma iterate_VisE'[consumes 1, case_names body]:
  assumes "iterate b Q s = Vis F"
    "\<And> G. \<lbrakk> b s; Q s = Vis G; F = (map_pfun (\<lambda> x. bind_itree x (\<tau> \<circ> iterate b Q)) G) \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms(1) assms(2) iterate_Vis_dest)

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

subsection \<open> Power \<close>

overloading
  itreepow \<equiv> "compow :: nat \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree"
begin

fun itreepow :: "nat \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
"itreepow 0 P = Ret" |
"itreepow (Suc n) P = P ;; itreepow n P"

end

subsection \<open> Chains \<close>

type_synonym ('e, 's) chain = "('e list \<times> 's) list"

inductive itree_chain :: "'s \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e list \<times> 's) list \<Rightarrow> 's \<Rightarrow> bool" ("_ \<turnstile> _ \<midarrow>_\<leadsto>\<^sup>* _" [55, 0, 0, 55] 55) where
chain_Nil [intro]: "s \<turnstile> P \<midarrow>[]\<leadsto>\<^sup>* s" |
chain_step [intro]: "\<lbrakk> P(s) \<midarrow>tr\<leadsto> \<checkmark> s\<^sub>0; s\<^sub>0 \<turnstile> P \<midarrow>chn\<leadsto>\<^sup>* s\<^sub>1 \<rbrakk> \<Longrightarrow> s \<turnstile> P \<midarrow>(tr, s\<^sub>0) # chn\<leadsto>\<^sup>* s\<^sub>1"

inductive_cases
  chain_stepE [elim]: "s \<turnstile> P \<midarrow>(tr, s\<^sub>0) # chn\<leadsto>\<^sup>* s\<^sub>1"

lemma chain_last: "\<lbrakk> s \<turnstile> P \<midarrow>chn\<leadsto>\<^sup>* s'; chn \<noteq> [] \<rbrakk> \<Longrightarrow> snd (last chn) = s'"
  by (induct rule: itree_chain.induct, auto)
     (metis itree_chain.simps list.discI)

lemma chain_appendI: "\<lbrakk> s \<turnstile> P \<midarrow>tr\<^sub>1\<leadsto>\<^sup>* s\<^sub>0; s\<^sub>0 \<turnstile> P \<midarrow>tr\<^sub>2\<leadsto>\<^sup>* s' \<rbrakk> \<Longrightarrow> s \<turnstile> P \<midarrow>tr\<^sub>1 @ tr\<^sub>2\<leadsto>\<^sup>* s'"
  by (induct rule: itree_chain.induct, auto simp add: chain_step)

lemma chain_appendD: "s \<turnstile> P \<midarrow>tr\<^sub>1 @ tr\<^sub>2\<leadsto>\<^sup>* s' \<Longrightarrow> \<exists> s\<^sub>0. s \<turnstile> P \<midarrow>tr\<^sub>1\<leadsto>\<^sup>* s\<^sub>0 \<and> s\<^sub>0 \<turnstile> P \<midarrow>tr\<^sub>2\<leadsto>\<^sup>* s'"
  apply (induct tr\<^sub>1 arbitrary: s s')
  apply (simp)
  using chain_Nil apply fastforce
  apply (simp)
  apply (case_tac a)
  apply (meson chain_step chain_stepE)
  done  

lemma chain_append_iff: "s \<turnstile> P \<midarrow>tr\<^sub>1 @ tr\<^sub>2\<leadsto>\<^sup>* s' \<longleftrightarrow> (\<exists> s\<^sub>0. s \<turnstile> P \<midarrow>tr\<^sub>1\<leadsto>\<^sup>* s\<^sub>0 \<and> s\<^sub>0 \<turnstile> P \<midarrow>tr\<^sub>2\<leadsto>\<^sup>* s')"
  by (meson chain_appendD chain_appendI)

definition chain_states :: "('e, 's) chain \<Rightarrow> 's set" where
"chain_states chn = set (map snd chn)"

lemma chain_states_Nil [simp]: "chain_states [] = {}" by (simp add: chain_states_def)
lemma chain_states_Cons [simp]: "chain_states ((tr, s) # chn) = insert s (chain_states chn)"
  by (auto simp add: chain_states_def)

definition chain_trace :: "('e, 's) chain \<Rightarrow> 'e list" where
"chain_trace chn = concat (map fst chn)"

lemma chain_trace_Nil [simp]: "chain_trace [] = []" by (simp add: chain_trace_def)
lemma chain_trace_Cons [simp]: "chain_trace ((tr, s) # chn) = tr @ chain_trace chn"
  by (simp add: chain_trace_def)

lemma chain_first_step: "\<lbrakk> s \<turnstile> P \<midarrow>chn\<leadsto>\<^sup>* s'; chn \<noteq> [] \<rbrakk> \<Longrightarrow> P s \<midarrow>fst (hd chn)\<leadsto> \<checkmark> (snd (hd chn))"
  by (metis chain_stepE list.collapse prod.collapse)

lemma chain_steps: "\<lbrakk> s \<turnstile> P \<midarrow>chn\<leadsto>\<^sup>* s'; length chn > 1; i < length chn - 1 \<rbrakk> \<Longrightarrow> P (snd (chn ! i)) \<midarrow>fst (chn ! Suc i)\<leadsto> \<checkmark> (snd (chn ! Suc i))"
proof (induct arbitrary: i rule: itree_chain.induct)
  case (chain_Nil s P)
  then show ?case by simp
next
  case (chain_step P s tr s\<^sub>0 chn s\<^sub>1)
  then show ?case
  proof (cases "i = 0")
    case True
    with chain_step show ?thesis
      by (simp, metis chain_first_step hd_conv_nth)
  next
    case False
    with chain_step gr0_conv_Suc show ?thesis
      by fastforce
  qed
qed

lemma chain_stated_indexed: "(\<forall>s\<in>chain_states chn. B s) \<longleftrightarrow> (\<forall> i<length chn. B (snd (chn ! i)))"
  by (auto simp add: chain_states_def, metis in_set_conv_nth snd_eqD)

fun itree_term_chain :: 
  "_ \<times> 's \<Rightarrow> ('e, 's) htree \<Rightarrow> 'e list \<Rightarrow> 's \<Rightarrow> bool" ("_ \<turnstile> _ \<midarrow>_\<leadsto>\<^sub>\<checkmark> _" [55, 0, 0, 55] 55)
  where "(b, s) \<turnstile> P \<midarrow>tr\<leadsto>\<^sub>\<checkmark> s' \<longleftrightarrow> (\<exists> chn s\<^sub>0 tr\<^sub>0. b s \<and> s \<turnstile> P \<midarrow>chn\<leadsto>\<^sup>* s\<^sub>0 \<and> (\<forall>s\<in>chain_states chn. b s) \<and> P s\<^sub>0 \<midarrow>tr\<^sub>0\<leadsto> \<checkmark> s' \<and> tr = chain_trace chn @ tr\<^sub>0)"

declare itree_term_chain.simps [simp del]

lemma term_chain_step:
  assumes "b s" "P(s) \<midarrow>tr\<^sub>0\<leadsto> \<checkmark> s\<^sub>0" "(b, s\<^sub>0) \<turnstile> P \<midarrow>tr\<^sub>1\<leadsto>\<^sub>\<checkmark> s'"
  shows "(b, s) \<turnstile> P \<midarrow>tr\<^sub>0 @ tr\<^sub>1\<leadsto>\<^sub>\<checkmark> s'"
proof -
  obtain chn s\<^sub>1 tr\<^sub>2 where chn: "b s\<^sub>0" "s\<^sub>0 \<turnstile> P \<midarrow>chn\<leadsto>\<^sup>* s\<^sub>1" "\<forall>s\<in>chain_states chn. b s" "P s\<^sub>1 \<midarrow>tr\<^sub>2\<leadsto> \<checkmark> s'" "tr\<^sub>1 = chain_trace chn @ tr\<^sub>2"
    by (metis assms(3) itree_term_chain.simps)
  have chn': "s \<turnstile> P \<midarrow>(tr\<^sub>0, s\<^sub>0) # chn\<leadsto>\<^sup>* s\<^sub>1"
    by (simp add: assms(2) chain_step chn(2))
  show ?thesis
    apply (simp add: itree_term_chain.simps assms)
    apply (rule_tac x="(tr\<^sub>0, s\<^sub>0) # chn" in exI)
    apply (rule_tac x="s\<^sub>1" in exI)
    apply (simp_all add: chn chn')
    done
qed

lemma iterate_transition_chain:
  assumes "s \<turnstile> P \<midarrow>chn\<leadsto>\<^sup>* s'" "b s" "\<forall> s\<^sub>0\<in>chain_states chn. b s\<^sub>0"
  shows "iterate b P s \<midarrow>chain_trace chn\<leadsto> iterate b P s'"
using assms
proof (induct s P chn s' rule: itree_chain.induct)
  case (chain_Nil s P)
  then show ?case by auto
next
  case (chain_step P s tr s\<^sub>0 chn s\<^sub>1)
  then show ?case 
    by simp
       (meson iterate_trace_to trace_to_trans)
qed

lemma final_state_in_chain: "\<lbrakk> s \<turnstile> P \<midarrow>chn\<leadsto>\<^sup>* s'; chn \<noteq> [] \<rbrakk> \<Longrightarrow> s' \<in> chain_states chn"
  by (drule chain_last, simp, auto simp add: chain_states_def)

lemma iterate_chain_terminates:
  assumes "b s" "(b, s) \<turnstile> P \<midarrow>tr\<leadsto>\<^sub>\<checkmark> s'" "\<not> b s'"
  shows "iterate b P s \<midarrow>tr\<leadsto> \<checkmark> s'"
proof -
  obtain chn s\<^sub>0 tr\<^sub>0 where P: "s \<turnstile> P \<midarrow>chn\<leadsto>\<^sup>* s\<^sub>0" "\<forall>s\<in>chain_states chn. b s" "P s\<^sub>0 \<midarrow>tr\<^sub>0\<leadsto> \<checkmark> s'" "tr = chain_trace chn @ tr\<^sub>0"
    using assms
    by (simp add: itree_term_chain.simps, auto)

  have 1: "iterate b P s \<midarrow>chain_trace chn\<leadsto> iterate b P s\<^sub>0"
    by (simp add: P(1) P(2) assms(1) iterate_transition_chain)
  have 2: "iterate b P s\<^sub>0 \<midarrow>tr\<^sub>0\<leadsto> \<checkmark> s'"
  proof -
    have "b s\<^sub>0"
      by (metis P(1) P(2) assms(1) final_state_in_chain itree_chain.cases list.discI)
    thus ?thesis
      by (simp add: P(3) assms(3) iterate_term_once)
  qed
  show ?thesis
    using "1" "2" P(4) trace_to_trans by blast
qed


lemmas disj_cases[consumes 1, case_names disj1 disj2] = disjE

lemma bind_extra_tauE:
  assumes 
    "(P \<bind> \<tau> \<circ> \<checkmark>) \<midarrow>tr\<leadsto> P'"
    "\<And>P\<^sub>0. \<lbrakk> P \<midarrow>tr\<leadsto> P\<^sub>0; P' = P\<^sub>0 \<bind> \<tau> \<circ> \<checkmark> \<rbrakk> \<Longrightarrow> thesis"
    "\<And>x. \<lbrakk> P \<midarrow>tr\<leadsto> Ret x; P' = Ret x \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
  using assms
  by (auto elim!: trace_to_bindE)
     (metis Ret_trns bind_Ret comp_apply self_append_conv trace_to_SilE)

text \<open> The next theorem states is a general law for extracting chains from prefixed iterations. 
  We adopt the prefixed pattern (@{term "Q \<bind> iterate b B"} so that the inductive proof goes through.
  Whenever @{term "(Q \<bind> iterate b B) \<midarrow>tr\<leadsto> R"} there are two possibilities. (1) The prefix @{term Q}
  performs the transition, and @{term "iterate b B"} is the continuation. (2) The prefix @{term Q}
  terminates in a state @{term "s"}, having done a prefix of the trace, and then there is a chain of 
  iterations of the loop body. Finally, it is possible that the body makes partial progress, leading
  to another continuation. The overall trace is consists of (a) the trace contributed by @{term Q};
  (b) the trace contributed in the chain; and (c) the trace contributed by partial execution of
  they body @{term B}.
 \<close>

theorem prefixed_iterate_chain:
  fixes B :: "('e, 's) htree"
  assumes "(Q \<bind> iterate b B) \<midarrow>tr\<leadsto> R"
  shows "(\<exists> Q'. Q \<midarrow>tr\<leadsto> Q' \<and> R = Q' \<bind> iterate b B)
         \<or> (\<exists> s chn s\<^sub>0 tr\<^sub>0 tr\<^sub>1 P' n. 
              Q \<midarrow>tr\<^sub>0\<leadsto> \<checkmark> s \<and> b s \<and> s \<turnstile> B \<midarrow>chn\<leadsto>\<^sup>* s\<^sub>0 \<and> (\<forall> s\<in>chain_states chn. b s) \<and> B s\<^sub>0 \<midarrow>tr\<^sub>1\<leadsto> P' 
            \<and> tr = tr\<^sub>0 @ chain_trace chn @ tr\<^sub>1 
            \<and> R = P' \<bind> Sils n \<circ> iterate b B \<and> n \<le> 1)"
  using assms
\<comment> \<open> We begin the proof by induction on the transition relation. This leads to three top-level
  cases corresponding to the three possible ways a transition is constructed in the inductive predicate. \<close>
proof (induct "Q \<bind> iterate b B" tr R arbitrary: Q rule: trace_to.induct)
  \<comment> \<open> If the transition is empty, and so @{term "R = Q \<bind> iterate b B"}, then the proof is trivial. \<close>
  case trace_to_Nil
  then show ?case
    by blast
next
  text \<open> If the transition is a @{term "\<tau>"} then we need to further determine whether it originates
    in @{term Q} or in the loop @{term "iterate b B"}. \<close>
  case (trace_to_Sil P tr P')
  have "\<tau> P = Q \<bind> iterate b B"
    by (simp add: trace_to_Sil.hyps(3))
  thus ?case
  \<comment> \<open> We split on these two possibilities below. \<close>
  proof (cases rule: bind_SilE')
    case (initial Q\<^sub>0)
    note Q_def = this(1) and P_def = this(2)
    from trace_to_Sil.hyps(2)[of Q\<^sub>0, OF initial(2)] show ?thesis
    \<comment> \<open> If it originates in @{term Q}, we need to further split the inductive hypotheses. Either
         the remainder of @{term Q} (@{term Q\<^sub>0}) can reach @{term R}, or else the loop body has
         executed, and so there is a chain. \<close>
    proof (cases rule: disj_cases)
      case disj1
      then show ?thesis
        using trace_to_Sil P_def Q_def by blast
    next
      case disj2
      then obtain s s\<^sub>0 ::"'s" and chn::"('e,'s) chain" and tr\<^sub>0 tr\<^sub>1 :: "'e list" and B' :: "('e, 's) itree" and n :: nat
        where steps: "Q\<^sub>0 \<midarrow>tr\<^sub>0\<leadsto> \<checkmark> s" "b s" "s \<turnstile> B \<midarrow>chn\<leadsto>\<^sup>* s\<^sub>0" "\<forall> s\<in>chain_states chn. b s" "B s\<^sub>0 \<midarrow>tr\<^sub>1\<leadsto> B'" 
                     "tr = tr\<^sub>0 @ chain_trace chn @ tr\<^sub>1" "P' = B' \<bind> Sils n \<circ> iterate b B" "n \<le> 1"
        by blast
        
      show ?thesis
        apply (simp add: Q_def P_def)
        apply (rule_tac disjI2)
        apply (rule_tac x="s" in exI)
        apply (rule_tac x="chn" in exI)
        apply (rule_tac x="s\<^sub>0" in exI)
        apply (rule_tac x="tr\<^sub>0" in exI)
        apply (simp add: steps)
        using steps(5) steps(8) apply auto
        done
    qed
  next
    case (continue s)
    note defs = this
    with defs(2) show ?thesis
    \<comment> \<open> If the @{term \<tau>} originates in the loop, then again we need two cases: (1) it originates
         in the first execution of body, or (2) some further iterations. \<close>
    proof (cases rule: iterate_SilE)
      case (continue s') 
      with trace_to_Sil(2)[of "Ret s' :: ('e, 's) itree", simplified, OF continue(3)] show ?thesis
      proof (cases rule: disj_cases)
        case disj1
        with continue show ?thesis
          apply (simp add: defs)
          apply (rule_tac disjI2)
          apply (rule_tac x="[]" in exI)
          apply (rule_tac x="s" in exI)
          apply (auto)
          apply (metis Sils.simps(1) bot_nat_0.extremum)
          done
      next
        case disj2
        then obtain chn s\<^sub>0 tr\<^sub>1 P'' n where P'': "b s'" "s' \<turnstile> B \<midarrow>chn\<leadsto>\<^sup>* s\<^sub>0" "\<forall> s\<in>chain_states chn. b s" "B s\<^sub>0 \<midarrow>tr\<^sub>1\<leadsto> P''" "tr = chain_trace chn @ tr\<^sub>1" "P' = P'' \<bind> Sils n \<circ> iterate b B" "n \<le> 1"
          by auto
        with continue show ?thesis
          apply (simp add: defs)
          apply (rule_tac disjI2)
          apply (rule_tac x="([], s') # chn" in exI)
          apply (rule_tac x="s\<^sub>0" in exI)
          apply auto
          done
      qed
    next
      \<comment> \<open> The prefix terminated in state @{term s}, and body @{term B} made partial progress. \<close>
      case (initial P\<^sub>0)
      hence P: "P = P\<^sub>0 \<bind> \<tau> \<circ> \<checkmark> \<bind> iterate b B"
        by (simp add: bind_itree_assoc[THEN sym] comp_def)
      from trace_to_Sil(2)[of "P\<^sub>0 \<bind> Sil \<circ> Ret", OF P] initial(1)
      show ?thesis
      proof (cases rule: disj_cases)
        case disj1
        with initial(1,2) show ?thesis 
          apply (simp add: defs)
          apply (rule disjI2)
          apply (rule_tac x="[]" in exI)
          apply (rule_tac x="s" in exI)
          apply (auto)
          apply (erule bind_extra_tauE)
           apply (simp)
           apply (rule_tac x="P\<^sub>0'" in exI)
           apply (auto simp add: bind_itree_assoc[THEN sym] comp_def)
           apply (rule_tac x="1" in exI)
          apply simp
          apply (metis Sils.simps(1) bind_Ret bot_nat_0.extremum trace_to.trace_to_Sil)
          done
      next
        case disj2
        then obtain s\<^sub>0 chn s\<^sub>1 tr\<^sub>0 tr\<^sub>1 P'' n
          where P\<^sub>0: "(P\<^sub>0 \<bind> \<tau> \<circ> \<checkmark>) \<midarrow>tr\<^sub>0\<leadsto> \<checkmark> s\<^sub>0" "b s\<^sub>0" "s\<^sub>0 \<turnstile> B \<midarrow>chn\<leadsto>\<^sup>* s\<^sub>1" "\<forall> s\<in>chain_states chn. b s"
                    "B s\<^sub>1 \<midarrow>tr\<^sub>1\<leadsto> P''" "tr = tr\<^sub>0 @ chain_trace chn @ tr\<^sub>1" "P' = P'' \<bind> Sils n \<circ> iterate b B" "n \<le> 1"
          by auto
        then show ?thesis
          apply (simp add: defs)
          apply (rule_tac disjI2)
          apply auto
          using initial(1) apply fastforce
          apply (rule_tac x="(tr\<^sub>0, s\<^sub>0) # chn" in exI)
          apply (rule_tac x="s\<^sub>1" in exI)
          apply auto
           apply (simp add: chain_step initial(2) trace_to_post_Sil_iff)
          done
      qed
    qed
  qed
next
  case (trace_to_Vis e F tr P')
  hence "Vis F = Q \<bind> iterate b B" by simp
  thus ?case
  proof (cases rule: bind_VisE')
    case (initial F')
    have F: "F(e)\<^sub>p = F'(e)\<^sub>p \<bind> iterate b B"
      using initial(2) trace_to_Vis.hyps(1) by auto

    from trace_to_Vis(3)[of "F'(e)\<^sub>p", OF F] show ?thesis
    proof (cases rule: disj_cases)
      case disj1
      then show ?thesis
        using initial(1) initial(2) trace_to_Vis.hyps(1) by auto
    next
      case disj2
      then show ?thesis
        by (metis append_Cons initial(1) initial(2) pdom_map_pfun trace_to.trace_to_Vis trace_to_Vis.hyps(1)) 
    qed
  next
    case (continue s)
    from continue(2) show ?thesis
    proof (cases rule: iterate_VisE')
      case (body G)
      hence "F(e)\<^sub>p = G(e)\<^sub>p \<bind> \<tau> \<circ> iterate b B"
        using trace_to_Vis.hyps(1) by auto
      hence F: "F(e)\<^sub>p = G(e)\<^sub>p \<bind> \<tau> \<circ> \<checkmark> \<bind> iterate b B"
        by (simp add: bind_itree_assoc[THEN sym] comp_def)
      from trace_to_Vis(3)[of "G(e)\<^sub>p \<bind> Sil \<circ> Ret", OF F] show ?thesis
      proof (cases rule: disj_cases)
        case disj1
        then obtain Q' where "(G(e)\<^sub>p \<bind> \<tau> \<circ> \<checkmark>) \<midarrow>tr\<leadsto> Q'" "P' = Q' \<bind> iterate b B"
          by auto
        with trace_to_Vis(1) continue(1) body show ?thesis
          apply (simp)
          apply (rule_tac x="[]" in exI)
          apply (rule_tac x="s" in exI)
          apply auto
          apply (erule bind_extra_tauE)
           apply (rule_tac x="P\<^sub>0" in exI)
           apply auto
           apply (rule_tac x="1" in exI)
          apply (simp add: bind_itree_assoc[THEN sym] comp_def)
          apply (metis Sils.simps(1) bind_Ret bot_nat_0.extremum comp_eq_dest_lhs)
        done
      next
        case disj2
        then obtain s\<^sub>0 chn s\<^sub>1 tr\<^sub>0 tr\<^sub>1 P'' n 
          where G: "(G(e)\<^sub>p \<bind> \<tau> \<circ> \<checkmark>) \<midarrow>tr\<^sub>0\<leadsto> \<checkmark> s\<^sub>0" "b s\<^sub>0" 
          and chn: "s\<^sub>0 \<turnstile> B \<midarrow>chn\<leadsto>\<^sup>* s\<^sub>1" "\<forall> s\<in>chain_states chn. b s" "B s\<^sub>1 \<midarrow>tr\<^sub>1\<leadsto> P''" "tr = tr\<^sub>0 @ chain_trace chn @ tr\<^sub>1" and P': "P' = P'' \<bind> Sils n \<circ> iterate b B" "n \<le> 1"
          by auto
        from G trace_to_Vis(1,2) continue(1) body P' chn show ?thesis
          apply (simp)
          apply (erule bind_extra_tauE)
          apply (rule_tac x="(e # tr, s\<^sub>0) # chn" in exI)
          apply (rule_tac x="s\<^sub>1" in exI)
          apply auto
          apply (rule_tac x="(e # tr\<^sub>0, s\<^sub>0) # chn" in exI)
          apply (rule_tac x="s\<^sub>1" in exI)
          apply auto
          done
      qed 
    qed
  qed
qed

lemma iterate_chain [consumes 1, case_names iterates terms]:
  assumes 
    "iterate b B s \<midarrow>tr\<leadsto> R"
    "\<And> chn s\<^sub>0 tr\<^sub>0 P' n. 
        \<lbrakk> b s;
          s \<turnstile> B \<midarrow>chn\<leadsto>\<^sup>* s\<^sub>0; 
          \<forall> s\<in>chain_states chn. b s;
          B s\<^sub>0 \<midarrow>tr\<^sub>0\<leadsto> P';
          tr = chain_trace chn @ tr\<^sub>0; 
          R = P' \<bind> Sils n \<circ> iterate b B; 
          n \<le> 1
        \<rbrakk> \<Longrightarrow> P"
    "\<lbrakk> \<not> b s; tr = []; R = \<checkmark> s \<rbrakk> \<Longrightarrow> P"
  shows P
proof (cases "b s")
  case True
  show ?thesis
    using prefixed_iterate_chain[of "\<checkmark> s", simplified, OF assms(1)]
  proof (cases rule: disj_cases)
    case disj1
    then show ?thesis
      by (rule_tac assms(2)[of "[]" s "[]" "B s" 1, simplified], auto simp add: iterate.code comp_def assms True)
  next
    case disj2
    then show ?thesis
      using assms(2) by force
  qed 
next
  case False
  thus ?thesis
    using assms(1) assms(3) by force
qed

lemma iterate_terminates_chain:
  assumes 
    "iterate b B s \<midarrow>tr\<leadsto> \<checkmark> s'"
    "\<lbrakk> b s; (b, s) \<turnstile> B \<midarrow>tr\<leadsto>\<^sub>\<checkmark> s'; \<not> b s' \<rbrakk> \<Longrightarrow> P"
    "\<lbrakk> \<not> b s; tr = []; s' = s \<rbrakk> \<Longrightarrow> P"
  shows P
  using assms
proof (cases rule: iterate_chain)
  case (iterates chn s\<^sub>0 tr\<^sub>0 P' n)
  hence P': "P' = \<checkmark> s'" "\<not> b s'"
    by (auto elim!: bind_RetE', metis Ret_Sils_iff iterate_RetE')+
  then show ?thesis
    by (metis assms(2) iterates(1-5) itree_term_chain.simps)
next
  case terms
  then show ?thesis
    using assms(3) by fastforce
qed

lemma iterate_term_chain_iff:
  "iterate b B s \<midarrow>tr\<leadsto> \<checkmark> s' \<longleftrightarrow> 
   ((\<not> b s \<and> s = s' \<and> tr = []) \<or> (b s \<and> (b, s) \<turnstile> B \<midarrow>tr\<leadsto>\<^sub>\<checkmark> s' \<and> \<not> b s'))"
proof (cases "b s")
  case True
  then show ?thesis
    by (metis iterate_chain_terminates iterate_terminates_chain)
next
  case False
  then show ?thesis
    by force 
qed

text \<open> These results also allow us to calculate the return values of @{const iterate}. \<close>

lemma retvals_iterate: "\<^bold>R(iterate P C s) = {s'. (\<not> P s \<and> s = s') \<or> (\<exists> es. P s \<and> (P, s) \<turnstile> C \<midarrow>es\<leadsto>\<^sub>\<checkmark> s' \<and> \<not> P s')}"
  by (auto simp add: retvals_def iterate_term_chain_iff)

text \<open> A result linking relational while loops and ITree iteration: \<close>

lemma rel_while_implies_chain:
  assumes "\<exists>xs. \<not> xs = [] \<and> (\<forall>i<length xs. P ((s # xs) ! i) \<and> (\<exists>es. C ((s # xs) ! i) \<midarrow>es\<leadsto> \<checkmark> (xs ! i))) \<and> s' = List.last xs" 
          "\<not> P s'"
  shows "P s" "\<exists>es. (P, s) \<turnstile> C \<midarrow>es\<leadsto>\<^sub>\<checkmark> s'"
proof -
  obtain xs where xs: "xs \<noteq> []" "\<forall>i < length xs. P ((s # xs) ! i) \<and> (\<exists>es. C ((s # xs) ! i) \<midarrow>es\<leadsto> \<checkmark> (xs ! i))" "s' = List.last xs"
    using assms(1) by blast
  hence "\<forall>i < length xs. \<exists>es. C ((s # xs) ! i) \<midarrow>es\<leadsto> \<checkmark> (xs ! i)"
    by presburger
  then obtain ess where ess: "length ess = length xs" "\<And> i. i < length xs \<Longrightarrow> C ((s # xs) ! i) \<midarrow>ess ! i\<leadsto> \<checkmark> (xs ! i)"
    by (auto simp add: Skolem_list_nth)
  obtain chn where chn_def: "chn = butlast (zip ess xs)" by blast
  have chn: "\<And> i. i < length chn \<Longrightarrow> C ((s # map snd chn) ! i) \<midarrow>fst (chn ! i)\<leadsto> \<checkmark> (snd (chn ! i))"
            "\<And> i. i < Suc (length chn) \<Longrightarrow> P ((s # map snd chn) ! i)"
    using chn_def ess xs 
    by auto
       (smt (verit) One_nat_def Suc_less_eq diff_less_Suc length_butlast length_map less_trans_Suc map_fst_zip map_snd_zip nth_Cons' nth_butlast nth_map
       ,metis append_butlast_last_id butlast.simps(2) length_Cons length_append_singleton map_butlast map_snd_zip nth_butlast)
  show P: "P s"
    by (metis length_greater_0_conv nth_Cons_0 xs(1) xs(2))

  have chn_st: "(\<forall>x\<in>chain_states chn. P x)"
    by (simp add: chain_states_def all_set_conv_all_nth)
       (metis chn(2) not_less_eq nth_Cons_Suc nth_map)

  let ?s\<^sub>0 = "List.last (s # map snd chn)"

  from chn have C_steps: "s \<turnstile> C \<midarrow>chn\<leadsto>\<^sup>* ?s\<^sub>0"
  proof (induct chn arbitrary: s)
    case Nil
    then show ?case
      by force
  next
    case (Cons a chn)
    have C:"C s \<midarrow>fst a\<leadsto> \<checkmark> (snd a)"
      using Cons.prems(1) by force
    have 1:"\<And>i. i < length chn \<Longrightarrow> C ((snd a # map snd chn) ! i) \<midarrow>fst (chn ! i)\<leadsto> \<checkmark> (snd (chn ! i))"
      by (metis (no_types, opaque_lifting) Cons.prems(1) Suc_less_eq2 length_Cons list.simps(9) nth_Cons_Suc)
    have 2:"\<And>i. i < Suc (length chn) \<Longrightarrow> P ((snd a # map snd chn) ! i)"
      by (metis Cons.prems(2) Suc_less_eq length_Cons list.simps(9) nth_Cons_Suc)
    have R:"snd a \<turnstile> C \<midarrow>chn\<leadsto>\<^sup>* (List.last (snd a # map snd chn))"
      using "1" "2" Cons.hyps by presburger
    show ?case
      using C R chain_step by fastforce
  qed

  let ?tr\<^sub>0 = "List.last ess"

  have Cs': "C ?s\<^sub>0 \<midarrow>?tr\<^sub>0\<leadsto> \<checkmark> s'" 
    apply (auto simp add: chn_def map_butlast map_fst_zip_take ess(1))
    apply (metis ess(1) ess(2) last_conv_nth length_butlast length_greater_0_conv list.size(3) nth_Cons_0 xs(1) xs(3))
    apply (metis (no_types, lifting) One_nat_def Suc_pred ess(1) ess(2) last_conv_nth length_butlast length_greater_0_conv lessI nth_Cons_Suc nth_butlast xs(1) xs(3))
    done

  have concat_ess: "concat ess = chain_trace chn @ ?tr\<^sub>0"
    by (simp add: chn_def chain_trace_def map_butlast map_fst_zip_take ess(1))
       (metis append.right_neutral append_butlast_last_id concat.simps(1) concat.simps(2) concat_append ess(1) length_0_conv xs(1))

  have "(P, s) \<turnstile> C \<midarrow>concat ess\<leadsto>\<^sub>\<checkmark> s'"
    by (metis Cs' P C_steps chn_st concat_ess itree_term_chain.simps)

  thus "\<exists>es. (P, s) \<turnstile> C \<midarrow>es\<leadsto>\<^sub>\<checkmark> s'" by blast
qed

text \<open> There is an ITree chain if-and-only-if there is a reflexive transitive closure (relational) chain \<close>

lemma itree_chain_iff_rtc_chain:
    "(\<not> P s \<and> s = s' \<or> P s \<and> (\<exists>es. ((P)\<^sub>e, s) \<turnstile> C \<midarrow>es\<leadsto>\<^sub>\<checkmark> s') \<and> \<not> P s') =
       ((s = s' \<or> (\<exists>xs. \<not> xs = [] 
                      \<and> (\<forall>i<length xs. P ((s # xs) ! i) \<and> (xs ! i) \<in> \<^bold>R(C ((s # xs) ! i))) 
                      \<and> s' = last xs)) 
                      \<and> \<not> P s')"
  apply (rule iffI)
  apply (erule disjE)
    apply simp
  apply force
   apply (simp_all add: itree_term_chain.simps retvals_def)
   apply (rule disjI2)
  apply clarify
   apply (rule_tac x="map snd chn @ [s']" in exI)
  apply (auto)[1]
  apply (metis cancel_ab_semigroup_add_class.add_diff_cancel_left' chain_states_def length_map less_Suc_eq_0_disj nth_Cons' nth_append nth_mem plus_1_eq_Suc)
   apply (case_tac "chn = []")
  apply simp
    apply (metis itree_chain.cases list.discI)
   apply (case_tac "i = 0")
  apply simp
  apply (metis (no_types, opaque_lifting) append.simps(2) chain_first_step list.map(2) list.sel(1) neq_Nil_conv nth_Cons_0)
  apply simp
   apply (case_tac "i = length chn")
  apply (simp add: nth_append)
    apply (metis One_nat_def chain_last last_conv_nth)
  apply (auto simp add: nth_append)[1]
    apply (rule_tac x="fst (chn ! i)" in exI)
  apply (smt (verit, best) One_nat_def Suc_less_eq Suc_pred chain_steps less_Suc_eq less_trans_Suc) 
  apply (erule conjE)
  apply (erule disjE)
   apply simp
  apply (rule disjI2)
  apply (metis itree_term_chain.simps rel_while_implies_chain(2))
  done


text \<open> If @{term P} is an invariant of a chain for process @{term C}, then the invariant holds
  for every element of the looped process @{term C}. \<close>

lemma chain_invariant:
  assumes 
    "B s" "P s"
    "\<And> s s'. \<lbrakk> B s; P s; s' \<in> \<^bold>R(C s) \<rbrakk> \<Longrightarrow> P s'"
    "s \<turnstile> C \<midarrow>chn\<leadsto>\<^sup>* s'"
    "\<forall> s\<^sub>0\<in>chain_states chn. B s\<^sub>0"
  shows "\<forall> s\<^sub>0\<in>chain_states chn. P s\<^sub>0"
proof -
  have "\<forall>i<length chn. P (snd (chn ! i))"
  proof (clarify)
    fix i
    assume i: "i < length chn"
    thus "P (snd (chn ! i))"
    proof (induct i)
      case 0
      hence "C s \<midarrow>fst (chn ! 0)\<leadsto> \<checkmark> (snd (chn ! 0))"
        by (metis assms(4) chain_first_step hd_conv_nth length_greater_0_conv)
      thus ?case
        by (meson assms(1) assms(2) assms(3) retvals_traceI)
    next
      case (Suc i)
      hence "C (snd (chn ! i)) \<midarrow>fst (chn ! Suc i)\<leadsto> \<checkmark> (snd (chn ! Suc i))"
        using assms(4) chain_steps by fastforce        
      moreover have "P (snd (chn ! i))"
        by (simp add: Suc.hyps Suc.prems Suc_lessD)
      moreover have "B (snd (chn ! i))"
        by (simp add: Suc.prems Suc_lessD assms(5) chain_states_def)
      ultimately show ?case
        by (meson assms(3) retvals_traceI)
    qed
  qed
  thus ?thesis
    by (simp add: chain_stated_indexed)
qed

lemma chain_invariant_simple:
  assumes 
    "P s"
    "\<And> s s'. \<lbrakk> P s; s' \<in> \<^bold>R(C s) \<rbrakk> \<Longrightarrow> P s'"
    "s \<turnstile> C \<midarrow>chn\<leadsto>\<^sup>* s'"
  shows "\<forall> s\<^sub>0\<in>chain_states chn. P s\<^sub>0"
  using assms
  by (rule_tac chain_invariant[of "\<lambda> s. True" s P C chn s'], auto)

text \<open> We can establish termination, as usual, with an variant function. Here, ``terminates'' means 
  that an ITree may terminate. \<close>

definition terminates :: "('e, 's) itree \<Rightarrow> bool" where
"terminates P = (\<exists> tr s'. P \<midarrow>tr\<leadsto> \<checkmark> s')"

lemma terminates_Ret: "terminates (\<checkmark> s')"
  by (simp add: terminates_def)

lemma terminates_Sil: "terminates (Sil P) = terminates P"
  by (simp add: terminates_def)

lemma terminates_Sils: "terminates (Sils n P) = terminates P"
  by (simp add: terminates_def)

lemma terminates_bind:
  assumes "terminates P" "\<And> v. v \<in> \<^bold>R(P) \<Longrightarrow> terminates(Q v)"
  shows "terminates (P \<bind> Q)"
  by (meson assms(1) assms(2) retvals_traceI terminates_def trace_to_bind)

lemma not_terminates_diverge:
  "terminates diverge = False"
  by (meson diverge_no_Ret_trans terminates_def)

text \<open> A terminating pure ITree is divergence free \<close>

lemma terminates_pure_implies_div_free:
  assumes "pure_itree P" "terminates P"
  shows "div_free P"
  by (metis Sils_diverge assms div_free_is_no_divergence no_divergence_def not_terminates_diverge pure_itree_def trace_to_Nil_Sils)

text \<open> The following theorem using both a variant @{term V} and invariant @{term I} to establish
  termination. \<close>

lemma wellorder_variant_term_chain:
  fixes V :: "'s \<Rightarrow> 'a::wellorder" and I :: "'s \<Rightarrow> bool"
  assumes 
    "\<And> s\<^sub>0. \<lbrakk> b s\<^sub>0; I s\<^sub>0 \<rbrakk> \<Longrightarrow> terminates (B s\<^sub>0)"
    "\<And> s\<^sub>0 s\<^sub>1 tr. \<lbrakk> b s\<^sub>0; I s\<^sub>0; B(s\<^sub>0) \<midarrow>tr\<leadsto> \<checkmark> s\<^sub>1 \<rbrakk> \<Longrightarrow> I s\<^sub>1"
    "\<And> s\<^sub>0 s\<^sub>1 tr. \<lbrakk> b s\<^sub>0; I s\<^sub>0; B(s\<^sub>0) \<midarrow>tr\<leadsto> \<checkmark> s\<^sub>1 \<rbrakk> \<Longrightarrow> V(s\<^sub>1) < V(s\<^sub>0)"
  shows "\<lbrakk> I s; b s \<rbrakk> \<Longrightarrow> \<exists> tr s'. (b, s) \<turnstile> B \<midarrow>tr\<leadsto>\<^sub>\<checkmark> s' \<and> \<not> b s'"
proof (induct "V(s)" arbitrary: s rule: less_induct)
  case (less s\<^sub>0)
  obtain s\<^sub>1 tr\<^sub>0 where B_next: "B(s\<^sub>0) \<midarrow>tr\<^sub>0\<leadsto> \<checkmark> s\<^sub>1"
    by (meson assms(1) less.prems(1) less.prems(2) terminates_def)
  have inv: "I s\<^sub>1"
    using B_next assms(2) less.prems(1) less.prems(2) by presburger
  have dec: "V(s\<^sub>1) < V(s\<^sub>0)"
    using B_next assms(3) less.prems(1) less.prems(2) by force
  show ?case
  proof (cases "b s\<^sub>1")
    case True
    obtain tr\<^sub>1 s' where chain: "(b, s\<^sub>1) \<turnstile> B \<midarrow>tr\<^sub>1\<leadsto>\<^sub>\<checkmark> s' \<and> \<not> b s'"
      using True dec inv less.hyps by presburger
    then show ?thesis
      by (meson B_next less.prems term_chain_step) 
  next
    case False
    then show ?thesis
      by (metis B_next iterate_term_chain_iff iterate_term_once less.prems(2)) 
  qed  
qed

lemma terminates_iterate_wellorder_variant:
  fixes V :: "'s \<Rightarrow> 'a::wellorder" and I :: "'s \<Rightarrow> bool"
  assumes 
    "\<And> s\<^sub>0. \<lbrakk> b s\<^sub>0; I s\<^sub>0 \<rbrakk> \<Longrightarrow> terminates (B s\<^sub>0)"
    "\<And> s\<^sub>0 s\<^sub>1 tr. \<lbrakk> b s\<^sub>0; I s\<^sub>0; B(s\<^sub>0) \<midarrow>tr\<leadsto> \<checkmark> s\<^sub>1 \<rbrakk> \<Longrightarrow> I s\<^sub>1"
    "\<And> s\<^sub>0 s\<^sub>1 tr. \<lbrakk> b s\<^sub>0; I s\<^sub>0; B(s\<^sub>0) \<midarrow>tr\<leadsto> \<checkmark> s\<^sub>1 \<rbrakk> \<Longrightarrow> V(s\<^sub>1) < V(s\<^sub>0)"
    "I s"
  shows "terminates (iterate b B s)"
proof (cases "b s")
  case True
  have "\<exists> tr s'. (b, s) \<turnstile> B \<midarrow>tr\<leadsto>\<^sub>\<checkmark> s' \<and> \<not> b s'"
    by (rule wellorder_variant_term_chain[of b I B V], simp_all add: assms True)
  then show ?thesis
    by (metis iterate_term_chain_iff terminates_def)
  next
  case False
  then show ?thesis
    by (simp add: terminates_def)
qed

text \<open> Generalised deadlock freedom check for loops. If @{term B} (the condition) @{term P} are 
  sufficient to establish deadlock freedom of @{term C}, and @{term P} is an invariant of @{term C}, 
  which holds also in the initial state @{term s}, then @{term "loop C s"} is also deadlock free. \<close>

lemma deadlock_free_iterate:
  assumes cond_dlockf: "\<And> s. \<lbrakk> B s; P s \<rbrakk> \<Longrightarrow> deadlock_free (C s)" 
  and invariant: "\<And> s s'. \<lbrakk> P s; s' \<in> \<^bold>R(C s) \<rbrakk> \<Longrightarrow> P s'"
  and initial: "P s"
  shows "deadlock_free (iterate B C s)"
proof (simp add: deadlock_free_def deadlock_def, clarify)
  fix tr 
  assume "iterate B C s \<midarrow>tr\<leadsto> Vis {\<mapsto>}"
  thus False
  proof (cases rule: iterate_chain)
    case (iterates chn s\<^sub>0 tr\<^sub>0 P' n)
    with initial invariant have "\<forall> s\<in>chain_states chn. P s"
      by (rule_tac chain_invariant_simple[where s="s" and C="C" and s'="s\<^sub>0"], auto)
    hence dlckf_C_s\<^sub>0: "deadlock_free (C s\<^sub>0)"
      by (metis cond_dlockf final_state_in_chain initial iterates(1) iterates(2) iterates(3) itree_chain.cases list.discI)
    with iterates(6) show False
    proof (cases rule: bind_VisE')
      case (initial F')
      then show ?thesis
        by (metis deadlock_def deadlock_free_def dlckf_C_s\<^sub>0 iterates(4) pdom_empty_iff_dom_empty pdom_map_pfun)
    next
      case (continue s')
      have "iterate B C s' = Vis {\<mapsto>}"
        by (metis comp_apply continue(2) deadlock_def deadlock_trace_to trace_of_Sils)
      then show ?thesis
        by (metis (no_types, lifting) \<open>\<forall>s\<in>chain_states chn. P s\<close> cond_dlockf continue(1) deadlock_def deadlock_free_def deadlock_trace_to final_state_in_chain initial invariant iterate_VisE iterates(2) iterates(4) itree_chain.simps list.distinct(1) pdom_empty_iff_dom_empty pdom_map_pfun pdom_zero retvals_traceI)
    qed
  next
    case terms
    then show ?thesis
      by blast
  qed
qed

lemma deadlock_free_loop:
  assumes cond_dlockf: "\<And> s. P s \<Longrightarrow> deadlock_free (C s)" 
  and invariant: "\<And> s s'. \<lbrakk> P s; s' \<in> \<^bold>R(C s) \<rbrakk> \<Longrightarrow> P s'"
  and initial: "P s"
  shows "deadlock_free (loop C s)"
  using assms by (auto intro: deadlock_free_iterate)
    
end