section \<open> Interaction Trees \<close>

theory Interaction_Trees
  imports "HOL-Library.Monad_Syntax" "HOL-Library.BNF_Corec" "HOL-Library.Prefix_Order"
begin

subsection \<open> Interaction Tree Type \<close>

notation Map.empty ("[\<mapsto>]")

abbreviation "rel_map R \<equiv> rel_fun (=) (rel_option R)"

lemma rel_map_iff: 
  "rel_map R f g \<longleftrightarrow> (dom(f) = dom(g) \<and> (\<forall> x\<in>dom(f). R (the (f x)) (the (g x))))"
  apply (auto simp add: rel_fun_def)
  apply (metis not_None_eq option.rel_distinct(2))
  apply (metis not_None_eq option.rel_distinct(1))
  apply (metis option.rel_sel option.sel option.simps(3))
  apply (metis domIff option.rel_sel)
  done

codatatype ('e, 'r) itree = 
  Ret 'r | \<comment> \<open> Terminate, returning a value \<close>
  Sil "('e, 'r) itree" | \<comment> \<open> Invisible event \<close>
  Vis "'e \<rightharpoonup> ('e, 'r) itree" \<comment> \<open> Visible events choosing the continuation \<close>

text \<open> A stable process has no possible internal activity \<close>

abbreviation "unstable P \<equiv> is_Sil P"
abbreviation "stable P \<equiv> \<not> unstable P"

translations "CONST stable P" <= "\<not> CONST unstable P"

lemma stable_Ret [intro]: "stable (Ret x)"
  by simp

lemma stable_Vis [intro]: "stable (Vis F)"
  by simp

lemma unstableE: "\<lbrakk> unstable P; \<And> P'. P = Sil P' \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  using is_Sil_def by auto

theorem itree_coind[elim, consumes 1, case_names wform Ret Sil Vis, induct pred: "HOL.eq"]:
  assumes "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q) \<and> (is_Sil P \<longleftrightarrow> is_Sil Q) \<and> (is_Vis P \<longleftrightarrow> is_Vis Q)" and
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> P Q. \<phi> (Sil P) (Sil Q) \<Longrightarrow> \<phi> P Q" and
  "\<And> F G. \<phi> (Vis F) (Vis G) \<Longrightarrow> (dom(F) = dom(G) \<and> (\<forall> x\<in>dom(F). \<phi> (the (F x)) (the (G x))))"
  shows "P = Q"
  using assms
  by (coinduct rule: itree.coinduct, auto simp add: rel_map_iff)

theorem itree_strong_coind[elim, consumes 1, case_names wform Ret Sil Vis, induct pred: "HOL.eq"]:
  assumes phi: "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q) \<and> (is_Sil P \<longleftrightarrow> is_Sil Q) \<and> (is_Vis P \<longleftrightarrow> is_Vis Q)" and
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> P Q. \<phi> (Sil P) (Sil Q) \<Longrightarrow> \<phi> P Q \<or> P = Q" and
  "\<And> F G. \<phi> (Vis F) (Vis G) \<Longrightarrow> (dom(F) = dom(G) \<and> (\<forall> x\<in>dom(F). \<phi> (the (F x)) (the (G x)) \<or> (the (F x)) = (the (G x))))"
  shows "P = Q"
  using assms
  by (coinduct rule: itree.coinduct_strong, auto simp add: rel_map_iff)

text \<open> Up-to technique would add a functor on. Respectful closure and enhancement. 
 cf. "Coinduction all the way up". Davide Sangiorgi. Replace R \<subseteq> F(R) prove R \<subseteq> C(F(R)). \<close>

subsection \<open> Kleisli Trees and Monad \<close>

type_synonym ('e, 'r) ktree = "'r \<Rightarrow> ('e, 'r) itree"

primcorec (exhaustive) bind_itree :: "('e, 'r) itree \<Rightarrow> ('r \<Rightarrow> ('e, 's) itree) \<Rightarrow> ('e, 's) itree" where
"bind_itree u k = 
  (case u of 
    Ret r \<Rightarrow> Sil (k r) | 
    Sil t \<Rightarrow> Sil (bind_itree t k) | 
    Vis t \<Rightarrow> Vis (\<lambda> e.
      case t e of
        None \<Rightarrow> None |
        Some x \<Rightarrow> Some (bind_itree x k)))"

print_theorems

friend_of_corec bind_itree :: "('e, 'r) itree \<Rightarrow> ('r \<Rightarrow> ('e, 'r) itree) \<Rightarrow> ('e, 'r) itree" where
"bind_itree u k = 
  (case u of 
    Ret r \<Rightarrow> Sil (k r) | 
    Sil t \<Rightarrow> Sil (bind_itree t k) | 
    Vis t \<Rightarrow> Vis (\<lambda> e.
      case t e of
        None \<Rightarrow> None |
        Some x \<Rightarrow> Some (bind_itree x k)))"
  by (simp add: bind_itree.code, transfer_prover)

adhoc_overloading bind bind_itree

lemma bind_Ret [simp]: "Ret v \<bind> k = Sil (k v)"
  by (simp add: bind_itree.ctr(1))

lemma bind_Sil [simp]: "Sil t \<bind> k = Sil (t \<bind> k)"
  by (simp add: bind_itree.ctr)

lemma bind_Vis [simp]: "Vis t \<bind> k = Vis (\<lambda> e. t e \<bind> (\<lambda> x. Some (x \<bind> k)))"
  by (auto simp add: bind_itree.ctr option.case_eq_if fun_eq_iff)

term "(\<circ>\<^sub>m) F' (Some \<circ> Q)"

definition [simp]: "kleisli_comp bnd f g = (\<lambda> x. bnd (f x) g)"

syntax
  "_kleisli_comp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<Zcomp>" 54)

translations
  "P \<Zcomp> Q" == "CONST kleisli_comp (CONST bind) P Q"

term "P \<bind> Q = Vis F \<Longrightarrow> (\<exists> F'. P = Vis F' \<and> F = F' \<Zcomp> (\<lambda> t. Some (t \<bind> Q)))"

thm bind_itree.simps

text \<open> A bind cannot evaluate to simply a @{const Ret} because the @{term P} and @{term Q} must both
  minimally terminate. \<close>

lemma bind_RetE [elim!]:
  assumes "P \<bind> Q = Ret x"
  shows False
  by (metis assms bind_itree.disc(1) bind_itree.disc(2) itree.disc(7) itree.exhaust_disc stable_Ret)

lemma bind_VisE:
  assumes "P \<bind> Q = Vis F"
  obtains F' where "Vis F' = P" "F = (F' \<Zcomp> (\<lambda> t. Some (t \<bind> Q)))"
proof -
  obtain F' where "Vis F' = P"
    by (metis assms bind_itree.disc_iff(2) is_Vis_def)
  moreover with assms have "F = (F' \<Zcomp> (\<lambda> t. Some (t \<bind> Q)))"
    by (auto simp add: fun_eq_iff)
  ultimately show ?thesis
    using that by force
qed

lemma bind_Sil_dest:
  "P \<bind> Q = Sil R \<Longrightarrow> ((\<exists> P'. P = Sil P' \<and> R = P' \<bind> Q) \<or> (\<exists> x. P = Ret x \<and> R = Q x))"
  by (metis bind_itree.disc_iff(1) bind_itree.simps(3) itree.case_eq_if itree.collapse(1) itree.collapse(2) itree.disc(5) itree.sel(2))

lemma bind_SilE:
  assumes "(P \<bind> Q) = Sil X"
    "\<And> P'. \<lbrakk> P = Sil P'; X = P' \<bind> Q \<rbrakk> \<Longrightarrow> R"
    "\<And> x. \<lbrakk> P = Ret x; X = Q x \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms bind_Sil_dest by blast

subsection \<open> Transitive Silent Steps \<close>

fun Sils :: "nat \<Rightarrow> ('e, 's) itree \<Rightarrow> ('e, 's) itree" where
"Sils 0 P = P" |
"Sils (Suc n) P = Sil (Sils n P)"

lemma Sils_0 [intro]: "Sils 0 P = P"
  by (simp)

lemma is_Ret_Sils [simp]: "is_Ret (Sils n P) \<longleftrightarrow> n = 0 \<and> is_Ret P"
  by (metis Sils.elims itree.disc(2) less_numeral_extra(3) zero_less_Suc)

lemma is_Vis_Sils [simp]: "is_Vis (Sils n P) \<longleftrightarrow> n = 0 \<and> is_Vis P"
  by (metis Sils.elims Sils.simps(1) itree.disc(8))

lemma is_Sil_Sils: "is_Sil (Sils n P) \<longleftrightarrow> (n > 0 \<or> is_Sil P)"
  by (metis Sils.simps(1) is_Ret_Sils is_Vis_Sils itree.exhaust_disc neq0_conv)

lemma un_Sil_Sils [simp]: "un_Sil (Sils n P) = (if n = 0 then un_Sil P else Sils (n - 1) P)"
  by (cases n, simp_all)

lemma Sils_Sils [simp]: "Sils m (Sils n P) = Sils (m + n) P"
  by (induct m, simp_all)

lemma Sils_injective: "Sils n P = Sils n Q \<Longrightarrow> P = Q"
  by (induct n, simp_all)

lemma Vis_Sils: "Vis F = Sils n (Vis G) \<longleftrightarrow> (n = 0 \<and> F = G)"
  by (metis Sils.elims is_Vis_Sils itree.disc(8) itree.disc(9) itree.inject(3))

lemma Sils_Vis_inj: "Sils m (Vis F) = Sils n (Vis G) \<Longrightarrow> (m = n \<and> F = G)"
  apply (induct m, auto simp add: Vis_Sils)
  apply (induct n, auto)
   apply (metis Sils.elims is_Vis_Sils itree.disc(9))
  apply (induct n, auto)
  apply (metis Sils.elims Vis_Sils)
  done 

lemma Vis_not_Sils_Ret: "Vis F = Sils n (Ret x) \<Longrightarrow> False"
  by (metis is_Vis_Sils itree.disc(7) itree.disc(9))

lemma Sils_Vis_not_Ret: "Sils m (Vis F) = Sils n (Ret x) \<Longrightarrow> False"
  apply (induct m, auto dest: Vis_not_Sils_Ret)
  apply (induct n, auto)
  apply (metis Sils.elims Vis_not_Sils_Ret)
  done

lemma Sils_Vis_iff: "Sils m (Vis F) = Sils n (Vis G) \<longleftrightarrow> (m = n \<and> F = G)"
  by (auto simp add: Sils_Vis_inj)

lemma bind_Sils [simp]: "Sils n P \<bind> Q = Sils n (P \<bind> Q)"
  by (induct n; simp)


lemma Sils_Sil_shift [simp]: "Sils n (Sil P) = Sil (Sils n P)"
  by (metis Sils.simps(1) Sils.simps(2) Sils_Sils add_Suc_right)


lemma bind_Sils_dest:
  "P \<bind> Q = Sils n R \<Longrightarrow> 
  ((\<exists> P'. P = Sils n P' \<and> R = P' \<bind> Q) 
    \<or> (\<exists> x m. m < n \<and> P = Sils m (Ret x) \<and> Q x = Sils (n - (m + 1)) R))"
  apply (induct n arbitrary: P Q R)
   apply (auto)[1]
  apply (simp)
  apply (erule bind_SilE)
   apply (metis Sils.simps(2) Suc_less_eq)
  apply (metis Sils.simps(1) diff_zero zero_less_Suc)
  done

lemma bind_SilsE:
  assumes "(P \<bind> Q) = Sils n X"
    "\<And> P'. \<lbrakk> P = Sils n P'; P' \<bind> Q = X \<rbrakk> \<Longrightarrow> R"
    "\<And> x m. \<lbrakk> m < n; P = Sils m (Ret x); Q x = Sils (n - (m + 1)) X \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms(1) assms(2) assms(3) bind_Sils_dest by blast
  
subsection \<open> Operational Semantics and Traces \<close>

inductive trace_to :: "('e, 's) itree \<Rightarrow> 'e list \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" ("_ \<midarrow>_\<leadsto> _" [55, 0, 55] 55) where
trace_to_Nil [intro]: "P \<midarrow>[]\<leadsto> P" | 
trace_to_Sil [intro]: "P \<midarrow>tr\<leadsto> P' \<Longrightarrow> Sil P \<midarrow>tr\<leadsto> P'" |
trace_to_Vis [intro]: "\<lbrakk> e \<in> dom F; the (F e) \<midarrow>tr\<leadsto> P' \<rbrakk> \<Longrightarrow> Vis F \<midarrow>e # tr\<leadsto> P'"

inductive_cases
  trace_toE [elim]: "P \<midarrow>tr\<leadsto> P'"

lemma trace_to_Sils [intro]: "P \<midarrow>tr\<leadsto> P' \<Longrightarrow> Sils n P \<midarrow>tr\<leadsto> P'"
  by (induct n, auto)

lemma trace_to_Ret: "Ret x \<midarrow>tr\<leadsto> P \<Longrightarrow> (tr, P) = ([], Ret x)"
  by (erule trace_toE, simp_all)

lemma trace_of_Sils [intro]: "Sils n P \<midarrow>[]\<leadsto> P"
  by (induct n, auto)

lemma trace_to_prefix_closed:
  assumes "P \<midarrow>tr'\<leadsto> Q" "tr \<le> tr'"
  shows "\<exists> P'. P \<midarrow>tr\<leadsto> P'"
  using assms proof (induct arbitrary: tr rule: trace_to.induct)
  case (trace_to_Nil P)
  then show ?case by (auto)
next
  case (trace_to_Sil P tr' P' tr)
  then show ?case by (auto)
next
  case (trace_to_Vis e F tr' P' tr)
  then show ?case
  proof (cases "tr = []")
    case True
    then show ?thesis by auto
  next
    case False
    then obtain tr'' where tr: "tr = e # tr''" "tr'' \<le> tr'"
      by (meson Prefix_Order.prefix_Cons trace_to_Vis.prems)
    moreover then obtain P'' where "the (F e) \<midarrow>tr''\<leadsto> P''"
      using trace_to_Vis.hyps(3) by presburger
    with trace_to_Vis tr show ?thesis
      by auto      
  qed
qed

lemma trace_to_Nil_Sils:
  assumes "P \<midarrow>[]\<leadsto> P'" 
  shows "\<exists> n. Sils n P' = P"
proof - 
  have "\<And> tr. P \<midarrow>tr\<leadsto> P' \<Longrightarrow> tr = [] \<longrightarrow> (\<exists> n. P = Sils n P')"
    by (induct_tac rule: trace_to.induct, auto
       , metis (mono_tags) Sils_0, metis (mono_tags) Sils.simps(2))
  thus ?thesis
    using assms by fastforce
qed

lemma trace_to_NilE:
  assumes "P \<midarrow>[]\<leadsto> P'" 
  obtains n where "P = Sils n P'"
  using assms trace_to_Nil_Sils by auto

lemma trace_to_ConsE:
  assumes "P \<midarrow>x # xs\<leadsto> Q" 
  obtains P' where "P \<midarrow>[x]\<leadsto> P'" "P' \<midarrow>xs\<leadsto> Q"
proof -
  have "\<And> tr. P \<midarrow>tr\<leadsto> Q \<Longrightarrow> tr \<noteq> [] \<longrightarrow> (\<exists>P'. P \<midarrow>[hd tr]\<leadsto> P' \<and> P' \<midarrow>tl tr\<leadsto> Q)"
  proof -
    fix tr
    assume "P \<midarrow>tr\<leadsto> Q"
    thus "tr \<noteq> [] \<longrightarrow> (\<exists>P'. P \<midarrow>[hd tr]\<leadsto> P' \<and> P' \<midarrow>tl tr\<leadsto> Q)"
      by (induct rule: trace_to.induct, auto)
  qed
  thus ?thesis
    by (metis assms list.distinct(1) list.sel(1) list.sel(3) that)
qed

lemma trace_to_singleE [elim!]:
  assumes "P \<midarrow>[a]\<leadsto> P'"
  obtains m n F  where "P = Sils m (Vis F)" "a \<in> dom F" "F a = Some (Sils n P')"
proof -
  have "\<And> tr. P \<midarrow>tr\<leadsto> P' \<Longrightarrow> (length tr = 1 \<longrightarrow> (\<exists> m n F. P = Sils m (Vis F) \<and> hd tr \<in> dom F \<and> F (hd tr) = Some (Sils n P')))"
    apply (induct_tac rule: trace_to.induct)
       apply (auto)
      apply (metis Sils.simps(2) domI)
     apply (metis Sils.simps(1) domI trace_to_Nil_Sils)
    apply (metis Vis_Sils domI trace_to_Nil_Sils)
    done
  thus ?thesis
    by (metis One_nat_def assms length_Cons list.sel(1) list.size(3) that)
qed

lemma trace_to_single_iff: "P \<midarrow>[a]\<leadsto> P' \<longleftrightarrow> (\<exists> m n F. P = Sils m (Vis F) \<and> a \<in> dom F \<and> F a = Some (Sils n P'))"
  by (metis option.sel trace_of_Sils trace_to_Sils trace_to_Vis trace_to_singleE)

lemma trace_to_Cons [intro]:
  "\<lbrakk> P \<midarrow>[x]\<leadsto> P'; P' \<midarrow>xs\<leadsto> P'' \<rbrakk> \<Longrightarrow> P \<midarrow>x # xs\<leadsto> P''"
  by force

lemma trace_to_trans:
  "\<lbrakk> P \<midarrow>tr\<leadsto> P'; P' \<midarrow>tr'\<leadsto> P'' \<rbrakk> \<Longrightarrow> P \<midarrow>tr @ tr'\<leadsto> P''"
  apply (induct tr arbitrary: P P' P'' tr')
   apply (auto  elim: trace_to_NilE trace_to_ConsE)
  apply (meson trace_to_Cons trace_to_ConsE)
  done  

lemma trace_to_bind_left:
  assumes "P \<midarrow>tr\<leadsto> P'"
  shows "(P \<bind> Q) \<midarrow>tr\<leadsto> (P' \<bind> Q)"
using assms proof (induct tr arbitrary: P)
  case Nil
  then show ?case
    by (metis bind_Sils trace_of_Sils trace_to_NilE) 
next
  case (Cons a tr)
  obtain P'' where P'': "P \<midarrow>[a]\<leadsto> P''" "P'' \<midarrow>tr\<leadsto> P'"
    by (meson Cons.prems trace_to_ConsE)
  with Cons(1)[OF P''(2)] show ?case
    apply (rule_tac trace_to_Cons)
     apply (auto)
    apply (rule trace_to_Sils)
    apply (rule trace_to_Vis)
     apply (auto)
    done    
qed

lemma trace_to_bind:
  assumes "P \<midarrow>tr\<leadsto> Ret x" "Q x \<midarrow>tr'\<leadsto> Q'"
  shows "(P \<bind> Q) \<midarrow>tr @ tr'\<leadsto> Q'"
proof -
  have "(P \<bind> Q) \<midarrow>tr\<leadsto> (Ret x \<bind> Q)"
    by (meson assms(1) trace_to_bind_left)
  moreover have "(Ret x \<bind> Q) \<midarrow>tr'\<leadsto> Q'"
    by (auto simp add: assms)
  ultimately show ?thesis
    by (simp add: trace_to_trans)
qed

inductive_cases
  ttb: "(P \<bind> Q) \<midarrow>tr\<leadsto> Q'"

thm ttb
thm trace_to.induct

lemma Sil_to_Ret [simp]: "Sil P \<midarrow>xs\<leadsto> Ret x \<longleftrightarrow> P \<midarrow>xs\<leadsto> Ret x"
  by (auto)

lemma Sils_to_Ret [simp]: "Sils n P \<midarrow>tr\<leadsto> Ret x \<longleftrightarrow> P \<midarrow>tr\<leadsto> Ret x"
  by (induct n, auto)

lemma trace_to_bind_Nil_cases:
  assumes 
    "(P \<bind> Q) \<midarrow>[]\<leadsto> Q'"
  shows "(\<exists> P'. P \<midarrow>[]\<leadsto> P' \<and> Q' = (P' \<bind> Q)) 
          \<or> (\<exists> x. P \<midarrow>[]\<leadsto> Ret x \<and> Q x \<midarrow>[]\<leadsto> Q')"
  using assms
  apply (erule_tac ttb)
    apply (auto)[1]
  apply (erule bind_SilE)
  apply (simp)
  apply (auto)
  apply (metis bind_Sils_dest trace_of_Sils trace_to_Nil_Sils trace_to_Sil)
  done

lemma trace_to_bind_single_cases:
  assumes 
    "(P \<bind> Q) \<midarrow>[a]\<leadsto> Q'"
  shows "(\<exists> P'. P \<midarrow>[a]\<leadsto> P' \<and> (P' \<bind> Q) = Q') 
          \<or> (\<exists> x. P \<midarrow>[a]\<leadsto> Ret x \<and> Q x \<midarrow>[]\<leadsto> Q')
          \<or> (\<exists> x. P \<midarrow>[]\<leadsto> Ret x \<and> Q x \<midarrow>[a]\<leadsto> Q')"
  using assms
  apply (erule_tac trace_to_singleE)
    apply (auto)[1]
  apply (erule bind_SilsE)
   apply (simp)
   apply (erule bind_VisE)
  apply (auto simp add: bind_eq_Some_conv)
  apply (metis domI option.sel trace_of_Sils trace_to_Sils trace_to_Vis trace_to_bind_Nil_cases)
  apply (metis domI option.sel trace_to_Nil trace_to_Sils trace_to_Vis)
  done

lemma [simp]: "Sils n (Vis F) \<midarrow>x # xs\<leadsto> P' \<longleftrightarrow> (Vis F \<midarrow>x # xs\<leadsto> P')"
  by (smt (verit, ccfv_threshold) Sils_Vis_inj option.sel trace_to_ConsE trace_to_Sils trace_to_Vis trace_to_singleE)
  
lemma trace_to_bind_cases:
  assumes 
    "(P \<bind> Q) \<midarrow>tr\<leadsto> Q'"
  shows "(\<exists> P'. P \<midarrow>tr\<leadsto> P' \<and> Q' = (P' \<bind> Q)) 
          \<or> (\<exists> x tr\<^sub>1 tr\<^sub>2. P \<midarrow>tr\<^sub>1\<leadsto> Ret x \<and> Q x \<midarrow>tr\<^sub>2\<leadsto> Q' \<and> tr = tr\<^sub>1 @ tr\<^sub>2)"
  using assms
  apply (induct tr arbitrary: P Q Q')
   apply (simp add: trace_to_bind_Nil_cases)
  apply (erule trace_to_ConsE)
  apply (auto)
  apply (erule bind_SilsE)
  apply (erule bind_VisE)
  apply (auto)
  apply (rule)
  apply (rule)
  apply (rule trace_to_Cons)

lemma "\<lbrakk> P \<midarrow>tr\<leadsto> P'; (P \<bind> Q) \<midarrow>tr'\<leadsto> Q' \<rbrakk> \<Longrightarrow> tr \<le> tr'"
  apply (erule_tac ttb)
    apply (auto)
  apply (simp)

lemma trace_to_bind_cases:
  assumes 
    "(P \<bind> Q) \<midarrow>tr\<leadsto> Q'"
  shows "(\<exists> P'. P \<midarrow>tr\<leadsto> P' \<and> Q' = (P' \<bind> Q)) 
          \<or> (\<exists> x tr\<^sub>1 tr\<^sub>2. P \<midarrow>tr\<^sub>1\<leadsto> Ret x \<and> Q x \<midarrow>tr\<^sub>2\<leadsto> Q' \<and> tr = tr\<^sub>1 @ tr\<^sub>2)"
  using assms
  apply (induct tr)
  apply (simp)
  apply (erule_tac ttb)
  apply (simp)
     apply blast
   apply (erule bind_SilE)
    apply (simp)
    apply (rule disjI1)
    apply (rule)
  apply (rule)
  apply (auto)
proof (induct rule: trace_to.induct )
  case (trace_to_Nil P')
  then show ?case apply (simp)
next
  case (trace_to_Sil P tr P')
  then show ?case sorry
next
  case (trace_to_Vis e F tr P')
  then show ?case sorry
qed
case (trace_to_Nil P)
  then show ?case 
    apply (auto)
next
  case (trace_to_Sil P tr P')
  then show ?case sorry
next
  case (trace_to_Vis e F tr P')
  then show ?case sorry
qed

lemma trace_to_bindE:
  assumes 
    "(P \<bind> Q) \<midarrow>tr\<leadsto> Q'"
    "\<And> P'. \<lbrakk> P \<midarrow>tr\<leadsto> P'; Q' = (P' \<bind> Q) \<rbrakk> \<Longrightarrow> R"
    "\<And> x tr\<^sub>1 tr\<^sub>2. \<lbrakk> P \<midarrow>tr\<^sub>1\<leadsto> Ret x; Q x \<midarrow>tr\<^sub>2\<leadsto> Q'; tr = tr\<^sub>1 @ tr\<^sub>2 \<rbrakk> \<Longrightarrow> R"
  shows "R"
  using assms
  apply (induct arbitrary: P Q rule: trace_to.induct)
  apply (auto)

subsection \<open> Weak Bisimulation \<close>

coinductive wbisim :: "('e, 's) itree \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" (infix "\<approx>" 50) where
wbisim_sym: "P \<approx> Q \<Longrightarrow> Q \<approx> P" |
wbisim_Ret [intro]: "Ret x \<approx> Ret x" |
wbisim_Sil [intro]: "P \<approx> Q \<Longrightarrow> Sil P \<approx> Q" |
wbisim_Vis [intro]: "\<lbrakk> dom(F) = dom(G); \<And> e. e \<in> dom(F) \<Longrightarrow> the (F e) \<approx> the (G e) \<rbrakk> \<Longrightarrow> Vis F \<approx> Vis G"

lemma wbisim_refl: "P \<approx> P"
  by (coinduction arbitrary: P, auto)

lemma wbisim_trans: "\<lbrakk> P \<approx> Q; Q \<approx> R \<rbrakk> \<Longrightarrow> P \<approx> R"
  by (coinduction arbitrary: P Q R, auto intro: wbisim_sym)

text \<open> For CCS, weak bisimulation is not a congruence with respect to choice. Hence, Milner creates
  a derived relation, observation congruence, which adds the requirement that an initial silent
  action must be matched by a silent action in the other process. This is an issue because $\tau$
  can resolve a choice in CCS. \<close>

end