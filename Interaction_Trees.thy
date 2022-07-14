section \<open> Interaction Trees \<close>

theory Interaction_Trees
  imports "HOL-Library.Monad_Syntax" "HOL-Library.BNF_Corec" "HOL-Library.Prefix_Order"
  "Z_Toolkit.Relation_Toolkit"
begin

subsection \<open> Preliminaries \<close>

unbundle Z_Type_Syntax

text \<open> Allow partial functions to be written with braces \<close>

syntax "_Pfun"     :: "maplets => ('a, 'b) pfun"            ("(1{_})")

notation pempty ("{\<mapsto>}")

consts tick :: "'a \<Rightarrow> 'b" ("\<checkmark>")

subsection \<open> Interaction Tree Type \<close>

codatatype ('e, 'r) itree = 
  Ret 'r | \<comment> \<open> Terminate, returning a value \<close>
  Sil "('e, 'r) itree" ("\<tau>") | \<comment> \<open> Invisible event \<close>
  Vis "'e \<Zpfun> ('e, 'r) itree" \<comment> \<open> Visible events choosing the continuation \<close>

adhoc_overloading tick Ret

syntax
  "_gchoice"      :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<bbar> _ \<in> _ \<rightarrow> _" [0, 0, 100] 100)
  "_gchoice_UNIV" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<bbar> _ \<rightarrow> _" [0, 100] 100)

translations
  "\<bbar> e \<in> E \<rightarrow> P" == "CONST Vis (\<lambda> e \<in> E \<bullet> P)"
  "\<bbar> e \<rightarrow> P" == "CONST Vis (\<lambda> e \<bullet> P)"

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

lemma stableE:
  assumes "stable P" "is_Ret P \<Longrightarrow> Q" "is_Vis P \<Longrightarrow> Q"
  shows Q
  by (metis assms(1) assms(2) assms(3) itree.exhaust_disc)

lemma is_VisE [elim]: "\<lbrakk> is_Vis P; \<And> x. P = Vis x \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  using is_Vis_def by blast

lemma is_RetE [elim]: "\<lbrakk> is_Ret P; \<And> x. P = Ret x \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (metis (mono_tags, opaque_lifting) is_Ret_def)

theorem itree_coind[elim, consumes 1, case_names wform Ret Sil Vis, induct pred: "HOL.eq"]:
  assumes "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q) \<and> (is_Sil P \<longleftrightarrow> is_Sil Q) \<and> (is_Vis P \<longleftrightarrow> is_Vis Q)" and
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> P Q. \<phi> (Sil P) (Sil Q) \<Longrightarrow> \<phi> P Q" and
  "\<And> F G. \<phi> (Vis F) (Vis G) \<Longrightarrow> (pdom(F) = pdom(G) \<and> (\<forall> x\<in>pdom(F). \<phi> (F x) (G x)))"
  shows "P = Q"
  using assms
  by (coinduct rule: itree.coinduct, auto simp add: relt_pfun_iff)

theorem itree_coind'[elim, consumes 1, case_names RetF SilF VisF Ret Sil Vis, induct pred: "HOL.eq"]:
  assumes "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q)"
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Sil P \<longleftrightarrow> is_Sil Q)"
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Vis P \<longleftrightarrow> is_Vis Q)"
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> P Q. \<phi> (Sil P) (Sil Q) \<Longrightarrow> \<phi> P Q" and
  "\<And> F G. \<phi> (Vis F) (Vis G) \<Longrightarrow> (pdom(F) = pdom(G) \<and> (\<forall> x\<in>pdom(F). \<phi> (F x) (G x)))"
  shows "P = Q"
  using assms
  by (coinduct rule: itree.coinduct, auto simp add: relt_pfun_iff)

theorem itree_strong_coind[elim, consumes 1, case_names wform Ret Sil Vis, induct pred: "HOL.eq"]:
  assumes phi: "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q) \<and> (is_Sil P \<longleftrightarrow> is_Sil Q) \<and> (is_Vis P \<longleftrightarrow> is_Vis Q)" and
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> P Q. \<phi> (Sil P) (Sil Q) \<Longrightarrow> \<phi> P Q \<or> P = Q" and
  "\<And> F G. \<phi> (Vis F) (Vis G) \<Longrightarrow> (pdom(F) = pdom(G) \<and> (\<forall> x\<in>pdom(F). \<phi> (F x) (G x) \<or> F x = G x))"
  shows "P = Q"
  using assms
  by (coinduct rule: itree.coinduct_strong, auto elim!: is_VisE simp add: relt_pfun_iff)

theorem itree_strong_coind'[elim, consumes 1, case_names RetF SilF VisF Ret Sil Vis, induct pred: "HOL.eq"]:
  assumes phi: "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q)"
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Sil P \<longleftrightarrow> is_Sil Q)"
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Vis P \<longleftrightarrow> is_Vis Q)"
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> P Q. \<phi> (Sil P) (Sil Q) \<Longrightarrow> \<phi> P Q \<or> P = Q" and
  "\<And> F G. \<phi> (Vis F) (Vis G) \<Longrightarrow> (pdom(F) = pdom(G) \<and> (\<forall> x\<in>pdom(F). \<phi> (F x) (G x) \<or> F x = G x))"
  shows "P = Q"
  using assms
  by (erule_tac itree_strong_coind, auto)

text \<open> Up-to technique would add a functor on. Respectful closure and enhancement. 
 cf. "Coinduction all the way up". Davide Sangiorgi. Replace @{term "R \<subseteq> F(R)"} prove @{term "R \<subseteq> C(F(R))"}. \<close>

subsection \<open> Kleisli Trees and Monads \<close>

type_synonym ('e, 'r, 's) ktree = "'r \<Rightarrow> ('e, 's) itree"
type_synonym ('e, 'r) htree = "('e, 'r, 'r) ktree"

primcorec (exhaustive) bind_itree :: "('e, 'r) itree \<Rightarrow> ('r \<Rightarrow> ('e, 's) itree) \<Rightarrow> ('e, 's) itree" where
"bind_itree u k = 
  (case u of
    \<comment> \<open> Pass the returned value to the continuation; the silent event is needed for friendliness. \<close>
    Ret r \<Rightarrow> (k r) | 
    \<comment> \<open> Execute the silent action and then the remainder of the binding. \<close>
    Sil t \<Rightarrow> Sil (bind_itree t k) | 
    \<comment> \<open> Apply the binding function to every possible continuation (non-trivial). \<close>
    Vis t \<Rightarrow> Vis (map_pfun (\<lambda> x. bind_itree x k) t))"

lemma map_pfun_alt_def: "map_pfun f g = pfun_of_map (map_option f \<circ> pfun_lookup g)"
  by (simp add: map_pfun_def)

adhoc_overloading bind bind_itree

lemma bind_Ret [simp, code]: "Ret v \<bind> k = (k v)"
  by (simp add: bind_itree.code)

lemma bind_Sil [simp, code]: "Sil t \<bind> k = Sil (t \<bind> k)"
  by (simp add: bind_itree.ctr)

lemma bind_Vis [simp, code]: "Vis t \<bind> k = Vis (map_pfun (\<lambda> x. bind_itree x k) t)"
  by (auto simp add: bind_itree.ctr option.case_eq_if fun_eq_iff)

definition "kleisli_comp bnd f g = (\<lambda> x. bnd (f x) g)"

syntax
  "_kleisli_comp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr ";;" 54)

translations
  "P ;; Q" == "CONST kleisli_comp (CONST bind) P Q"

text \<open> A bind cannot evaluate to simply a @{const Ret} because the @{term P} and @{term Q} must both
  minimally terminate. \<close>

lemma bind_RetE [elim]:
  assumes "P \<bind> Q = Ret x"
  obtains y where "P = Ret y" "Q y = Ret x"
  by (metis (no_types, opaque_lifting) assms bind_Ret bind_itree.disc_iff(1) is_Ret_def)
  
lemma bind_RetE' [elim]:
  assumes "Ret x = P \<bind> Q"
  obtains y where "P = Ret y" "Q y = Ret x"
  by (metis assms bind_RetE)

lemma bind_VisE [elim]:
  assumes "P \<bind> Q = Vis F"
    "\<And> F'. \<lbrakk> P = Vis F'; F = map_pfun (\<lambda> x. x \<bind> Q) F' \<rbrakk> \<Longrightarrow> R"
    "\<And> x. \<lbrakk> P = Ret x; Q x = Vis F \<rbrakk> \<Longrightarrow> R"
  shows "R"
  by (metis assms bind_Ret bind_Vis bind_itree.disc_iff(3) is_VisE itree.collapse(1) itree.disc(9) itree.sel(3))


lemma bind_VisE' [elim]:
  assumes "Vis F = P \<bind> Q"
    "\<And> F'. \<lbrakk> P = Vis F'; F = map_pfun (\<lambda> x. x \<bind> Q) F' \<rbrakk> \<Longrightarrow> R"
    "\<And> x. \<lbrakk> P = Ret x; Q x = Vis F \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms bind_VisE)

lemma bind_Sil_dest:
  "P \<bind> Q = Sil R \<Longrightarrow> ((\<exists> P'. P = Sil P' \<and> R = P' \<bind> Q) \<or> (\<exists> x. P = Ret x \<and> Sil R = Q x))"
  by (metis (no_types, lifting) bind_itree.code bind_itree.disc_iff(2) itree.case_eq_if itree.collapse(1) itree.collapse(2) itree.disc(5) itree.sel(2))
  
lemma bind_SilE [elim]:
  assumes "(P \<bind> Q) = Sil X"
    "\<And> P'. \<lbrakk> P = Sil P'; X = P' \<bind> Q \<rbrakk> \<Longrightarrow> R"
    "\<And> x. \<lbrakk> P = Ret x; Sil X = Q x \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms bind_Sil_dest by blast

lemma bind_SilE' [elim]:
  assumes "Sil X = (P \<bind> Q)"
    "\<And> P'. \<lbrakk> P = Sil P'; X = P' \<bind> Q \<rbrakk> \<Longrightarrow> R"
    "\<And> x. \<lbrakk> P = Ret x; Sil X = Q x \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms(1) assms(2) assms(3) bind_SilE)

lemma bind_itree_right_unit:
  shows "P \<bind> Ret = P"
  by (coinduction arbitrary: P rule: itree_strong_coind, auto)

lemma bind_itree_assoc:
  fixes P :: "('e, 's) itree"
  shows "P \<bind> (\<lambda> x. (Q x \<bind> R)) = (P \<bind> Q) \<bind> R"
proof (coinduction arbitrary: P Q R rule: itree_strong_coind')
  case RetF
  then show ?case by auto
next
  case SilF
  then show ?case by auto
next
  case VisF
  then show ?case by auto
next
  case Ret
  then show ?case by auto
next
  case Sil
  then show ?case by (auto elim!: bind_SilE', metis itree.sel(2))
next
  case Vis
  then show ?case by (force elim!: bind_VisE')
qed

friend_of_corec bind_itree :: "('e, 'r) itree \<Rightarrow> ('r \<Rightarrow> ('e, 'r) itree) \<Rightarrow> ('e, 'r) itree" where
"bind_itree u k = 
  (case u of 
    Ret r \<Rightarrow> 
      (case k r of 
         Ret x \<Rightarrow> Ret x |
         Vis F \<Rightarrow> Vis F |
         Sil P \<Rightarrow> Sil P) |
    Sil t \<Rightarrow> Sil (bind_itree t k) | 
    Vis t \<Rightarrow> Vis (map_pfun (\<lambda> x. bind_itree x k) t))"
   apply (simp add: bind_itree.code)
   apply (metis (no_types, opaque_lifting) itree.case_eq_if itree.collapse(1) itree.collapse(2) itree.collapse(3) itree.exhaust_disc)
  apply transfer_prover
  done

lemma kcomp_assoc: 
  fixes P :: "('e, 'r, 's) ktree" 
  shows "(P ;; Q) ;; R = P ;; (Q ;; R)"
  by (simp add: kleisli_comp_def fun_eq_iff bind_itree_assoc)

subsection \<open> Run \<close>

primcorec run :: "'e set \<Rightarrow> ('e, 's) itree" where
"run E = Vis (map_pfun (\<lambda> x. run E) (pId_on E))"

lemma Run_alt_def: "run E = (\<bbar> e \<in> E \<rightarrow> run E)"
proof -
  have "run E = Vis (map_pfun (\<lambda> x. run E) (pId_on E))"
    by (metis run.code)
  also have "... = \<bbar> x \<in> E \<rightarrow> run E"
    by (simp add: map_pfun_as_pabs)
  finally show ?thesis .
qed

lemma run_empty: "run {} = Vis {}\<^sub>p"
  by (metis (no_types, lifting) pdom_map_pfun pdom_pId_on pdom_res_empty pdom_res_pdom run.code)

lemma run_bind: "run E \<bind> K = run E"
  apply (coinduction rule: itree_coind')
  apply (meson bind_itree.disc(3) itree.distinct_disc(3) run.disc_iff)
  apply (meson bind_itree.disc(3) itree.distinct_disc(5) run.disc_iff)
  apply simp
  apply (metis itree.disc(7) run.disc_iff)
   apply (metis itree.disc(8) run.disc_iff)
  apply (smt (verit, best) bind_VisE itree.disc(7) itree.sel(3) map_pfun_apply pdom_map_pfun run.disc_iff run.sel)
  done  

subsection \<open> Transitive Silent Steps \<close>

fun Sils :: "nat \<Rightarrow> ('e, 's) itree \<Rightarrow> ('e, 's) itree" where
"Sils 0 P = P" |
"Sils (Suc n) P = Sil (Sils n P)"

lemma "Sils n P = (\<tau>^^n) P"
  by (induct n, simp_all)

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
    \<or> (\<exists> x m. m \<le> n \<and> P = Sils m (Ret x) \<and> Q x = Sils (n - (m)) R))"
  apply (induct n arbitrary: P Q R)
   apply (auto)[1]
  apply (simp)
  apply (erule bind_SilE)
   apply (metis (no_types, opaque_lifting) Sils.simps(2) Suc_le_mono diff_Suc_Suc)
  apply (metis Sils.simps(1) Sils.simps(2) diff_zero zero_le)
  done

lemma bind_SilsE:
  assumes "(P \<bind> Q) = Sils n X"
    "\<And> P'. \<lbrakk> P = Sils n P'; P' \<bind> Q = X \<rbrakk> \<Longrightarrow> R"
    "\<And> x m. \<lbrakk> m \<le> n; P = Sils m (Ret x); Q x = Sils (n - m) X \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms(1) assms(2) assms(3) bind_Sils_dest by blast  

lemma bind_SilsE':
  assumes "Sils n X = (P \<bind> Q)"
    "\<And> P'. \<lbrakk> P = Sils n P'; P' \<bind> Q = X \<rbrakk> \<Longrightarrow> R"
    "\<And> x m. \<lbrakk> m \<le> n; P = Sils m (Ret x); Q x = Sils (n - m) X \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms(1) assms(2) assms(3) bind_SilsE)

lemma Ret_Sils_iff [simp]: "Ret x = Sils n P \<longleftrightarrow> (n = 0 \<and> P = Ret x)"
  by (metis Sils.simps(1) is_Ret_Sils itree.disc(1))


lemma stabilises_eq_iff [simp]: 
  "\<lbrakk> stable P; stable Q \<rbrakk> \<Longrightarrow> Sils m P = Sils n Q \<longleftrightarrow> (m = n \<and> P = Q)"
  apply (induct m arbitrary: n P Q )
  apply (case_tac P, case_tac[!] Q)
  apply (auto dest: Vis_not_Sils_Ret simp add: Vis_Sils)
  apply (metis Sils.elims itree.disc(2) itree.disc(4) itree.discI(1) itree.sel(2))
  apply (metis Sils.elims itree.disc(4) itree.distinct(1) itree.sel(2))
  apply (metis Sils.elims itree.disc(6) itree.disc(8) itree.disc(9) itree.sel(2))
  apply (metis Sils.elims itree.disc(6) itree.distinct(5) itree.sel(2))
  done

subsection \<open> Operational Semantics and Traces \<close>

inductive trace_to :: "('e, 's) itree \<Rightarrow> 'e list \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" ("_ \<midarrow>_\<leadsto> _" [55, 0, 55] 55) where
trace_to_Nil [intro]: "P \<midarrow>[]\<leadsto> P" | 
trace_to_Sil [intro]: "P \<midarrow>tr\<leadsto> P' \<Longrightarrow> Sil P \<midarrow>tr\<leadsto> P'" |
trace_to_Vis [intro]: "\<lbrakk> e \<in> pdom F; F e \<midarrow>tr\<leadsto> P' \<rbrakk> \<Longrightarrow> Vis F \<midarrow>e # tr\<leadsto> P'"

inductive_cases
  trace_to_VisE [elim]: "Vis F \<midarrow>tr\<leadsto> P" and
  trace_to_RetE [elim]: "Ret x \<midarrow>tr\<leadsto> P" and
  trace_to_SilE [elim]: "Sil P \<midarrow>tr\<leadsto> P'"

lemma trace_to_Sils [intro]: "P \<midarrow>tr\<leadsto> P' \<Longrightarrow> Sils n P \<midarrow>tr\<leadsto> P'"
  by (induct n, auto)

lemma trace_to_Ret: "Ret x \<midarrow>tr\<leadsto> P \<Longrightarrow> (tr, P) = ([], Ret x)"
  by auto

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
    moreover then obtain P'' where "F e \<midarrow>tr''\<leadsto> P''"
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

lemma trace_to_NilE [elim]:
  assumes "P \<midarrow>[]\<leadsto> P'" 
  obtains n where "P = Sils n P'"
  using assms trace_to_Nil_Sils by auto

lemma trace_to_Nil_iff: "P \<midarrow>[]\<leadsto> P' \<longleftrightarrow> (\<exists> n. P = Sils n P')"
  by (meson trace_of_Sils trace_to_NilE)

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
  obtains m n F  where "P = Sils m (Vis F)" "a \<in> pdom F" "F a = Sils n P'"
proof -
  have "\<And> tr. P \<midarrow>tr\<leadsto> P' \<Longrightarrow> (length tr = 1 \<longrightarrow> (\<exists> m n F. P = Sils m (Vis F) \<and> hd tr \<in> pdom F \<and> F (hd tr) = Sils n P'))"
    apply (induct_tac rule: trace_to.induct)
       apply (auto)
      apply (metis Sils.simps(2))
     apply (metis Sils.simps(1) trace_to_Nil_Sils)
    apply (metis Vis_Sils trace_to_Nil_Sils)
    done
  thus ?thesis
    by (metis One_nat_def assms length_Cons list.sel(1) list.size(3) that)
qed

lemma trace_to_single_iff: "P \<midarrow>[a]\<leadsto> P' \<longleftrightarrow> (\<exists> m n F. P = Sils m (Vis F) \<and> a \<in> pdom F \<and> F a = Sils n P')"
  by (metis trace_of_Sils trace_to_Sils trace_to_Vis trace_to_singleE)

lemma trace_to_Cons [intro]:
  "\<lbrakk> P \<midarrow>[x]\<leadsto> P'; P' \<midarrow>xs\<leadsto> P'' \<rbrakk> \<Longrightarrow> P \<midarrow>x # xs\<leadsto> P''"
  by force

lemma trace_to_appendE:
  assumes "P \<midarrow>t\<^sub>1 @ t\<^sub>2\<leadsto> Q"
  obtains P' where "P \<midarrow>t\<^sub>1\<leadsto> P'" "P' \<midarrow>t\<^sub>2\<leadsto> Q"
  using assms by (induct t\<^sub>1 arbitrary: P, auto, meson trace_to_Cons trace_to_ConsE)

lemma trace_to_trans:
  "\<lbrakk> P \<midarrow>tr\<leadsto> P'; P' \<midarrow>tr'\<leadsto> P'' \<rbrakk> \<Longrightarrow> P \<midarrow>tr @ tr'\<leadsto> P''"
  apply (induct tr arbitrary: P P' P'' tr')
   apply (auto elim: trace_to_NilE trace_to_ConsE)
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
  apply (metis assms bind_Ret trace_to_Nil)
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
  apply (metis trace_of_Sils trace_to_Sils trace_to_Vis trace_to_bind_Nil_cases)
  apply (metis trace_to_Nil trace_to_Sils trace_to_Vis)
  apply (metis (full_types) trace_to_Nil trace_to_Sils trace_to_Vis)
  done

lemma Vis_Cons_trns [simp]: "Vis F' \<midarrow>a # tr\<leadsto> P' \<longleftrightarrow> (a \<in> pdom(F') \<and> F' a \<midarrow>tr\<leadsto> P')"
  by (auto)

lemma Ret_trns [simp]: "Ret x \<midarrow>tr\<leadsto> P \<longleftrightarrow> (tr = [] \<and> P = Ret x)"
  by auto

lemma Sils_Vis_trns [simp]: "Sils n (Vis F) \<midarrow>x # xs\<leadsto> P' \<longleftrightarrow> (Vis F \<midarrow>x # xs\<leadsto> P')"
  by (smt (verit, ccfv_threshold) Sils_Vis_inj option.sel trace_to_ConsE trace_to_Sils trace_to_Vis trace_to_singleE)

lemma Sils_Ret_trns [simp]: "Sils n (Ret x) \<midarrow>t # ts\<leadsto> P' \<longleftrightarrow> False"
  by (auto, metis Sils_Vis_not_Ret trace_to_ConsE trace_to_singleE)

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
  apply (auto simp add: bind_eq_Some_conv)
  apply (smt (verit) append_Cons append_Nil domI option.sel trace_of_Sils trace_to_Vis trace_to_trans)
  apply (metis trace_to_Sils trace_to_Vis)
  apply (metis trace_to_Sils trace_to_Vis)
  done

lemma trace_to_bindE:
  assumes 
    "(P \<bind> Q) \<midarrow>tr\<leadsto> Q'"
    "\<And> P'. \<lbrakk> P \<midarrow>tr\<leadsto> P'; Q' = (P' \<bind> Q) \<rbrakk> \<Longrightarrow> R"
    "\<And> x tr\<^sub>1 tr\<^sub>2. \<lbrakk> P \<midarrow>tr\<^sub>1\<leadsto> Ret x; Q x \<midarrow>tr\<^sub>2\<leadsto> Q'; tr = tr\<^sub>1 @ tr\<^sub>2 \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms(1) assms(2) assms(3) trace_to_bind_cases by blast

text \<open> If an interaction tree has terminated, no further interactions are possible. \<close>

lemma trace_to_Ret_end:
  "\<lbrakk> P \<midarrow>tr\<leadsto> Ret x; P \<midarrow>tr @ [e]\<leadsto> P' \<rbrakk> \<Longrightarrow> False"
  by (induct tr arbitrary: P P', auto)
     (metis Sils_Vis_trns Vis_Cons_trns trace_to_ConsE trace_to_singleE)

text \<open> If an event happened beyond a visible choice, then this must have resolved the choice. \<close>

lemma trace_to_determinstic_choice:
  "\<lbrakk> P \<midarrow>tr\<leadsto> Vis F; P \<midarrow>tr @ [e]\<leadsto> P' \<rbrakk> \<Longrightarrow> e \<in> pdom(F)"
  apply (induct tr arbitrary: P P', auto)
  apply (metis Sils_Vis_trns Vis_Cons_trns trace_to_ConsE trace_to_singleE)
  done

text \<open> An interaction tree cannot lead to both termination and a visible event. \<close>

lemma trace_to_Ret_excl_Vis:
  "\<lbrakk> P \<midarrow>tr\<leadsto> Ret v; P \<midarrow>tr\<leadsto> Vis F \<rbrakk> \<Longrightarrow> False"
  apply (induct tr arbitrary: P)
  apply (metis Sils_Vis_not_Ret trace_to_NilE)
  apply (metis Sils_Vis_trns Vis_Cons_trns trace_to_ConsE trace_to_singleE)
  done

lemma trace_to_Sil_dest [dest]: "P \<midarrow>tr\<leadsto> \<tau> P' \<Longrightarrow> P \<midarrow>tr\<leadsto> P'"
  by (metis append.right_neutral trace_to_Nil trace_to_Sil trace_to_trans)

lemma trace_to_post_Sil_iff:
  "(P \<bind> \<tau> \<circ> \<checkmark>) \<midarrow>es\<leadsto> \<checkmark> x \<longleftrightarrow> P \<midarrow>es\<leadsto> \<checkmark> x"
  apply (auto)
   apply (force elim: trace_to_bindE)
  apply (metis bind_Ret comp_eq_dest_lhs trace_to_Sil_dest trace_to_bind_left)
  done

text \<open> Termination is deterministic. \<close>

lemma termination_determinsitic: "\<lbrakk> P \<midarrow>tr\<leadsto> Ret x; P \<midarrow>tr\<leadsto> Ret y \<rbrakk> \<Longrightarrow> x = y"
  by (induct tr arbitrary: P, auto)
     (metis Sils_to_Ret Vis_Cons_trns trace_to_ConsE trace_to_singleE)

subsection \<open> Initial Events \<close>

definition initev :: "('e, 's) itree \<Rightarrow> 'e set" ("\<^bold>I") where
"\<^bold>I(P) = {e. (\<exists> P'. P \<midarrow>[e]\<leadsto> P')}"

lemma initev_Sil [simp]: "\<^bold>I(Sil P) = \<^bold>I(P)"
  apply (auto simp add: initev_def)
  apply (metis not_Cons_self2 trace_to_SilE trace_to_single_iff)
  apply blast
  done

lemma initev_Sils [simp]: "\<^bold>I(Sils n P) = \<^bold>I(P)"
  by (induct n, auto)

lemma initev_Vis [simp]: "\<^bold>I(Vis F) = pdom F"
  by (auto simp add: initev_def)

lemma initev_Ret [simp]: "\<^bold>I(Ret x) = {}"
  by (auto simp add: initev_def)

subsection \<open> Return Values \<close>

definition retvals :: "('e, 's) itree \<Rightarrow> 's set" ("\<^bold>R") where
"\<^bold>R(P) = {x. \<exists> es. P \<midarrow>es\<leadsto> Ret x}"

lemma retvals_traceI: "P \<midarrow>es\<leadsto> Ret x \<Longrightarrow> x \<in> \<^bold>R(P)"
  by (auto simp add: retvals_def)

abbreviation "nonterminates P \<equiv> (\<^bold>R(P) = {})"

abbreviation "terminates P \<equiv> (\<^bold>R(P) \<noteq> {})"

lemma nonterminates_iff: "nonterminates P \<longleftrightarrow> (\<forall> es x. \<not> P \<midarrow>es\<leadsto> \<checkmark> x)"
  by (auto simp add: retvals_def)

lemma retvals_Ret [simp]: "\<^bold>R(Ret x) = {x}"
  by (auto simp add: retvals_def)

lemma retvals_Sil [simp]: "\<^bold>R(Sil P) = \<^bold>R(P)"
  by (auto simp add: retvals_def)

lemma retvals_Vis [simp]: "\<^bold>R(Vis F) = \<Union> (\<^bold>R ` pran(F))"
  apply (auto simp add: retvals_def)
  apply (metis image_eqI itree.distinct(3) pran_pdom trace_to_VisE)
  apply (metis (no_types, lifting) image_iff pran_pdom trace_to_Vis)
  done

lemma retvals_bind [simp]: "\<^bold>R(P \<bind> Q) = \<Union> {\<^bold>R (Q x)| x. x \<in> \<^bold>R(P)}"
  apply (auto elim!: trace_to_bindE bind_RetE' simp add: retvals_def)
  apply (metis mem_Collect_eq trace_to_Nil)
  apply (meson trace_to_bind)
  done

subsection \<open> Event Alphabet \<close>

definition evalpha :: "('e, 's) itree \<Rightarrow> 'e set" ("\<^bold>A") where
"\<^bold>A(P) = \<Union> {set es | es. \<exists> P'. P \<midarrow>es\<leadsto> P'}"

lemma initev_subset_evalpha: "\<^bold>I(P) \<subseteq> \<^bold>A(P)"
  by (auto simp add: initev_def evalpha_def)
     (metis list.set_intros(1) trace_to_single_iff)

lemma evalpha_Sil [simp]: "\<^bold>A(Sil P) = \<^bold>A(P)"
  by (auto simp add: evalpha_def, metis equals0D set_empty trace_to_SilE)

lemma evalpha_Ret [simp]: "\<^bold>A(Ret x) = {}"
  by (auto simp add: evalpha_def)

lemma evalpha_Vis [simp]: "\<^bold>A(Vis F) = pdom(F) \<union> (\<Union> (\<^bold>A ` pran(F)))"
  apply (auto simp add: evalpha_def)
  apply (metis Vis_Cons_trns image_eqI list.set_cases pran_pdom)
   apply (metis list.set_intros(1) trace_to_Nil trace_to_Vis)
  apply (metis (no_types, lifting) imageE list.set_intros(2) pran_pdom trace_to_Vis)
  done

lemma evalpha_bind: "\<^bold>A(P \<bind> Q) = \<^bold>A(P) \<union> \<Union> {\<^bold>A (Q x)| x. x \<in> \<^bold>R(P)}"
  apply (auto elim!: trace_to_bindE bind_RetE' simp add: evalpha_def retvals_def)
     apply blast
    apply blast
   apply (metis trace_to_bind_left)
  apply (metis (no_types, opaque_lifting) append.assoc bind_Ret in_set_conv_decomp trace_to_bind_left trace_to_trans)
  done

end