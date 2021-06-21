section \<open> Interaction Trees \<close>

theory Interaction_Trees
  imports "HOL-Library.Monad_Syntax" "HOL-Library.BNF_Corec" "HOL-Library.Prefix_Order"
  "Z_Toolkit.Partial_Fun" "HOL-Library.Countable_Set_Type"
begin

subsection \<open> Preliminaries \<close>

type_notation pfun (infixr "\<Zpfun>" 0)
notation pdom_res (infixr "\<Zdres>" 66)
abbreviation ndres (infixr "\<Zndres>" 66) where "ndres A P \<equiv> (- A) \<Zdres> P"

declare [[coercion pfun_app]]
declare [[coercion_enabled]]

consts tick :: "'a \<Rightarrow> 'b" ("\<cmark>")

subsection \<open> Interaction Tree Type \<close>

codatatype ('e, 'r) itree = 
  Ret 'r | \<comment> \<open> Terminate, returning a value \<close>
  Tau "('e, 'r) itree cset" | \<comment> \<open> Internal choice \<close>
  Vis "'e \<Zpfun> ('e, 'r) itree" \<comment> \<open> Visible events choosing the continuation \<close>

print_theorems

definition Sil ("\<tau>") where
"Sil P = Tau (csingle P)"

definition "is_Sil P = (is_Tau P \<and> (\<exists> P'. un_Tau P = csingle P'))"

lemma is_Sil [simp]: "is_Sil (Sil P)" "is_Sil (Ret x) \<Longrightarrow> False" "is_Sil (Vis F) \<Longrightarrow> False"
  by (simp_all add: Sil_def is_Sil_def)

lemma Sil_dists [simp]: "Sil P \<noteq> Vis F" "Vis F \<noteq> Sil P" "Sil P \<noteq> Ret x" "Ret x \<noteq> Sil P"
  by (simp_all add: Sil_def)

definition "un_Sil P = (SOME P'. P = Tau (csingle P'))"

lemma un_Sil [simp]: "un_Sil (Sil P) = P"
  by (simp add: Sil_def un_Sil_def)

definition "miracle = Tau cempty"

adhoc_overloading tick Ret

syntax
  "_gchoice"      :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<bbar> _ \<in> _ \<rightarrow> _" [0, 0, 100] 100)
  "_gchoice_UNIV" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<bbar> _ \<rightarrow> _" [0, 100] 100)

translations
  "\<bbar> e \<in> E \<rightarrow> P" == "CONST Vis (\<lambda> e \<in> E \<bullet> P)"
  "\<bbar> e \<rightarrow> P" == "CONST Vis (\<lambda> e \<bullet> P)"

text \<open> A stable process has no possible internal activity \<close>

abbreviation "unstable P \<equiv> is_Tau P"
abbreviation "stable P \<equiv> \<not> unstable P"

translations "CONST stable P" <= "\<not> CONST unstable P"

lemma stable_Ret [intro]: "stable (Ret x)"
  by simp

lemma stable_Vis [intro]: "stable (Vis F)"
  by simp

lemma unstableE: "\<lbrakk> unstable P; \<And> P'. P = Tau P' \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  using is_Tau_def by auto

lemma stableE:
  assumes "stable P" "is_Ret P \<Longrightarrow> Q" "is_Vis P \<Longrightarrow> Q"
  shows Q
  by (metis assms(1) assms(2) assms(3) itree.exhaust_disc)

lemma is_VisE [elim]: "\<lbrakk> is_Vis P; \<And> x. P = Vis x \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  using is_Vis_def by blast

lemma is_RetE [elim]: "\<lbrakk> is_Ret P; \<And> x. P = Ret x \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (metis (mono_tags, hide_lams) is_Ret_def)

notation cin (infix "\<in>\<^sub>c" 50)

theorem itree_coind[elim, consumes 1, case_names wform Ret Tau Vis, induct pred: "HOL.eq"]:
  assumes "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q) \<and> (is_Tau P \<longleftrightarrow> is_Tau Q) \<and> (is_Vis P \<longleftrightarrow> is_Vis Q)" and
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> A B. \<phi> (Tau A) (Tau B) \<Longrightarrow> (\<forall> P. P \<in>\<^sub>c A \<longrightarrow> (\<exists> Q. Q \<in>\<^sub>c B \<and> \<phi> P Q))" and
  "\<And> A B. \<phi> (Tau A) (Tau B) \<Longrightarrow> (\<forall> Q. Q \<in>\<^sub>c B \<longrightarrow> (\<exists> P. P \<in>\<^sub>c A \<and> \<phi> P Q))" and
  "\<And> F G. \<phi> (Vis F) (Vis G) \<Longrightarrow> (pdom(F) = pdom(G) \<and> (\<forall> x\<in>pdom(F). \<phi> (F x) (G x)))"
  shows "P = Q"
  using assms
  apply (coinduct rule: itree.coinduct, auto simp add: relt_pfun_iff rel_cset_iff)
  apply (metis (no_types, lifting) itree.collapse(2))
  apply (metis (mono_tags, hide_lams) itree.collapse(2))
  done

theorem itree_strong_coind[elim, consumes 1, case_names wform Ret Sil Vis, induct pred: "HOL.eq"]:
  assumes phi: "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q) \<and> (is_Tau P \<longleftrightarrow> is_Tau Q) \<and> (is_Vis P \<longleftrightarrow> is_Vis Q)" and
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> A B. \<phi> (Tau A) (Tau B) \<Longrightarrow> (\<forall> P. P \<in>\<^sub>c A \<longrightarrow> (\<exists> Q. Q \<in>\<^sub>c B \<and> (\<phi> P Q \<or> P = Q)))" and
  "\<And> A B. \<phi> (Tau A) (Tau B) \<Longrightarrow> (\<forall> Q. Q \<in>\<^sub>c B \<longrightarrow> (\<exists> P. P \<in>\<^sub>c A \<and> (\<phi> P Q \<or> P = Q)))" and
  "\<And> F G. \<phi> (Vis F) (Vis G) \<Longrightarrow> (pdom(F) = pdom(G) \<and> (\<forall> x\<in>pdom(F). \<phi> (F x) (G x) \<or> F x = G x))"
  shows "P = Q"
  using assms
  apply (coinduct rule: itree.coinduct_strong, auto elim!: is_VisE simp add: relt_pfun_iff rel_cset_iff)
  apply (metis (no_types, hide_lams) itree.collapse(2))
  apply (metis (no_types, hide_lams) itree.collapse(2))
  done

text \<open> Up-to technique would add a functor on. Respectful closure and enhancement. 
 cf. "Coinduction all the way up". Davide Sangiorgi. Replace R \<subseteq> F(R) prove R \<subseteq> C(F(R)). \<close>

text \<open> Configuring the code generator; either partial functions or associative lists can be used
  in specifying choice functions. \<close>

code_datatype pfun_of_alist pfun_of_map

subsection \<open> Internal Choice \<close>

text \<open> A first attempt at internal choice. How does this interact with divergence? \<close>

primcorec ichoice :: "('e, 's) itree \<Rightarrow> ('e, 's) itree \<Rightarrow> ('e, 's) itree" where
"ichoice P Q = 
  (case (P, Q) of
     (Tau A, Tau B) \<Rightarrow> Tau (cUn A B) |
     (Tau A, _) \<Rightarrow> Tau (cinsert Q A) |
     (_, Tau B) \<Rightarrow> Tau (cinsert P B) |
     _ \<Rightarrow> Tau (cinsert P (csingle Q)))"

lemma "ichoice miracle (Tau A) = Tau A"
  by (simp add: ichoice.code miracle_def)

subsection \<open> Kleisli Trees and Monads \<close>

type_synonym ('e, 'r, 's) ktree = "'r \<Rightarrow> ('e, 's) itree"
type_synonym ('e, 'r) htree = "('e, 'r, 'r) ktree"

term cimage

primcorec (exhaustive) bind_itree :: "('e, 'r) itree \<Rightarrow> ('r \<Rightarrow> ('e, 's) itree) \<Rightarrow> ('e, 's) itree" where
"bind_itree u k = 
  (case u of
    \<comment> \<open> Pass the returned value to the continuation; the silent event is needed for friendliness. \<close>
    Ret r \<Rightarrow> (k r) | 
    \<comment> \<open> Execute the silent action and then the remainder of the binding. \<close>
    Tau A \<Rightarrow> Tau (cimage (\<lambda> t. bind_itree t k) A) | 
    \<comment> \<open> Apply the binding function to every possible continuation (non-trivial). \<close>
    Vis t \<Rightarrow> Vis (map_pfun (\<lambda> x. bind_itree x k) t))"

print_theorems

lemma map_pfun_alt_def: "map_pfun f g = pfun_of_map (map_option f \<circ> pfun_lookup g)"
  by (simp add: map_pfun_def)

adhoc_overloading bind bind_itree

lemma bind_Ret [simp, code]: "Ret v \<bind> k = (k v)"
  by (simp add: bind_itree.code)

lemma bind_Tau [simp, code]: "Tau A \<bind> k = Tau (cimage (\<lambda> t. t \<bind> k) A)"
  by (simp add: bind_itree.ctr)

lemma bind_Sil [simp, code]: "Sil t \<bind> k = Sil (t \<bind> k)"
  by (simp add: bind_itree.ctr Sil_def)

lemma bind_Vis [simp, code]: "Vis t \<bind> k = Vis (map_pfun (\<lambda> x. bind_itree x k) t)"
  by (auto simp add: bind_itree.ctr option.case_eq_if fun_eq_iff)

definition [simp]: "kleisli_comp bnd f g = (\<lambda> x. bnd (f x) g)"

syntax
  "_kleisli_comp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<Zcomp>" 54)

translations
  "P \<Zcomp> Q" == "CONST kleisli_comp (CONST bind) P Q"

text \<open> A bind cannot evaluate to simply a @{const Ret} because the @{term P} and @{term Q} must both
  minimally terminate. \<close>

lemma bind_RetE [elim]:
  assumes "P \<bind> Q = Ret x"
  obtains y where "P = Ret y" "Q y = Ret x"
  by (metis (no_types, hide_lams) assms bind_Ret bind_itree.disc_iff(1) is_Ret_def)
  
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

lemma bind_Tau_dest:
  "P \<bind> Q = Tau A \<Longrightarrow> ((\<exists> B P'. P = Tau B \<and> A = cimage (\<lambda> t. t \<bind> Q) B) \<or> (\<exists> x. P = Ret x \<and> Tau A = Q x))"
  by (auto, metis bind_Ret bind_Tau bind_Vis itree.distinct(5) itree.exhaust itree.inject(2))

lemma bind_TauE [elim]:
  assumes "(P \<bind> Q) = Tau A"
    "\<And> B. \<lbrakk> P = Tau B; A = cimage (\<lambda> t. t \<bind> Q) B \<rbrakk> \<Longrightarrow> R"
    "\<And> x. \<lbrakk> P = Ret x; Tau A = Q x \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms(1) assms(2) assms(3) bind_Ret bind_Tau bind_itree.disc_iff(2) is_Tau_def itree.collapse(1) itree.sel(2))

lemma bind_TauE' [elim]:
  assumes "Tau A = (P \<bind> Q)"
    "\<And> B. \<lbrakk> P = Tau B; A = cimage (\<lambda> t. t \<bind> Q) B \<rbrakk> \<Longrightarrow> R"
    "\<And> x. \<lbrakk> P = Ret x; Tau A = Q x \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms(1) assms(2) assms(3) bind_TauE cset.map_cong0)

lemma miracle_bind [simp]: "miracle \<bind> P = miracle"
  by (simp add: miracle_def)

(* Is this true? *)

lemma bind_Sil_dest:
  "P \<bind> Q = Sil R \<Longrightarrow> ((\<exists> P'. P = Sil P' \<and> R = P' \<bind> Q) \<or> (\<exists> x. P = Ret x \<and> Sil R = Q x))"
  apply (simp add: Sil_def, drule bind_Tau_dest, auto)
  oops

lemma bind_SilE [elim]:
  assumes "(P \<bind> Q) = Sil X"
    "\<And> P'. \<lbrakk> P = Sil P'; X = P' \<bind> Q \<rbrakk> \<Longrightarrow> R"
    "\<And> x. \<lbrakk> P = Ret x; Sil X = Q x \<rbrakk> \<Longrightarrow> R"
  shows R
  oops

lemma bind_SilE' [elim]:
  assumes "Sil X = (P \<bind> Q)"
    "\<And> P'. \<lbrakk> P = Sil P'; X = P' \<bind> Q \<rbrakk> \<Longrightarrow> R"
    "\<And> x. \<lbrakk> P = Ret x; Sil X = Q x \<rbrakk> \<Longrightarrow> R"
  shows R
  oops

lemma bind_itree_right_unit:
  shows "P \<bind> Ret = P"
  by (coinduction arbitrary: P rule: itree_strong_coind, auto)

lemma bind_itree_assoc:
  fixes P :: "('e, 's) itree"
  shows "P \<bind> (\<lambda> x. (Q x \<bind> R)) = (P \<bind> Q) \<bind> R"
  apply (coinduction arbitrary: P Q R rule: itree_strong_coind)
     apply (smt (verit, best) bind_Ret bind_itree.disc(2) bind_itree.disc_iff(3) itree.collapse(1) itree.distinct_disc(1) itree.distinct_disc(3) itree.distinct_disc(6) itree.exhaust_disc)
    apply force
   apply (auto elim!: bind_TauE')
  apply auto[1]
  apply blast
  apply (metis itree.sel(2))
  apply auto[1]
  apply blast
  apply (metis itree.sel(2))
  apply (auto elim!: bind_VisE')
  apply metis
  done

friend_of_corec bind_itree :: "('e, 'r) itree \<Rightarrow> ('r \<Rightarrow> ('e, 'r) itree) \<Rightarrow> ('e, 'r) itree" where
"bind_itree u k = 
  (case u of 
    Ret r \<Rightarrow> 
      (case k r of 
         Ret x \<Rightarrow> Ret x |
         Vis F \<Rightarrow> Vis F |
         Tau A \<Rightarrow> Tau A) |
    Tau A \<Rightarrow> Tau (cimage (\<lambda> t. bind_itree t k) A) | 
    Vis t \<Rightarrow> Vis (map_pfun (\<lambda> x. bind_itree x k) t))"
   apply (simp add: bind_itree.code)
   apply (metis (no_types, hide_lams) itree.case_eq_if itree.collapse(1) itree.collapse(2) itree.collapse(3) itree.exhaust_disc)
  apply transfer_prover
  done

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
  apply (coinduction rule: itree_coind)
      apply (metis bind_itree.disc(3) itree.distinct_disc(3) itree.distinct_disc(6) run.disc_iff)
     apply (metis itree.disc(7) run.disc_iff)
    apply (metis itree.disc(8) run.disc_iff)
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
  by (metis Sil_def Sils.elims is_Ret_def itree.disc(4) itree.disc(5) less_Suc_eq_0_disj less_numeral_extra(3))

lemma is_Vis_Sils [simp]: "is_Vis (Sils n P) \<longleftrightarrow> n = 0 \<and> is_Vis P"
  by (metis Sil_def Sils.elims itree.disc(5) itree.distinct_disc(6) less_Suc_eq_0_disj less_numeral_extra(3))

lemma is_Sil_Sils: "is_Sil (Sils n P) \<longleftrightarrow> (n > 0 \<or> is_Sil P)"
  by (metis Sils.elims Sils.simps(1) is_Sil(1) neq0_conv)

lemma un_Sil_Sils [simp]: "un_Sil (Sils n P) = (if n = 0 then un_Sil P else Sils (n - 1) P)"
  by (cases n, simp_all)

lemma Sils_Sils [simp]: "Sils m (Sils n P) = Sils (m + n) P"
  by (induct m, simp_all)

lemma Sil_injective [simp]: "Sil P = Sil Q \<longleftrightarrow> P = Q"
  by (metis Sil_def csingleton_inject itree.inject(2))

lemma Sils_injective: "Sils n P = Sils n Q \<Longrightarrow> P = Q"
  by (induct n, simp_all)

lemma Vis_Sils: "Vis F = Sils n (Vis G) \<longleftrightarrow> (n = 0 \<and> F = G)"
  by (metis Sils.simps(1) is_Vis_Sils itree.disc(9) itree.sel(3))

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

(*
lemma bind_Sils_dest:
  "P \<bind> Q = Sils n R \<Longrightarrow> 
  ((\<exists> P'. P = Sils n P' \<and> R = P' \<bind> Q) 
    \<or> (\<exists> x m. m \<le> n \<and> P = Sils m (Ret x) \<and> Q x = Sils (n - (m)) R))"
  apply (induct n arbitrary: P Q R)
   apply (auto)[1]
  apply (simp)
  apply (erule bind_SilE)
   apply (metis (no_types, hide_lams) Sils.simps(2) Suc_le_mono diff_Suc_Suc)
  apply (metis Sils.simps(1) Sils.simps(2) diff_zero zero_le)
  done

lemma bind_SilsE:
  assumes "(P \<bind> Q) = Sils n X"
    "\<And> P'. \<lbrakk> P = Sils n P'; P' \<bind> Q = X \<rbrakk> \<Longrightarrow> R"
    "\<And> x m. \<lbrakk> m \<le> n; P = Sils m (Ret x); Q x = Sils (n - m) X \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms(1) assms(2) assms(3) bind_Sils_dest by blast  
*)

subsection \<open> Operational Semantics and Traces \<close>

inductive trace_to :: "('e, 's) itree \<Rightarrow> 'e list \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" ("_ \<midarrow>_\<leadsto> _" [55, 0, 55] 55) where
trace_to_Nil [intro]: "P \<midarrow>[]\<leadsto> P" | 
trace_to_Tau [intro]: "\<lbrakk> P \<in>\<^sub>c A; P \<midarrow>tr\<leadsto> P' \<rbrakk> \<Longrightarrow> Tau A \<midarrow>tr\<leadsto> P'" |
trace_to_Vis [intro]: "\<lbrakk> e \<in> pdom F; F e \<midarrow>tr\<leadsto> P' \<rbrakk> \<Longrightarrow> Vis F \<midarrow>e # tr\<leadsto> P'"

inductive_cases
  trace_to_VisE [elim]: "Vis F \<midarrow>tr\<leadsto> P" and
  trace_to_RetE [elim]: "Ret x \<midarrow>tr\<leadsto> P" and
  trace_to_TauE [elim]: "Tau P \<midarrow>tr\<leadsto> P'" and
  trace_to_SilE [elim]: "Sil P \<midarrow>tr\<leadsto> P'"

lemma trace_to_Sil [intro]: "P \<midarrow>tr\<leadsto> P' \<Longrightarrow> Sil P \<midarrow>tr\<leadsto> P'"
  by (auto simp add: Sil_def)

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
  case (trace_to_Tau P A tr' P' tr)
  then show ?case
    by (meson trace_to.trace_to_Tau)
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
    apply (induct_tac rule: trace_to.induct, auto simp add: assms)
    apply (metis Sils.simps(1))
  thus ?thesis
    using assms by fastforce
qed

lemma trace_to_NilE [elim]:
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
  using Sils_Vis_inj apply blast
  apply (metis Sils_Vis_trns Vis_Cons_trns trace_to_ConsE trace_to_singleE)
  done

text \<open> An interaction tree cannot lead to both termination and a visible event. \<close>

lemma trace_to_Ret_excl_Vis:
  "\<lbrakk> P \<midarrow>tr\<leadsto> Ret v; P \<midarrow>tr\<leadsto> Vis F \<rbrakk> \<Longrightarrow> False"
  apply (induct tr arbitrary: P)
  apply (metis Sils_Vis_not_Ret trace_to_NilE)
  apply (metis Sils_Vis_trns Vis_Cons_trns trace_to_ConsE trace_to_singleE)
  done

text \<open> Termination is deterministic. \<close>

lemma termination_determinsitic: "\<lbrakk> P \<midarrow>tr\<leadsto> Ret x; P \<midarrow>tr\<leadsto> Ret y \<rbrakk> \<Longrightarrow> x = y"
  by (induct tr arbitrary: P, auto)
     (metis Sils_to_Ret Vis_Cons_trns trace_to_ConsE trace_to_singleE)

end