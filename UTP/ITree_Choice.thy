section \<open> Generalised Choice \<close>

theory ITree_Choice
  imports "Interaction_Trees.ITrees" "Optics.Optics" "Circus_Toolkit.Channels_Events"
begin

text \<open> Generalised choice is parametric over a function to merge the choice functions. \<close>

type_synonym ('e, 'a) chomerge = "(('e \<Zpfun> ('e, 'a) itree) \<Rightarrow> ('e \<Zpfun> ('e, 'a) itree) \<Rightarrow> 'e \<Zpfun> ('e, 'a) itree)" 

primcorec 
  genchoice :: "('e, 'a) chomerge 
                \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'a) itree"  where
"genchoice \<M> P Q =
   (case (P, Q) of 
      (Vis F, Vis G) \<Rightarrow> Vis (\<M> F G) |
      (Sil P', _) \<Rightarrow> Sil (genchoice \<M> P' Q) | \<comment> \<open> Maximal progress \<close>
      (_, Sil Q') \<Rightarrow> Sil (genchoice \<M> P Q') |
      \<comment> \<open> cf. Butterfield's external choice miraculous issue and a quantum-like computation with reconciliation \<close>
      (Ret x, Ret y) \<Rightarrow> if (x = y) then Ret x else Vis {}\<^sub>p |
      (Ret v, Vis _) \<Rightarrow> Ret v | \<comment> \<open> Is this like sliding choice? \<close>
      (Vis _, Ret v) \<Rightarrow> Ret v
   )"

lemma genchoice_Vis_Vis [simp]: "genchoice \<M> (Vis F) (Vis G) = Vis (\<M> F G)"
  by (simp add: genchoice.code)

lemma genchoice_diverge: "genchoice \<M> diverge P = diverge"
  by (coinduction arbitrary: P, auto elim!: stableE is_RetE is_VisE unstableE, metis diverge.code itree.simps(11))

lemma is_Sil_genchoice: "is_Sil (genchoice \<M> P Q) = (is_Sil P \<or> is_Sil Q)"
  using itree.exhaust_disc by (auto)

lemma genchoice_Vis_iff: 
  "genchoice \<M> P Q = Vis H \<longleftrightarrow> ((\<exists> F G. P = Vis F \<and> Q = Vis G \<and> H = (\<M> F G)) \<or> (\<exists> x y. P = Ret x \<and> Q = Ret y \<and> x \<noteq> y \<and> H = {}\<^sub>p))"
  (is "?lhs = ?rhs")
proof
  assume a: ?lhs
  hence is_Vis: "is_Vis (genchoice \<M> P Q)"
    by simp
  thus ?rhs
    apply (auto elim!: is_RetE is_VisE)
    using a
     apply (simp_all add: a genchoice.code)
    done
next
  assume ?rhs
  thus ?lhs
    by (auto simp add: genchoice.code)
qed

lemma genchoice_VisE [elim]:
  assumes "Vis H = genchoice \<M> P Q"
  "\<And> F G. \<lbrakk> P = Vis F; Q = Vis G; H = (\<M> F G) \<rbrakk> \<Longrightarrow> R"
  "\<And> x y. \<lbrakk> P = Ret x; Q = Ret y; x \<noteq> y; H = {}\<^sub>p \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms(1) assms(2) assms(3) genchoice_Vis_iff)

lemma genchoice_Sils: "genchoice \<M> (Sils m P) Q = Sils m (genchoice \<M> P Q)"
  by (induct m, simp_all add: genchoice.code)

lemma genchoice_Sil_stable: "stable P \<Longrightarrow> genchoice \<M> P (Sil Q) = Sil (genchoice \<M> P  Q)"
  by (cases P, simp_all add: genchoice.code)

lemma genchoice_Sils_stable: "stable P \<Longrightarrow> genchoice \<M> P (Sils m Q) = Sils m (genchoice \<M> P Q)"
  by (induct m, simp_all add: genchoice_Sil_stable)

lemma genchoice_Sils': "genchoice \<M> P (Sils m Q) = Sils m (genchoice \<M> P Q)"
proof (cases "divergent P")
  case True
  then show ?thesis
    by (metis Sils_diverge genchoice_diverge diverges_then_diverge) 
next
  case False
  then obtain n P' where "Sils n P' = P" "stable P'"
    using stabilises_def by blast
  then show ?thesis
    by (metis Sils_Sils add.commute genchoice_Sils genchoice_Sils_stable)
qed

lemma genchoice_deadlock_left [simp]: 
  assumes "\<And> F. \<M> {}\<^sub>p F = F"
  shows "genchoice \<M> deadlock P = P"
proof (coinduction arbitrary: P rule: itree_strong_coind)
  case wform
then show ?case
  by (simp add: deadlock_def) 
next
  case (Ret x y)
  then show ?case
    by (metis (no_types, lifting) deadlock_def genchoice.ctr(1) itree.collapse(1) itree.disc(9) itree.discI(1) itree.inject(1) itree.simps(12) prod.sel(1) prod.sel(2)) 
next
  case (Sil P' Q' P)
  then show ?case
    by (metis genchoice_Sil_stable itree.inject(2) stable_deadlock)
next
  case Vis
  then show ?case
    by (metis assms deadlock_def genchoice_Vis_Vis itree.inject(3)) 
qed

lemma genchoice_deadlock_right [simp]: 
  assumes "\<And> F. \<M> F {}\<^sub>p = F"
  shows "genchoice \<M> P deadlock = P"
proof (coinduction arbitrary: P rule: itree_strong_coind)
  case wform
  then show ?case
  by (simp add: deadlock_def) 
next
  case Ret
  then show ?case
    by (metis (no_types, lifting) deadlock_def genchoice.ctr(1) itree.case_eq_if itree.collapse(1) itree.disc(9) itree.discI(1) itree.inject(1) itree.simps(12) prod.sel(1) prod.sel(2)) 
next
  case Sil
  then show ?case
    by (metis genchoice.sel(2) itree.case(2) itree.disc(5) itree.sel(2) prod.sel(1))
next
  case Vis
  then show ?case
    by (metis assms deadlock_def genchoice_Vis_Vis itree.inject(3))
qed

lemma genchoice_Sil': "genchoice \<M> P (Sil Q) = genchoice \<M> (Sil P) Q"
proof (coinduction arbitrary: P Q rule: itree_strong_coind)
case wform
  then show ?case
    by (meson is_Sil_genchoice itree.disc(2) itree.disc(8) itree.distinct_disc(1) itree.distinct_disc(6) itree.exhaust_disc)
next
  case Ret
  then show ?case
    by (metis is_Sil_genchoice itree.disc(4) itree.disc(5)) 
next
  case (Sil P Q P' Q')
  then show ?case
    by (metis Sils.simps(1) Sils.simps(2) genchoice_Sils genchoice_Sils' itree.sel(2))    
next
  case Vis
  then show ?case
    by (metis is_Sil_genchoice itree.disc(5) itree.disc(6)) 
qed

lemma genchoice_unstable: "unstable P \<Longrightarrow> genchoice \<M> P Q = Sil (genchoice \<M> (un_Sil P) Q)"
  by (metis (no_types, lifting) genchoice.ctr(2) itree.case(2) itree.collapse(2) prod.sel(1))

lemma genchoice_unstable': "unstable Q \<Longrightarrow> genchoice \<M> P Q = Sil (genchoice \<M> P (un_Sil Q))"
  by (metis genchoice_Sil' genchoice_Sil_stable genchoice_unstable itree.collapse(2))

lemma genchoice_commute:
  fixes P Q :: "('e, 's) itree"
  assumes "\<And> F. \<M> F {}\<^sub>p = F" "\<And> F. \<M> {}\<^sub>p F = F"
  shows "genchoice \<M> P Q = genchoice (\<lambda> F G. \<M> G F) Q P"
proof (coinduction arbitrary: P Q rule: itree_coind)
  case wform
  then show ?case
    by (metis genchoice.disc_iff(1) genchoice.disc_iff(3) itree.distinct_disc(1) itree.distinct_disc(6) itree.exhaust_disc prod.sel(1) prod.sel(2))
next
  case Ret
  then show ?case
    by (smt genchoice.disc_iff(1) genchoice.simps(3) genchoice.simps(4) itree.case_eq_if itree.disc(7) itree.sel(1) prod.sel(1) snd_conv un_Ret_def)
next
  case (Sil P Q P' Q')
  then show ?case
  proof (cases "unstable P'")
    case True
    with Sil have "P = genchoice \<M> (un_Sil P') Q'" "Q = genchoice (\<lambda> F G. \<M> G F) Q' (un_Sil P')"
      by (simp_all add: genchoice_unstable genchoice_unstable')
    thus ?thesis
      by blast
  next
    case False
      then show ?thesis
        by (metis Sil(1) Sil(2) genchoice_Sil' genchoice_unstable' is_Sil_genchoice itree.disc(5) itree.sel(2) unstableE)
  qed
next
  case Vis
  then show ?case
    using assms by (auto elim!: genchoice_VisE, metis genchoice_deadlock_left genchoice_deadlock_right)
qed

lemma genchoice_commutative:
  fixes P Q :: "('e, 's) itree"
  assumes "\<And> F. \<M> F {}\<^sub>p = F" "\<And> F. \<M> {}\<^sub>p F = F" "\<And> F G. \<M> F G = \<M> G F"
  shows "genchoice \<M> P Q = genchoice \<M> Q P"
  by (subst genchoice_commute, simp_all add: assms)

lemma Ret_unit_stable_genchoice_left: 
  assumes "stable P"
  shows "genchoice \<M> (Ret ()) P = Ret ()"
  by (metis (mono_tags, opaque_lifting) assms genchoice.disc_iff(1) is_Ret_def itree.exhaust_disc old.unit.exhaust prod.sel(1) prod.sel(2))

lemma Ret_unit_stable_genchoice_right:
  assumes "stable P"
  shows "genchoice \<M> P (Ret ()) = Ret ()"
  by (metis (mono_tags, opaque_lifting) assms genchoice.disc_iff(1) is_Ret_def itree.exhaust_disc old.unit.exhaust prod.sel(1) prod.sel(2))

lemma genchoice_RetE [elim]:
  assumes "genchoice \<M> P Q = \<checkmark> x" 
    "\<lbrakk> P = Ret x; Q = Ret x\<rbrakk> \<Longrightarrow> R"
    "\<lbrakk> P = Ret x; is_Vis Q \<rbrakk> \<Longrightarrow> R"
    "\<lbrakk> Q = Ret x; is_Vis P \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms by (cases P, auto simp add: genchoice.code itree.case_eq_if, meson itree.exhaust_disc)


end
