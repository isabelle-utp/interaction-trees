section \<open> Generalised Parallel Composition \<close>

theory ITree_Parallel
  imports ITree_Choice
begin

text \<open> This parallel composition operator follows a similar approach to the UTP "parallel-by-merge" scheme. \<close>

datatype (discs_sels) ('a, 'b) andor = Left 'a | Right 'b | Both "'a \<times> 'b"

type_synonym ('e, 'a, 'b) pmerge = 
  "(('e \<Zpfun> ('e, 'a) itree) \<Rightarrow> 'e set \<Rightarrow> ('e \<Zpfun> ('e, 'b) itree) \<Rightarrow> 'e \<Zpfun> (('e, 'a) itree, ('e, 'b) itree) andor)"

primcorec genpar :: "('e, 'a, 'b) pmerge \<Rightarrow> ('e, 'a) itree \<Rightarrow> 'e set \<Rightarrow> ('e, 'b) itree \<Rightarrow> ('e, 'a \<times> 'b) itree" where
"genpar \<M> P A Q =
   (case (P, Q) of 
      \<comment> \<open> Silent events happen independently and have priority \<close>
      (Sil P', _) \<Rightarrow> Sil (genpar \<M> P' A Q) |
      (_, Sil Q') \<Rightarrow> Sil (genpar \<M> P A Q') |
      \<comment> \<open> Visible events are subject to synchronisation constraints \<close>
      (Vis F, Vis G) \<Rightarrow>
        Vis (map_pfun 
              (\<lambda>x. case x of 
                     Left P' \<Rightarrow> genpar \<M> P' A Q \<comment> \<open> Left side acts independently \<close>
                   | Right Q' \<Rightarrow> genpar \<M> P A Q' \<comment> \<open> Right side acts independently \<close> 
                   | Both (P', Q') \<Rightarrow> genpar \<M> P' A Q') \<comment> \<open> Both sides synchronise \<close>
              (\<M> F A G)) |
      \<comment> \<open> If both sides terminate, then they must agree on the returned value. This could be
           generalised using a merge function. \<close>
      (Ret x, Ret y) \<Rightarrow> Ret (x, y) |
      \<comment> \<open> A termination occurring on one side is pushed forward. Only events not requiring
           synchronisation can occur on the other side. \<close>
      (Ret v, Vis G)   \<Rightarrow> Vis (map_pfun (\<lambda> P. (genpar \<M> (Ret v) A P)) (A \<Zndres> G)) |
      (Vis F, Ret v)   \<Rightarrow> Vis (map_pfun (\<lambda> P. (genpar \<M> P A (Ret v))) (A \<Zndres> F))
   )" 

lemma genpar_Sil_left [simp]:
  "genpar \<M> (Sil P') E Q = Sil (genpar \<M> P' E Q)"
  by (simp add: genpar.code)

lemma genpar_Sil_stable_right:
  "stable P \<Longrightarrow> genpar \<M> P E (Sil Q') = Sil (genpar \<M> P E Q')"
  by (auto elim!: stableE simp add: genpar.code)

lemma unstable_genpar [simp]: "unstable (genpar \<M> P E Q) = (unstable P \<or> unstable Q)"
  by (auto elim!: stableE)

lemma genpar_Ret_iff: "Ret x = genpar \<M> P E Q \<longleftrightarrow> (\<exists> a b. P = Ret a \<and> Q = Ret b \<and> x = (a, b))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume a:?lhs
  hence "is_Ret (genpar \<M> P E Q)"
    by (metis itree.disc(1))
  then obtain a b where "P = Ret a" "Q = Ret b"
    by force
  with a show ?rhs
    by (simp add: genpar.code)
next
  show "?rhs \<Longrightarrow> ?lhs"
    by (auto simp add: genpar.code)
qed

lemma genpar_Sil_iff: "Sil R = genpar \<M> P E Q \<longleftrightarrow> ((\<exists> P'. P = Sil P' \<and> R = genpar \<M> P' E Q) \<or> (\<exists> Q'. stable P \<and> Q = Sil Q' \<and> R = genpar \<M> P E Q'))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume a:?lhs
  hence sil: "is_Sil (genpar \<M> P E Q)"
    by (metis (no_types, opaque_lifting) itree.disc(5))
  show ?rhs
  proof (cases "unstable P")
    case True
    with a show ?thesis
      by (auto elim!: unstableE simp add: genpar.code)
  next
    case False
    hence "unstable Q"
      by (metis sil unstable_genpar)
    with a False show ?thesis by (auto simp add: genpar_Sil_stable_right elim!: unstableE)
  qed
next
  show "?rhs \<Longrightarrow> ?lhs"
    by (auto simp add: genpar_Sil_stable_right)
qed
  
lemma genpar_SilE [elim!]:
  assumes "Sil R = genpar \<M> P E Q"
  "\<And> P'. \<lbrakk> P = Sil P'; R = genpar \<M> P' E Q \<rbrakk> \<Longrightarrow> S"
  "\<And> Q'. \<lbrakk> stable P; Q = Sil Q'; R = genpar \<M> P E Q' \<rbrakk> \<Longrightarrow> S"
  shows S
  by (metis (full_types) assms(1) assms(2) assms(3) genpar_Sil_iff)

lemma genpar_Sil_shift [simp]: "genpar \<M> P E (Sil Q) = genpar \<M> (Sil P) E Q"
  by (coinduction arbitrary: P Q rule: itree_strong_coind, auto elim!: stableE, metis)

lemma genpar_Sils_left [simp]: "genpar \<M> (Sils n P) E Q = Sils n (genpar \<M> P E Q)"
  by (induct n, simp_all)

lemma genpar_Sils_right [simp]: "genpar \<M> P E (Sils n Q) = Sils n (genpar \<M> P E Q)"
  by (induct n, simp_all)

lemma genpar_Ret_Ret [simp]:
  "genpar \<M> (Ret x) E (Ret y) = Ret (x, y)"
  by (simp add: genpar.code)

definition "pmerge_Vis \<M> F A G \<equiv> 
  map_pfun 
    (\<lambda>x. case x of 
           Left P' \<Rightarrow> genpar \<M> P' A (Vis G) \<comment> \<open> Left side acts independently \<close>
         | Right Q' \<Rightarrow> genpar \<M> (Vis F) A Q' \<comment> \<open> Right side acts independently \<close> 
         | Both (P', Q') \<Rightarrow> genpar \<M> P' A Q') \<comment> \<open> Both sides synchronise \<close>
    (\<M> F A G)"

lemma pdom_pmerge_Vis [simp]: "pdom (pmerge_Vis \<M> F A G) = pdom (\<M> F A G)"
  by (simp add: pmerge_Vis_def)

lemma genpar_Vis_Vis [simp]:
  "genpar \<M> (Vis F) E (Vis G) = Vis (pmerge_Vis \<M> F E G)"
  by (auto simp add: genpar.code pmerge_Vis_def)

lemma genpar_Ret_Vis [simp]:
  "genpar \<M> (Ret v) A (Vis G) = Vis (map_pfun (\<lambda> P. (genpar \<M> (Ret v) A P)) (A \<Zndres> G))"
  by (subst genpar.code, simp)

lemma genpar_Vis_Ret [simp]:
  "genpar \<M> (Vis F) A (Ret v) = Vis (map_pfun (\<lambda> P. (genpar \<M> P A (Ret v))) (A \<Zndres> F))"
  by (subst genpar.code, simp)

lemma genpar_Vis_iff: 
  "Vis H = genpar \<M> P E Q \<longleftrightarrow> ((\<exists> F G. P = Vis F \<and> Q = Vis G \<and> H = pmerge_Vis \<M> F E G) 
                         \<or> (\<exists> x G. P = Ret x \<and> Q = Vis G \<and> H = map_pfun (\<lambda> P. (genpar \<M> (Ret x) E P)) (E \<Zndres> G))
                         \<or> (\<exists> x F. P = Vis F \<and> Q = Ret x \<and> H = map_pfun (\<lambda> P. (genpar \<M> P E (Ret x))) (E \<Zndres> F)))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume a: "?lhs"
  hence "is_Vis (genpar \<M> P E Q)"
    by (metis itree.disc(9))
  thus ?rhs
    apply (auto elim!: is_RetE is_VisE)
    using a apply (simp_all)
    done
next
  show "?rhs \<Longrightarrow> ?lhs" by (auto)
qed

lemma genpar_VisE [elim!]:
  assumes "Vis H = genpar \<M> P E Q"
  "\<And> F G. \<lbrakk> P = Vis F; Q = Vis G; H = pmerge_Vis \<M> F E G \<rbrakk> \<Longrightarrow> R"
  "\<And> x G. \<lbrakk> P = Ret x; Q = Vis G; H = map_pfun (\<lambda> P. (genpar \<M> (Ret x) E P)) (E \<Zndres> G) \<rbrakk> \<Longrightarrow> R"
  "\<And> x F. \<lbrakk> P = Vis F; Q = Ret x; H = map_pfun (\<lambda> P. (genpar \<M> P E (Ret x))) (E \<Zndres> F) \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms by (auto simp add: genpar_Vis_iff)

lemma genpar_diverge: "genpar \<M> diverge E P = diverge"
proof (coinduction arbitrary: P rule: itree_coind)
case wform
then show ?case by (auto)
next
  case Ret
  then show ?case
    by (metis diverge_not_Ret) 
next
  case Sil
  then show ?case 
    by (auto, metis diverge.sel itree.sel(2))+
next
  case Vis
  then show ?case
    by (metis diverge_not_Vis) 
qed

end