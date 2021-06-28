section \<open> Biased Operators for CSP \<close>

theory ITree_CSP_Biased
  imports ITree_CSP
begin

subsection \<open> Biased External Choice \<close>

text \<open> Almost identical to external choice, except we resolve non-determinism by biasing the left or right branch. \<close>

definition bextchoicel :: "('e, 'a) itree \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'a) itree" (infixl "\<^sub><\<box>" 59) where
"bextchoicel = genchoice (\<lambda> F G. G + F)"

definition bextchoicer :: "('e, 'a) itree \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'a) itree" (infixl "\<box>\<^sub>>" 59) where
"bextchoicer = genchoice (+)"

lemma extchoice_eq_bextchoice_iff:
  assumes "\<^bold>I(P) \<inter> \<^bold>I(Q) = {}" 
  shows "P \<^sub><\<box> Q = P \<box> Q"
proof (cases P rule: itree_cases)
  case (Vis m F)
  note Vis' = this
  show ?thesis 
  proof (cases Q rule: itree_cases)
    case (Vis n G)
    with Vis' assms show ?thesis
      by (simp add: extchoice_itree_def bextchoicel_def genchoice_Sils genchoice_Sils')
         (metis empty_iff map_prod_as_ovrd pfun_plus_commute_weak)
  next
    case (Ret n x)
    with assms Vis' show ?thesis 
      by (simp add: extchoice_itree_def bextchoicel_def genchoice_Sils genchoice_Sils' genchoice.ctr(1))
  next
    case diverge
    then show ?thesis
      by (metis Sil_cycle_diverge bextchoicel_def diverge.disc_iff diverge.sel extchoice_itree_def genchoice_unstable' is_Sil_genchoice itree.sel(2)) 
  qed
next
  case (Ret m x)
  note Ret' = this
  then show ?thesis
  proof (cases Q rule: itree_cases)
    case (Vis n F)
    with assms Ret' show ?thesis
      by (simp add: extchoice_itree_def bextchoicel_def genchoice_Sils genchoice_Sils' genchoice.ctr(1))
  next
    case (Ret n y)
    show ?thesis
    proof (cases "x = y")
      case True
      with assms Ret Ret' show ?thesis 
        by (simp add: extchoice_itree_def bextchoicel_def genchoice_Sils genchoice_Sils' genchoice.ctr(1))
    next
      case False
      with assms Ret Ret' show ?thesis
        by (simp add: extchoice_itree_def bextchoicel_def genchoice_Sils genchoice_Sils')
           (metis genchoice_Vis_iff)
    qed
  next
    case diverge
    then show ?thesis
      by (metis Sil_cycle_diverge bextchoicel_def diverge.sel extchoice_itree_def genchoice_unstable' is_Sil_genchoice itree.sel(2) unstable_diverge) 
  qed
next
  case diverge
  then show ?thesis
    by (simp add: bextchoicel_def choice_diverge genchoice_diverge) 
qed

subsection \<open> Biased Parallel Composition\<close>

text \<open> The biased merge function is almost the same as @{const emerge}, except that it does not
  remove events from the left hand process, thus allowing them to taking precedence. \<close>

definition bemerge :: "('a \<Zpfun> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<Zpfun> 'c) \<Rightarrow> ('a \<Zpfun> ('b, 'c) andor)" where
"bemerge f A g = 
  map_pfun Both (A \<Zdres> pfuse f g) + map_pfun Left f + map_pfun Right ((A \<union> pdom(f)) \<Zndres> g)"

abbreviation "bparl \<equiv> genpar bemerge"

definition bgpar_csp ("_ \<^sub><\<parallel>\<^bsub>_\<^esub> _" [55, 0, 56] 56) where
"bgpar_csp P cs Q \<equiv> bparl P cs Q \<bind> (\<lambda> (x, y). Ret ())"

abbreviation inter_csp :: "('e, unit) itree \<Rightarrow> ('e, unit) itree \<Rightarrow> ('e, unit) itree" (infixl "\<^sub><\<interleave>" 55) where
"inter_csp P Q \<equiv> gpar_csp P {} Q"

end