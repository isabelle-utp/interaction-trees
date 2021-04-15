section \<open> CSP Operators \<close>

theory ITree_CSP
  imports ITree_Deadlock "Optics.Optics"
begin

subsection \<open> Basic Constructs \<close>

definition skip :: "('e, unit) itree" where
"skip = Ret ()"

definition inp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 'a) itree" where
"inp c = Vis (pfun_of_map (\<lambda> e. match\<^bsub>c\<^esub> e \<bind> Some \<circ> Ret))"

definition inp_in :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a list \<Rightarrow> ('e, 'a) itree" where
"inp_in c B = Vis (pfun_of_alist [(build\<^bsub>c\<^esub> v, Ret v). v \<leftarrow> B])"

definition outp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a \<Rightarrow> ('e, unit) itree" where
"outp c v = Vis (pfun_of_alist [(build\<^bsub>c\<^esub> v, Ret())])"

definition guard :: "bool \<Rightarrow> ('e, unit) itree" where
"guard b = (if b then Ret () else deadlock)"

subsection \<open> Iteration \<close>

text \<open> For now we support only basic iteration for CSP processes. \<close>

corec while :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) ktree \<Rightarrow> ('e, 's) ktree" where
"while b P s = (if (b s) then Sil (P s \<bind> while b P) else Ret s)"

abbreviation "loop \<equiv> while (\<lambda> s. True)"

subsection \<open> External Choice \<close>

definition map_prod :: "('a \<Zpfun> 'b) \<Rightarrow> ('a \<Zpfun> 'b) \<Rightarrow> ('a \<Zpfun> 'b)" (infixl "\<odot>" 100) where
"map_prod f g = (pdom(g) \<Zndres> f) + (pdom(f) \<Zndres> g)"

lemma map_prod_commute: "x \<odot> y = y \<odot> x"
  apply (auto simp add: fun_eq_iff map_prod_def option.case_eq_if)
  apply (metis Compl_iff IntD1 IntD2 pdom_pdom_res pfun_plus_commute_weak)
  done

lemma map_prod_empty [simp]: "x \<odot> {}\<^sub>p = x" "{}\<^sub>p \<odot> x = x"
  by (simp_all add: map_prod_def)

lemma map_prod_merge: 
  "f(x \<mapsto> v)\<^sub>p \<odot> g = 
  (if (x \<notin> pdom(g)) then (f \<odot> g)(x \<mapsto> v)\<^sub>p else {x} \<Zndres> (f \<odot> g))"
  by (auto simp add: map_prod_def)
     (metis (no_types, hide_lams) Compl_Un insert_absorb insert_is_Un)

text \<open> This is like race-free behaviour \<close>

class extchoice = 
  fixes extchoice :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<box>" 59)

text \<open> This is an completion of Hoare's bar operator. \<close>

instantiation itree :: (type, type) extchoice 
begin

text \<open> cf. RAISE language "interlock" operator -- basic operators of CCS vs. CSP operators. Can
  this be expressed in terms of operators? \<close>

primcorec extchoice_itree :: "('e, 'a) itree \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'a) itree"  where
"extchoice_itree P Q =
   (case (P, Q) of 
      (Vis F, Vis G) \<Rightarrow> Vis (F \<odot> G) |
      (Sil P', _) \<Rightarrow> Sil (extchoice_itree P' Q) | \<comment> \<open> Maximal progress \<close>
      (_, Sil Q') \<Rightarrow> Sil (extchoice_itree P Q') |
      \<comment> \<open> cf. Butterfield's external choice miraculous issue and a quantum-like computation with reconciliation \<close>
      (Ret x, Ret y) \<Rightarrow> if (x = y) then Ret x else Vis {}\<^sub>p |
      (Ret v, Vis _) \<Rightarrow> Ret v | \<comment> \<open> Is this like sliding choice? \<close>
      (Vis _, Ret v) \<Rightarrow> Ret v
   )"

instance ..

end

lemma choice_diverge: "diverge \<box> P = diverge"
  by (coinduction arbitrary: P, auto, metis diverge.code itree.simps(11))

lemma is_Sil_choice: "is_Sil (P \<box> Q) = (is_Sil P \<or> is_Sil Q)"
  using itree.exhaust_disc by (auto)

lemma choice_Vis_iff: 
  "P \<box> Q = Vis H \<longleftrightarrow> ((\<exists> F G. P = Vis F \<and> Q = Vis G \<and> H = (F \<odot> G)) \<or> (\<exists> x y. P = Ret x \<and> Q = Ret y \<and> x \<noteq> y \<and> H = {}\<^sub>p))"
  (is "?lhs = ?rhs")
proof
  assume a: ?lhs
  hence is_Vis: "is_Vis (P \<box> Q)"
    by simp
  thus ?rhs
    apply (auto elim!: is_RetE is_VisE)
    using a
     apply (simp_all add: a extchoice_itree.code)
    done
next
  assume ?rhs
  thus ?lhs
    by (auto simp add: extchoice_itree.code)
qed

lemma choice_VisE [elim!]:
  assumes "Vis H = P \<box> Q"
  "\<And> F G. \<lbrakk> P = Vis F; Q = Vis G; H = (F \<odot> G) \<rbrakk> \<Longrightarrow> R"
  "\<And> x y. \<lbrakk> P = Ret x; Q = Ret y; x \<noteq> y; H = {}\<^sub>p \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms(1) assms(2) assms(3) choice_Vis_iff)
  

lemma choice_Sils: "(Sils m P) \<box> Q = Sils m (P \<box> Q)"
  by (induct m, simp_all add: extchoice_itree.code)

lemma choice_Sil_stable: "stable P \<Longrightarrow> P \<box> (Sil Q) = Sil (P \<box> Q)"
  by (cases P, simp_all add: extchoice_itree.code)

lemma choice_Sils_stable: "stable P \<Longrightarrow> P \<box> (Sils m Q) = Sils m (P \<box> Q)"
  by (induct m, simp_all add: choice_Sil_stable)

lemma choice_Sils': "P \<box> (Sils m Q) = Sils m (P \<box> Q)"
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

text \<open> External Choice test cases \<close>

lemma "X \<noteq> Y \<Longrightarrow> (Vis {X \<mapsto> Ret a}\<^sub>p) \<box> (Vis {Y \<mapsto> Ret b}\<^sub>p) = 
       Vis {X \<mapsto> Ret a, Y \<mapsto> Ret b}\<^sub>p"
  by (auto simp add: extchoice_itree.code map_prod_merge pfun_upd_comm)

lemma "(Vis {X \<mapsto> Ret a}\<^sub>p) \<box> (Vis {X \<mapsto> Ret b}\<^sub>p) = 
       deadlock"
  by (simp add: extchoice_itree.code deadlock_def map_prod_merge)

lemma "X \<noteq> Y \<Longrightarrow> (Sil (Vis {X \<mapsto> Ret a}\<^sub>p)) \<box> (Sil (Vis {Y \<mapsto> Ret b}\<^sub>p)) = 
       Sil (Sil (Vis {X \<mapsto> Ret a, Y \<mapsto> Ret b}\<^sub>p))"
  by (simp add: extchoice_itree.code map_prod_merge pfun_upd_comm)

text \<open> This requires weak bisimulation \<close>

lemma "\<And> P. (X = (P :: ('e, 's) itree) \<box> P \<and> Y = P) \<or> (X = Y) \<Longrightarrow> X = Y"
  apply (coinduction arbitrary: X Y)
  apply (auto simp add: itree.case_eq_if itree.distinct_disc(1))
  oops

lemma choice_deadlock [simp]: "deadlock \<box> P = P"
proof (coinduction arbitrary: P rule: itree_strong_coind)
  case wform
then show ?case
  by (simp add: deadlock_def) 
next
  case (Ret x y)
  then show ?case
    by (metis (no_types, lifting) extchoice_itree.simps(4) deadlock_def is_Vis_def itree.disc(1) itree.sel(1) itree.simps(12) prod.sel(1) snd_conv) 
next
  case (Sil P' Q' P)
  then show ?case
    by (smt extchoice_itree.simps(5) deadlock_def fst_conv itree.case_eq_if itree.disc(6) itree.disc(9) itree.discI(2) itree.sel(2) itree.simps(11) snd_conv)
next
  case Vis
  then show ?case
    by (metis extchoice_itree.simps(6) deadlock_def itree.disc(9) itree.sel(3) itree.simps(12) map_prod_empty(2) prod.sel(1) snd_conv) 
qed

lemma choice_deadlock' [simp]: "P \<box> deadlock = P"
proof (coinduction arbitrary: P rule: itree_strong_coind)
  case wform
  then show ?case
  by (simp add: deadlock_def) 
next
  case Ret
  then show ?case
    by (metis (no_types, lifting) extchoice_itree.simps(4) deadlock_def itree.case_eq_if itree.disc(1) itree.disc(9) itree.sel(1) prod.sel(1) snd_conv stable_deadlock) 
next
  case Sil
  then show ?case
    by (metis extchoice_itree.sel(2) itree.disc(5) itree.sel(2) itree.simps(11) prod.sel(1))
next
  case Vis
  then show ?case
    by (metis extchoice_itree.simps(6) deadlock_def itree.disc(9) itree.sel(3) itree.simps(12) map_prod_empty(1) prod.sel(1) snd_conv)
qed

lemma choice_Sil': "P \<box> (Sil Q) = (Sil P) \<box> Q"
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
    by (metis (no_types, lifting) extchoice_itree.sel(2) choice_Sil_stable itree.collapse(2) itree.disc(5) itree.sel(2) itree.simps(11) prod.sel(1))    
next
  case Vis
  then show ?case
    by (metis is_Sil_choice itree.disc(5) itree.disc(6)) 
qed

lemma choice_unstable: "unstable P \<Longrightarrow> P \<box> Q = Sil ((un_Sil P) \<box> Q)"
  by (metis (no_types, lifting) extchoice_itree.ctr(2) itree.collapse(2) itree.simps(11) prod.sel(1))

lemma choice_unstable': "unstable Q \<Longrightarrow> P \<box> Q = Sil (P \<box> (un_Sil Q))"
  by (metis choice_Sil' choice_Sil_stable choice_unstable itree.collapse(2))

lemma choice_commutative:
  fixes P Q :: "('e, 's) itree"
  shows "P \<box> Q = Q \<box> P"
proof (coinduction arbitrary: P Q rule: itree_coind)
  case wform
  then show ?case
    by (metis extchoice_itree.disc_iff(1) extchoice_itree.simps(3) is_Sil_choice prod.sel(1) snd_conv)
next
  case Ret
  then show ?case
    by (smt extchoice_itree.disc_iff(1) extchoice_itree.simps(3) extchoice_itree.simps(4) itree.case_eq_if itree.disc(7) itree.sel(1) prod.sel(1) snd_conv un_Ret_def)
next
  case (Sil P Q P' Q')
  then show ?case
  proof (cases "unstable P'")
    case True
    with Sil have "P = (un_Sil P') \<box> Q'" "Q = Q' \<box> (un_Sil P')"
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
    apply (smt extchoice_itree.simps(3) extchoice_itree.simps(6) itree.case_eq_if itree.disc(9) itree.sel(3) map_prod_commute prod.sel(1) snd_conv)
     apply (smt extchoice_itree.simps(3) extchoice_itree.simps(6) itree.case_eq_if itree.disc(9) itree.sel(3) map_prod_commute prod.sel(1) snd_conv)
    apply (metis choice_deadlock choice_deadlock' map_prod_commute)
    done
qed

lemma skip_stable_choice: 
  assumes "stable P"
  shows "skip \<box> P = skip"
  by (metis (mono_tags, lifting) assms extchoice_itree.ctr(1) itree.discI(1) itree.exhaust_disc old.unit.exhaust prod.sel(1) prod.sel(2) skip_def)

subsection \<open> Parallel Composition \<close>

text \<open> The following function combines two choice functions for parallel composition. \<close>

datatype (discs_sels) ('a, 'b) andor = Left 'a | Right 'b | Both "'a \<times> 'b"

definition emerge :: "('a \<Zpfun> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<Zpfun> 'c) \<Rightarrow> ('a \<Zpfun> ('b, 'c) andor)" where
"emerge f A g = 
  map_pfun Both (A \<Zdres> pfuse f g) + map_pfun Left ((A \<union> pdom(g)) \<Zndres> f) + map_pfun Right ((A \<union> pdom(f)) \<Zndres> g)"

lemma pdom_pfuse [simp]: "pdom (pfuse f g) = pdom(f) \<inter> pdom(g)"
  by (metis (no_types, lifting) pdom_pfun_entries pfuse_def)

lemma pdom_emerge_commute: "pdom (emerge f A g) = pdom (emerge g A f)"
  by (auto simp add: emerge_def)

text \<open> Remove merge function; it can be done otherwise. \<close>

primcorec par :: "('e, 'a) itree \<Rightarrow> 'e set \<Rightarrow> ('e, 'b) itree \<Rightarrow> ('e, 'a \<times> 'b) itree" where
"par P A Q =
   (case (P, Q) of 
      \<comment> \<open> Silent events happen independently and have priority \<close>
      (Sil P', _) \<Rightarrow> Sil (par P' A Q) |
      (_, Sil Q') \<Rightarrow> Sil (par P A Q') |
      \<comment> \<open> Visible events are subject to synchronisation constraints \<close>
      (Vis F, Vis G) \<Rightarrow>
        Vis (map_pfun 
              (\<lambda>x. case x of 
                     Left P' \<Rightarrow> par P' A Q \<comment> \<open> Left side acts independently \<close>
                   | Right Q' \<Rightarrow> par P A Q' \<comment> \<open> Right side acts independently \<close> 
                   | Both (P', Q') \<Rightarrow> par P' A Q') \<comment> \<open> Both sides synchronise \<close>
              (emerge F A G)) |
      \<comment> \<open> If both sides terminate, then they must agree on the returned value. This could be
           generalised using a merge function. \<close>
      (Ret x, Ret y) \<Rightarrow> Ret (x, y) |
      \<comment> \<open> A termination occurring on one side is pushed forward. Only events not requiring
           synchronisation can occur on the other side. \<close>
      (Ret v, Vis G)   \<Rightarrow> Vis (map_pfun (\<lambda> P. (par (Ret v) A P)) (A \<Zndres> G)) |
      (Vis F, Ret v)   \<Rightarrow> Vis (map_pfun (\<lambda> P. (par P A (Ret v))) (A \<Zndres> F))
   )" 

lemma par_Sil_left [simp]:
  "par (Sil P') E Q = Sil (par P' E Q)"
  by (simp add: par.code)

lemma stableE [elim!]:
  assumes "stable P" "is_Ret P \<Longrightarrow> Q" "is_Vis P \<Longrightarrow> Q"
  shows Q
  by (metis assms(1) assms(2) assms(3) itree.exhaust_disc)

lemma par_Sil_stable_right:
  "stable P \<Longrightarrow> par P E (Sil Q') = Sil (par P E Q')"
  by (auto simp add: par.code)

lemma unstable_par [simp]: "unstable (par P E Q) = (unstable P \<or> unstable Q)"
  by auto

lemma par_Ret_iff: "Ret x = par P E Q \<longleftrightarrow> (\<exists> a b. P = Ret a \<and> Q = Ret b \<and> x = (a, b))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume a:?lhs
  hence "is_Ret (par P E Q)"
    by (metis itree.disc(1))
  then obtain a b where "P = Ret a" "Q = Ret b"
    by force
  with a show ?rhs
    by (simp add: par.code)
next
  show "?rhs \<Longrightarrow> ?lhs"
    by (auto simp add: par.code)
qed

lemma par_Sil_iff: "Sil R = par P E Q \<longleftrightarrow> ((\<exists> P'. P = Sil P' \<and> R = par P' E Q) \<or> (\<exists> Q'. stable P \<and> Q = Sil Q' \<and> R = par P E Q'))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume a:?lhs
  hence sil: "is_Sil (par P E Q)"
    by (metis (no_types, hide_lams) itree.disc(5))
  show ?rhs
  proof (cases "unstable P")
    case True
    with a show ?thesis
      by (auto elim!: unstableE simp add: par.code)
  next
    case False
    hence "unstable Q"
      by (metis sil unstable_par)
    with a False show ?thesis by (auto simp add: par_Sil_stable_right elim!: unstableE)
  qed
next
  show "?rhs \<Longrightarrow> ?lhs"
    by (auto simp add: par_Sil_stable_right)
qed
  
lemma par_SilE [elim!]:
  assumes "Sil R = par P E Q"
  "\<And> P'. \<lbrakk> P = Sil P'; R = par P' E Q \<rbrakk> \<Longrightarrow> S"
  "\<And> Q'. \<lbrakk> stable P; Q = Sil Q'; R = par P E Q' \<rbrakk> \<Longrightarrow> S"
  shows S
  by (metis (full_types) assms(1) assms(2) assms(3) par_Sil_iff)

lemma par_Sil_shift [simp]: "par P E (Sil Q) = par (Sil P) E Q"
  by (coinduction arbitrary: P Q rule: itree_strong_coind, auto, metis)

lemma par_Sils_left [simp]: "par (Sils n P) E Q = Sils n (par P E Q)"
  by (induct n, simp_all)

lemma par_Sils_right [simp]: "par P E (Sils n Q) = Sils n (par P E Q)"
  by (induct n, simp_all)

lemma par_Ret_Ret [simp]:
  "par (Ret x) E (Ret y) = Ret (x, y)"
  by (simp add: par.code)

definition "merge_Vis F A G \<equiv> 
  map_pfun 
    (\<lambda>x. case x of 
           Left P' \<Rightarrow> par P' A (Vis G) \<comment> \<open> Left side acts independently \<close>
         | Right Q' \<Rightarrow> par (Vis F) A Q' \<comment> \<open> Right side acts independently \<close> 
         | Both (P', Q') \<Rightarrow> par P' A Q') \<comment> \<open> Both sides synchronise \<close>
    (emerge F A G)"

lemma pfun_app_add' [simp]: "\<lbrakk> e \<in> pdom f; e \<notin> pdom g \<rbrakk> \<Longrightarrow> (f + g)(e)\<^sub>p = f(e)\<^sub>p"
  by (metis (no_types, lifting) pfun_app_upd_1 pfun_upd_add_left pfun_upd_ext)
  
lemma pfuse_app [simp]:
  "\<lbrakk> e \<in> pdom F; e \<in> pdom G \<rbrakk> \<Longrightarrow> (pfuse F G)(e)\<^sub>p = (F(e)\<^sub>p, G(e)\<^sub>p)"
  by (metis (no_types, lifting) IntI pfun_entries_apply_1 pfuse_def)

lemma merge_Vis_both [simp]: "\<lbrakk> e \<in> E; e \<in> pdom F; e \<in> pdom G \<rbrakk> \<Longrightarrow> merge_Vis F E G(e)\<^sub>p = par (F(e)\<^sub>p) E (G(e)\<^sub>p)"
  by (simp add: merge_Vis_def emerge_def)

lemma merge_Vis_left [simp]: "\<lbrakk> e \<notin> E; e \<in> pdom F; e \<notin> pdom G \<rbrakk> \<Longrightarrow> merge_Vis F E G(e)\<^sub>p = par (F(e)\<^sub>p) E (Vis G)"
  by (simp add: merge_Vis_def emerge_def)

lemma merge_Vis_right [simp]: "\<lbrakk> e \<notin> E; e \<notin> pdom F; e \<in> pdom G \<rbrakk> \<Longrightarrow> merge_Vis F E G(e)\<^sub>p = par (Vis F) E (G(e)\<^sub>p)"
  by (simp add: merge_Vis_def emerge_def)

lemma pdom_merge_Vis [simp]: "pdom (merge_Vis F A G) = pdom (emerge F A G)"
  by (simp add: merge_Vis_def)

lemma par_Vis_Vis [simp]:
  "par (Vis F) E (Vis G) = Vis (merge_Vis F E G)"
  by (auto simp add: par.code merge_Vis_def)

lemma par_Ret_Vis [simp]:
  "par (Ret v) A (Vis G) = Vis (map_pfun (\<lambda> P. (par (Ret v) A P)) (A \<Zndres> G))"
  by (subst par.code, simp)

lemma par_Vis_Ret [simp]:
  "par (Vis F) A (Ret v) = Vis (map_pfun (\<lambda> P. (par P A (Ret v))) (A \<Zndres> F))"
  by (subst par.code, simp)

lemma par_Vis_iff: 
  "Vis H = par P E Q \<longleftrightarrow> ((\<exists> F G. P = Vis F \<and> Q = Vis G \<and> H = merge_Vis F E G) 
                         \<or> (\<exists> x G. P = Ret x \<and> Q = Vis G \<and> H = map_pfun (\<lambda> P. (par (Ret x) E P)) (E \<Zndres> G))
                         \<or> (\<exists> x F. P = Vis F \<and> Q = Ret x \<and> H = map_pfun (\<lambda> P. (par P E (Ret x))) (E \<Zndres> F)))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume a: "?lhs"
  hence "is_Vis (par P E Q)"
    by (metis itree.disc(9))
  thus ?rhs
    apply (auto elim!: is_RetE is_VisE)
    using a apply (simp_all)
    done
next
  show "?rhs \<Longrightarrow> ?lhs" by (auto)
qed

lemma par_VisE [elim!]:
  assumes "Vis H = par P E Q"
  "\<And> F G. \<lbrakk> P = Vis F; Q = Vis G; H = merge_Vis F E G \<rbrakk> \<Longrightarrow> R"
  "\<And> x G. \<lbrakk> P = Ret x; Q = Vis G; H = map_pfun (\<lambda> P. (par (Ret x) E P)) (E \<Zndres> G) \<rbrakk> \<Longrightarrow> R"
  "\<And> x F. \<lbrakk> P = Vis F; Q = Ret x; H = map_pfun (\<lambda> P. (par P E (Ret x))) (E \<Zndres> F) \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms by (auto simp add: par_Vis_iff)

lemma par_commute: "par P E Q = (par Q E P) \<bind> (\<lambda> (a, b). Ret (b, a))"
  apply (coinduction arbitrary: P Q rule: itree_strong_coind)
     apply (auto elim!: is_RetE unstableE bind_RetE' bind_SilE' simp add: par_Ret_iff)
  apply metis
  apply metis
  apply metis
  apply (metis pdom_emerge_commute)
     apply (metis pdom_emerge_commute)
    apply (simp add: emerge_def)
    apply (auto)
    apply (rename_tac e F G)
    apply (rule_tac x="F e" in exI)
    apply (rule_tac x="G e" in exI)
  apply (simp)
  apply (smt (verit, ccfv_threshold) map_pfun_apply merge_Vis_both pdom.rep_eq pdom_emerge_commute pdom_map_pfun pdom_merge_Vis pfun_app.rep_eq)
  apply (metis (no_types, lifting) map_pfun_apply merge_Vis_left merge_Vis_right pdom.rep_eq pdom_emerge_commute pdom_map_pfun pdom_merge_Vis pfun_app.rep_eq)
  apply (metis (no_types, lifting) map_pfun_apply merge_Vis_left merge_Vis_right pdom.rep_eq pdom_emerge_commute pdom_map_pfun pdom_merge_Vis pfun_app.rep_eq)
  done  

lemma par_diverge: "par diverge E P = diverge"
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

consts 
  interleave :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<interleave>" 55)
  gparallel :: "'a \<Rightarrow> 'e set \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<parallel>\<^bsub>_\<^esub> _" [55, 0, 56] 56)

definition "gpar_csp P cs Q \<equiv> par P cs Q \<bind> (\<lambda> (x, y). Ret ())"

abbreviation inter_csp :: "('e, unit) itree \<Rightarrow> ('e, unit) itree \<Rightarrow> ('e, unit) itree" where
"inter_csp P Q \<equiv> gpar_csp P {} Q"

adhoc_overloading gparallel gpar_csp and interleave inter_csp

lemma gpar_csp_commute: "P \<parallel>\<^bsub>E\<^esub> Q = Q \<parallel>\<^bsub>E\<^esub> P"
proof -
  have "P \<parallel>\<^bsub>E\<^esub> Q = (par P E Q \<bind> (\<lambda>(x, y). Ret ()))"
    by (simp add: gpar_csp_def)
  also have "... = (par Q E P \<bind> (\<lambda>(x, y). Ret (y, x))) \<bind> (\<lambda>(x, y). Ret ())"
    by (metis par_commute)
  also have "... = par Q E P \<bind> (\<lambda>(x, y). Ret ())"
    by (simp add: bind_itree_assoc[THEN sym])
       (metis (full_types) case_prod_beta' old.unit.exhaust)
  also have "... = Q \<parallel>\<^bsub>E\<^esub> P"
    by (simp add: gpar_csp_def)
  finally show ?thesis .
qed

lemma gpar_csp_diverge: "diverge \<parallel>\<^bsub>E\<^esub> P = diverge"
  by (metis bind_diverge gpar_csp_def par_diverge)

lemma interleave_commute:
  fixes P :: "('e, unit) itree"
  shows "P \<interleave> Q = Q \<interleave> P"
  by (simp add: gpar_csp_commute)

lemma skip_interleave: "skip \<interleave> P = P"
proof (coinduction arbitrary: P rule: itree_coind)
  case wform
  then show ?case by (auto simp add: gpar_csp_def skip_def)
next
  case Ret
  then show ?case
    by (auto simp add: gpar_csp_def skip_def)
next
  case Sil
  then show ?case 
    by (auto simp add: gpar_csp_def skip_def)
next
  case Vis
  then show ?case
    by (auto simp add: gpar_csp_def skip_def)
qed

subsection \<open> Hiding \<close>

text \<open> Could we prioritise events to keep determinism? \<close>

corec hide :: "('e, 'a) itree \<Rightarrow> 'e set \<Rightarrow> ('e, 'a) itree" where
"hide P A = 
  (case P of
    Vis F \<Rightarrow> 
      \<comment> \<open> If precisely one event in the hidden set is enabled, this becomes a silent event \<close>
      if (card (A \<inter> pdom(F)) = 1) then Sil (hide (F (the_elem (A \<inter> pdom(F)))) A)
      \<comment> \<open> If no event is in the hidden set, then the process continues as normal \<close>
      else if (A \<inter> pdom(F)) = {} then Vis (map_pfun (\<lambda> X. hide X A) F)
      \<comment> \<open> Otherwise, there are multiple hidden events present and we deadlock \<close>
      else deadlock |
    Sil P \<Rightarrow> Sil (hide P A) |
    Ret x \<Rightarrow> Ret x)"

lemma is_Ret_hide [simp]: "is_Ret (hide P E) = is_Ret P"
  by (simp add: hide.code deadlock_def itree.case_eq_if)

lemma is_Sil_hide [simp]: "is_Sil (hide P E) = (is_Sil P \<or> (is_Vis P \<and> card (E \<inter> pdom(un_Vis P)) = 1))"
  by (auto simp add: hide.code deadlock_def itree.case_eq_if)

lemma is_Vis_hide [simp]: "is_Vis (hide P E) = (is_Vis P \<and> (card (E \<inter> pdom(un_Vis P)) \<noteq> 1 \<or> E \<inter> pdom(un_Vis P) = {}))"
  by (auto simp add: hide.code itree.case_eq_if deadlock_def)

lemma hide_empty: "hide P {} = P"
  apply (coinduction arbitrary: P rule: itree_coind)
     apply (auto)
      apply (simp add: hide.code)
     apply (simp add: hide.code)
    apply (simp add: hide.code)
   apply (simp add: hide.code)
  apply (simp add: hide.code)
  apply (auto simp add: itree.case_eq_if)
  apply (metis (no_types, lifting) hide.code itree.case_eq_if)
  oops

end