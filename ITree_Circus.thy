theory ITree_Circus
  imports "Interaction_Trees" "Optics.Optics" "Shallow-Expressions.Shallow_Expressions"
begin

primcorec diverge :: "('e, 'r) itree" where
"diverge = Sil diverge"

definition Skip :: "('e, 'r) ktree" where
"Skip = (\<lambda> s. Ret s)"

abbreviation Div :: "('e, 'r) ktree" where
"Div \<equiv> (\<lambda> s. diverge)"

text \<open> Deadlock is an interaction with no visible event \<close>

definition deadlock :: "('e, 'r) itree" where
"deadlock = Vis [\<mapsto>]"

abbreviation 
"Stop \<equiv> (\<lambda> s. deadlock)"

corec test :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) ktree" where
"test b = (\<lambda> s. if (b s) then Ret s else deadlock)"

lemma "test (\<lambda> s. False) = Stop"
  by (simp add: test.code)

term "[x \<leadsto> $x + 1, y \<leadsto> True]"

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

lemma bind_diverge: "diverge \<bind> F = diverge"
  by (coinduction, auto simp add: itree.case_eq_if)

definition inp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 'a) itree" where
"inp c = Vis (\<lambda> e. match\<^bsub>c\<^esub> e \<bind> Some \<circ> Ret)"

definition input :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 's) ktree) \<Rightarrow> ('e, 's) ktree" where
"input c P = (\<lambda> s. inp c \<bind> (\<lambda> x. P x s))"

syntax "_input" :: "id \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic" ("_?'(_') \<rightarrow> _" [90, 0, 91] 91)
translations "c?(x) \<rightarrow> P" == "CONST input c (\<lambda> x. P)"

primcorec outp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a \<Rightarrow> ('e, unit) itree" where
"outp c v = Vis (\<lambda> e. case match\<^bsub>c\<^esub> e of 
                      Some x \<Rightarrow> if (v = x) then Some (Ret ()) else None | 
                      _ \<Rightarrow> None)"

definition "output" :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a \<Rightarrow> ('e, 's) ktree \<Rightarrow> ('e, 's) ktree" where
"output c e P = (\<lambda> s. outp c e \<then> Ret s)"

syntax "_output" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_!'(_') \<rightarrow> _" [90, 0, 91] 91)
translations "c!(e) \<rightarrow> P" == "CONST output c e P"

definition map_prod :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" (infixl "\<odot>" 100) where
"map_prod f g = (\<lambda>x. case g x of 
                      None \<Rightarrow> f x | 
                      Some y \<Rightarrow> 
                        (case f x of 
                          None \<Rightarrow> g x |
                          Some z \<Rightarrow> None))"

lemma map_prod_commute: "x \<odot> y = y \<odot> x"
  by (auto simp add: fun_eq_iff map_prod_def option.case_eq_if)

lemma map_prod_empty [simp]: "x \<odot> [\<mapsto>] = x" "[\<mapsto>] \<odot> x = x"
   by (force simp add: fun_eq_iff map_prod_def option.case_eq_if)+

lemma map_prod_merge: 
  "f(x \<mapsto> v) \<odot> g = 
  (if (g x = None) then (f \<odot> g)(x \<mapsto> v) else (f \<odot> g) |` (-{x}))"
  by (auto simp add: map_prod_def fun_eq_iff option.case_eq_if)

definition seq :: "('e, 's) ktree \<Rightarrow> ('e, 's) ktree \<Rightarrow> ('e, 's) ktree" where
"seq P Q = (\<lambda> s. P s \<bind> Q)"

text \<open> This is like race-free behaviour \<close>

primcorec choice :: "('e, 'a) itree \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'a) itree" where
"choice P Q =
   (case (P, Q) of 
      (Vis F, Vis G) \<Rightarrow> Vis (F \<odot> G) |
      (Sil P', _) \<Rightarrow> Sil (choice P' Q) |
      (_, Sil Q') \<Rightarrow> Sil (choice P Q') |
      (Ret x, Ret y) \<Rightarrow> if (x = y) then Ret x else Vis [\<mapsto>] | 
      (Ret v, Vis _)   \<Rightarrow> Ret v | \<comment> \<open> Needs more thought \<close>
      (Vis _, Ret v)   \<Rightarrow> Ret v
   )"

text \<open> External Choice test cases \<close>

lemma "X \<noteq> Y \<Longrightarrow> choice (Vis [X \<mapsto> Ret a]) (Vis [Y \<mapsto> Ret b]) = 
       Vis [X \<mapsto> Ret a, Y \<mapsto> Ret b]"
  by (auto simp add: choice.code map_prod_merge)

lemma "choice (Vis [X \<mapsto> Ret a]) (Vis [X \<mapsto> Ret b]) = 
       deadlock"
  by (simp add: choice.code deadlock_def map_prod_merge)

lemma "X \<noteq> Y \<Longrightarrow> choice (Sil (Vis [X \<mapsto> Ret a])) (Sil (Vis [Y \<mapsto> Ret b])) = 
       Sil (Sil (Vis [X \<mapsto> Ret a, Y \<mapsto> Ret b]))"
  by (simp add: choice.code map_prod_merge fun_upd_twist)

text \<open> This requires weak bisimulation \<close>

lemma "\<And> P. (X = choice P P \<and> Y = P) \<or> (X = Y) \<Longrightarrow> X = Y"
  apply (coinduction arbitrary: X Y)
  apply (auto simp add: itree.case_eq_if itree.distinct_disc(1))
  oops

fun Sils :: "nat \<Rightarrow> ('e, 's) itree \<Rightarrow> ('e, 's) itree" where
"Sils 0 P = P" |
"Sils (Suc n) P = Sil (Sils n P)"

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

(*
lemma [elim!]: "\<lbrakk> is_Ret (Sils n P); \<lbrakk> n = 0; is_Ret P \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  using is_Ret_Sils by force
  

lemma [elim!]: "\<lbrakk> is_Vis (Sils n P); \<lbrakk> n = 0; is_Vis P \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (metis Sils.elims itree.disc(8))

lemma [elim!]: "\<lbrakk> is_Ret (Sils (m + n) P); \<lbrakk> m = 0; n = 0; is_Ret P \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (metis Sils.simps(1) is_Ret_Sils zero_eq_add_iff_both_eq_0)
  

lemma is_VisE2 [elim!]: "\<lbrakk> is_Vis (Sils (m + n) P); \<lbrakk> m = 0; n = 0; is_Vis P \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (metis Sils.elims itree.disc(8) zero_eq_add_iff_both_eq_0)
*)  

text \<open> A stable process has no possible internal activity \<close>

abbreviation "unstable P \<equiv> is_Sil P"
abbreviation "stable P \<equiv> \<not> unstable P"

translations "CONST stable P" <= "\<not> CONST unstable P"

lemma "unstable diverge"
  by simp

text \<open> A process stabilises if it stabilises within a finite number of internal events \<close>

definition "stabilises P = (\<exists> n P'. (Sils n P' = P \<and> stable P'))"

abbreviation "diverges P \<equiv> (\<not> (stabilises P))"

translations "CONST diverges P" <= "\<not> (CONST stabilises P)"

lemma diverges_implies_unstable [intro]: "diverges P \<Longrightarrow> unstable P"
  by (metis Sils.simps(1) stabilises_def)

lemma Sils_injective: "Sils n P = Sils n Q \<Longrightarrow> P = Q"
  by (induct n, simp_all)

lemma Sils_diverge: "Sils n diverge = diverge"
  by (induct n, simp_all, metis diverge.code)

lemma diverges_diverge [simp]: "diverges diverge"
  by (auto simp add: stabilises_def Sils_diverge, metis Sils_diverge Sils_injective diverge.disc_iff)

text \<open> If $P$ is not divergent, then it must be prefixed by a finite sequence of taus. \<close>

lemma diverges_implies_equal: 
  assumes "diverges P" "diverges Q"
  shows "P = Q"
using assms proof (coinduction arbitrary: P Q rule: itree_coind)
  case (wform P Q)
  then show ?case
    by blast
next
  case (Ret x y)
  then show ?case
    by (meson diverges_implies_unstable itree.disc(4))
next
  case (Sil P' Q' P Q)
  then show ?case
    by (metis Sils.simps(2) stabilises_def)
next
  case (Vis F G P Q)
  then show ?case
    using diverges_implies_unstable itree.disc(6) by blast
qed

lemma Sil_cycle_diverge: "\<lbrakk> is_Sil P; un_Sil P = P \<rbrakk> \<Longrightarrow> P = diverge"
  by (coinduction arbitrary: P, auto)

lemma diverges_then_diverge: "diverges P \<longleftrightarrow> P = diverge"
  using diverges_diverge diverges_implies_equal by blast

lemma choice_diverge: "choice diverge P = diverge"
  by (coinduction arbitrary: P, auto, metis diverge.code itree.simps(11))

lemma choice_Sils: "choice (Sils m P) Q = Sils m (choice P Q)"
  by (induct m, simp_all add: choice.code)

lemma choice_Sil_stable: "stable P \<Longrightarrow> choice P (Sil Q) = Sil (choice P Q)"
  by (cases P, simp_all add: choice.code)

lemma choice_Sils_stable: "stable P \<Longrightarrow> choice P (Sils m Q) = Sils m (choice P Q)"
  by (induct m, simp_all add: choice_Sil_stable)

lemma choice_Sils': "choice P (Sils m Q) = Sils m (choice P Q)"
proof (cases "diverges P")
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

inductive trace_to :: "('e, 's) itree \<Rightarrow> 'e list \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" ("_ \<midarrow>_\<leadsto> _" [55, 0, 55] 55) where
trace_to_Nil [intro]: "P \<midarrow>[]\<leadsto> P" | 
trace_to_Sil [intro]: "P \<midarrow>tr\<leadsto> P' \<Longrightarrow> Sil P \<midarrow>tr\<leadsto> P'" |
trace_to_Vis [intro]: "\<lbrakk> e \<in> dom F; the (F e) \<midarrow>tr\<leadsto> P' \<rbrakk> \<Longrightarrow> Vis F \<midarrow>e # tr\<leadsto> P'"

inductive_cases
  trace_toE [elim]: "P \<midarrow>tr\<leadsto> P'"

abbreviation (input) "trace_of \<equiv> (\<lambda> (tr, P') P. P \<midarrow>tr\<leadsto> P')"

lemma trace_to_Sils [intro]: "P \<midarrow>tr\<leadsto> P' \<Longrightarrow> Sils n P \<midarrow>tr\<leadsto> P'"
  by (induct n, auto)

lemma trace_to_Ret: "Ret x \<midarrow>tr\<leadsto> P \<Longrightarrow> (tr, P) = ([], Ret x)"
  by (erule trace_toE, simp_all)

definition "traces P = {tr. \<exists> P'. P \<midarrow>tr\<leadsto> P'}"

lemma trace_of_divergent:
  assumes "P \<midarrow>t\<leadsto> P'" "diverges P"
  shows "(t, P') = ([], diverge)"
  using assms(1-2)
  apply (induct rule: trace_to.induct)
  apply (auto simp add: assms diverges_then_diverge)
  apply (metis diverge.code itree.inject(2))
  apply (metis diverge.code itree.inject(2))
  apply (metis diverge.code itree.simps(9))
  done

lemma traces_diverge: "traces diverge = {[]}"
  by (auto simp add: traces_def dest: trace_of_divergent)

lemma trace_of_deadlock: "deadlock \<midarrow>t\<leadsto> P \<Longrightarrow> (t, P) = ([], deadlock)"
  by (auto simp add: deadlock_def)

lemma traces_deadlock: "traces deadlock = {[]}"
  by (auto simp add: traces_def deadlock_def)

lemma traces_inp: "wb_prism e \<Longrightarrow> traces (inp e) = {[]} \<union> {[build\<^bsub>e\<^esub> x] | x. True}"
  apply (simp add: traces_def inp_def)
  apply (auto)
   apply (erule trace_toE)
     apply (simp)
    apply (erule trace_toE)
      apply (simp)
     apply (simp)
    apply (simp)
   apply (simp_all add: fun_eq_iff comp_def)
   apply (smt (verit, best) bind_eq_Some_conv comp_apply domIff itree.distinct(1) itree.distinct(3) option.collapse option.sel prod.inject trace_to.cases wb_prism.build_match)
  apply (metis (mono_tags, lifting) bind.bind_lunit domIff option.simps(3) trace_to.intros(3) trace_to_Nil wb_prism.match_build)
  done

text \<open> A failure is recorded when there is a trace leading to a stable interaction tree. At this
  point, the refusal is calculated. \<close>

definition failure_of :: "('e list \<times> 'e set) \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" where
"failure_of = (\<lambda> (tr, E) t. \<exists> t'. (trace_of (tr, t') t \<and> is_Vis t' \<and> E \<subseteq> (- dom (un_Vis t'))))"

definition failures :: "('e, 's) itree \<Rightarrow> ('e list \<times> 'e set) set" where
"failures P = {f. failure_of f P}"

lemma diverge_no_failures [dest]: "failure_of t diverge \<Longrightarrow> False"
  apply (simp add: failure_of_def prod.case_eq_if)
  apply (auto)
  apply (metis diverge.disc_iff diverges_diverge itree.distinct_disc(6) snd_conv trace_of_divergent)
  done

lemma deadlock_failure: "failure_of f deadlock \<Longrightarrow> \<exists> E. f = ([], E)"
  by (auto simp add: failure_of_def prod.case_eq_if, metis eq_fst_iff trace_of_deadlock)

lemma failures_deadlock: "failures deadlock = {([], E) | E. True}"
  apply (auto simp add: failures_def )
  apply (meson deadlock_failure prod.inject)
  apply (metis (mono_tags, lifting) compl_le_swap1 deadlock_def dom_empty empty_subsetI failure_of_def itree.disc(9) itree.sel(3) old.prod.case trace_to_Nil)
  done

text \<open> A (minimal) divergence trace is recorded when there is a trace that leads to a divergent state. \<close>

definition min_divergence_of :: "'e list \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" where
"min_divergence_of tr P = trace_of (tr, diverge) P"

lemma min_divergence_diverge [intro]: "min_divergence_of [] diverge"
  by (simp add: min_divergence_of_def trace_to_Nil)

definition "no_divergence P = (\<forall> tr. \<not> min_divergence_of tr P)" 

lemma divergence_diverge [simp]: "no_divergence diverge = False"
  by (auto simp add: no_divergence_def)

inductive stabilises_to :: "(('e, 's) itree \<Rightarrow> bool) \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" where
ret_stbs [intro]: "stabilises_to R (Ret x)" |
sil_stbs [intro]: "stabilises_to R P \<Longrightarrow> stabilises_to R (Sil P)" |
vis_stbs [intro]: "(\<And> t. t \<in> ran F \<Longrightarrow> R t) \<Longrightarrow> stabilises_to R (Vis F)"

lemma monotonic_stabilises_to: "stabilises_to R P \<Longrightarrow> R \<le> S \<Longrightarrow> stabilises_to S P"
  apply (induct rule: stabilises_to.induct)
  apply (simp_all add: ret_stbs sil_stbs vis_stbs)
  apply (simp add: predicate1D vis_stbs)
  done

lemma mono_stabilises_to [mono add]: "R \<le> S \<Longrightarrow> stabilises_to R \<le> stabilises_to S"
  using monotonic_stabilises_to by auto

lemma Sils_0 [intro]: "Sils 0 P = P"
  by (simp)

lemma stable_Ret [intro]: "stable (Ret x)"
  by simp

lemma stable_Vis [intro]: "stable (Vis F)"
  by simp

lemma stabilises_Ret [simp]: "stabilises (Ret x)"
  by (force simp add: stabilises_def)

lemma stabilises_Sil [intro, simp]: 
  "stabilises P \<Longrightarrow> stabilises (Sil P)"
  by (metis diverge.sel diverges_then_diverge itree.sel(2))

lemma stabilises_Vis [intro, simp]:
  "stabilises (Vis F)"
  by (meson diverges_implies_unstable stable_Vis)

lemma stabilises_to_stabilises [intro]: "stabilises_to R P \<Longrightarrow> stabilises P"
  by (induct rule: stabilises_to.induct, auto)

lemma stabilises_to_Sils_VisI [intro]: "ran F \<subseteq> Collect R \<Longrightarrow> stabilises_to R (Sils n (Vis F))"
  by (induct n, auto)

lemma stabilises_to_Sils_RetI [intro]: "stabilises_to R (Sils n (Ret x))"
  by (induct n, auto)

lemma stabilises_alt_def: 
  "stabilises_to R P = (\<exists> n P'. Sils n P' = P \<and> ((P' \<in> range Vis \<and> ran (un_Vis P') \<subseteq> Collect R) \<or> P' \<in> range Ret))"
  apply (auto)
   apply (induct rule: stabilises_to.induct)
  apply (auto)
  apply (meson Sils.simps(1) range_eqI)
  apply (metis Sils.simps(2) itree.sel(3) rangeI)
  apply (meson Sils.simps(2) rangeI)
  apply (smt (z3) Collect_mono_iff Sils.simps(1) itree.sel(3) mem_Collect_eq ran_def rangeI)
  done

lemma stabilises_alt_def': 
  "stabilises_to R P = 
    ((\<exists> n F. Sils n (Vis F) = P \<and> ran F \<subseteq> Collect R) \<or> (\<exists> n x. Sils n (Ret x) = P))"
  by (auto simp add: stabilises_alt_def, metis itree.sel(3) rangeI, blast)
  
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

lemma stabilises_to_Sils_Vis [simp]: "stabilises_to R (Sils n (Vis F)) = (ran F \<subseteq> Collect R)"
  by (auto, auto simp add: Sils_Vis_iff stabilises_alt_def, metis Sils_Vis_not_Ret)

lemma no_divergence: "no_divergence P = (\<forall>tr P'. trace_of (tr, P') P \<longrightarrow> stabilises P')"
  apply (auto simp add: no_divergence_def min_divergence_of_def)
  using diverges_diverge diverges_implies_equal apply blast
  apply (meson diverges_diverge)
  done

lemma stabilises_to_no_divergence: 
  assumes "stabilises_to no_divergence P"
  shows "no_divergence P"
proof (clarsimp simp add: no_divergence)
  fix tr P'
  assume "P \<midarrow>tr\<leadsto> P'"
  hence "(\<lambda> (tr, P') P. stabilises P') (tr, P') P"
    using assms
    apply (induct rule: trace_to.induct)
      apply (auto)
    using stabilises_to.cases apply fastforce
    apply (metis itree.disc(7) itree.disc(8) itree.discI(3) itree.sel(3) no_divergence prod.simps(2) ranI stabilises_to.cases)
    done
  thus "stabilises P'"
    by auto
qed

lemma no_divergence_prefp_div_free:
  "stabilises_to no_divergence \<le> no_divergence"
  by (simp add: predicate1I stabilises_to_no_divergence)

lemma itree_disj_cases:
  "(\<exists> n F. P = Sils n (Vis F)) \<or> (\<exists> n x. P = Sils n (Ret x)) \<or> P = diverge"
  by (metis diverges_then_diverge is_Ret_def itree.collapse(3) itree.exhaust_disc stabilises_def)

lemma itree_cases:
  assumes 
    "\<And> n F. P = (Sils n (Vis F)) \<Longrightarrow> Q"
    "\<And> n x. P = (Sils n (Ret x)) \<Longrightarrow> Q"
    "P = diverge \<Longrightarrow> Q"
  shows "Q"
  by (metis assms(1) assms(2) assms(3) itree_disj_cases)

lemma trace_of_Sils [intro]: "trace_of ([], P) (Sils n P)"
  by (induct n, auto)

lemma no_divergence_Sil: "no_divergence (Sil P) = no_divergence P"
  by (force simp add: no_divergence)

lemma no_divergence_Sils: "no_divergence (Sils n P) = no_divergence P"
  by (induct n, simp_all add: no_divergence_Sil)

lemma no_divergence_Vis: "no_divergence (Vis F) = (ran F \<subseteq> Collect no_divergence)"
  apply (auto simp add: no_divergence)
  apply (smt (z3) domIff mem_Collect_eq option.sel option.simps(3) ran_def trace_to.intros(3))
  apply (metis no_divergence no_divergence_Sils split_conv stabilises_to_Sils_Vis stabilises_to_no_divergence)
  done

lemma no_divergence_stabilises_to: "no_divergence P \<Longrightarrow> stabilises_to no_divergence P"
  apply (cases P rule: itree_cases)
  apply (simp add: stabilises_alt_def' fun_eq_iff )
  apply (auto simp add: Sils_Vis_iff no_divergence_Sils no_divergence_Vis)
  done

lemma stabilises_to_is_no_diverge: "stabilises_to no_divergence = no_divergence"
  by (auto simp add: fun_eq_iff stabilises_to_no_divergence no_divergence_stabilises_to)

lemma Collect_no_div_lemma: "(\<not> A \<subseteq> Collect no_divergence) = (\<exists> Q \<in> A. \<not> no_divergence Q)"
  by (auto)

coinductive div_free :: "('e, 's) itree \<Rightarrow> bool" where
scons: "stabilises_to div_free P \<Longrightarrow> div_free P"

print_theorems

lemma div_free_diverge [simp]: "div_free diverge = False"
  by (meson div_free.simps diverges_diverge stabilises_to_stabilises)

lemma div_free_Sil [simp]: "div_free (Sil P) = div_free P"
  by (metis div_free.simps is_Ret_def itree.disc(2) itree.disc(5) itree.disc(6) itree.sel(2) sil_stbs stabilises_to.cases)

print_theorems

lemma div_free_is_upto: "div_free \<le> stabilises_to div_free"
  by (meson div_free.cases predicate1I)

lemma div_free_coind:
  assumes "\<phi> P"
  and "\<phi> \<le> stabilises_to \<phi>"
  shows "div_free P"
  using assms
  apply (coinduction arbitrary: P rule: div_free.coinduct)
  apply (auto)
  apply (metis (mono_tags, lifting) mono_stabilises_to predicate1I rev_predicate1D)
  done

lemma "no_divergence \<le> div_free"
  apply (auto)
  apply (rule div_free_coind[of "no_divergence"])
   apply (auto simp add: stabilises_to_is_no_diverge)
  done


lemma trace_to_Nil_Sils:
  assumes "P \<midarrow>[]\<leadsto> P'" 
  shows "\<exists> n. Sils n P' = P"
proof - 
  have "\<And> tr. P \<midarrow>tr\<leadsto> P' \<Longrightarrow> tr = [] \<longrightarrow> (\<exists> n. P = Sils n P')"
    by (induct_tac rule: trace_to.induct, auto, metis Sils_0, metis Sils.simps(2))
  thus ?thesis
    using assms by fastforce
qed


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
  by (metis case_prodD' option.sel trace_of_Sils trace_to_Sils trace_to_Vis trace_to_singleE)

lemma div_free_Vis: "div_free (Vis F) \<longleftrightarrow> (\<forall> P \<in> ran F. div_free P)"
  by (metis (mono_tags, lifting) Ball_Collect Vis_Sils Vis_not_Sils_Ret div_free.simps stabilises_alt_def')

lemma div_free_Sils: "div_free (Sils n P) \<longleftrightarrow> div_free P"
  by (induct n, auto)

lemma div_free_step: "\<lbrakk> P \<midarrow>[a]\<leadsto> P'; div_free P \<rbrakk> \<Longrightarrow> div_free P'"
  by (auto simp add: div_free_Vis div_free_Sils, meson div_free_Sils ranI)

lemma trace_to_Nil_diverges: "\<lbrakk> trace_of ([], diverge) P \<rbrakk> \<Longrightarrow> diverges P"
  using Sils_diverge diverges_then_diverge trace_to_Nil_Sils by force

lemma trace_to_div_free: "P \<midarrow>tr\<leadsto> P' \<Longrightarrow> div_free P \<Longrightarrow> div_free P'"
  apply (induct tr arbitrary: P)
  apply (metis div_free_Sils trace_to_Nil_Sils)
  apply (erule trace_to_ConsE)
  apply (auto)
  apply (meson div_free_Sils div_free_Vis ranI)
  done

lemma div_free_in_no_divergence: "div_free \<le> no_divergence"
  by (auto, metis div_free_diverge diverges_diverge diverges_implies_equal no_divergence split_conv trace_to_div_free)
  
lemma div_free_is_no_divergence: "div_free = no_divergence"
  by (simp add: antisym div_free_coind div_free_in_no_divergence predicate1I stabilises_to_is_no_diverge)


lemma div_free_no_min_divergence: "div_free P \<Longrightarrow> \<not> min_divergence_of t P"
  by (simp add: div_free_is_no_divergence no_divergence_def)

(*
theorem itree_coind[elim, consumes 1, case_names wform Ret Sil Vis, induct pred: "HOL.eq"]:
  assumes "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q) \<and> (is_Sil P \<longleftrightarrow> is_Sil Q) \<and> (is_Vis P \<longleftrightarrow> is_Vis Q)" and
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> P Q. \<phi> (Sil P) (Sil Q) \<Longrightarrow> \<phi> P Q" and
  "\<And> F G. \<phi> (Vis F) (Vis G) \<Longrightarrow> (dom(F) = dom(G) \<and> (\<forall> x\<in>dom(F). \<phi> (the (F x)) (the (G x))))"
  shows "P = Q"
  using assms
*)

lemma is_Sil_choice: "is_Sil (choice P Q) = (is_Sil P \<or> is_Sil Q)"
  using itree.exhaust_disc by (auto)

(*
lemma deadlock_l1: "\<And> P. (T\<^sub>1 = choice deadlock P \<and> T\<^sub>2 = P) \<or> (T\<^sub>1 = T\<^sub>2) \<Longrightarrow> T\<^sub>1 = T\<^sub>2"
  apply (simp only: deadlock_def)
  apply (coinduction arbitrary: T\<^sub>1 T\<^sub>2)
  apply (auto simp add: itree.case_eq_if itree.distinct_disc(3))
  using itree.distinct_disc(5) apply force
  using rel_map_iff apply blast+
  done
*)

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


lemma unstableE: "\<lbrakk> unstable P; \<And> P'. P = Sil P' \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  using is_Sil_def by auto

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
    apply (subgoal_tac "G x = Some y")
    apply (metis choice_deadlock choice_deadlock' option.sel)
    apply (smt choice.simps(3) choice.simps(6) itree.case_eq_if itree.disc(9) itree.sel(3) map_prod_commute prod.sel(1) snd_conv)
    done
qed

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

corec speak :: "('e, 's) itree" where
"speak = Vis (\<lambda> e. Some (Sil speak))"

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
   apply (simp add: ran_def)
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
  loop (\<lambda> s. choice (do { i \<leftarrow> inp Input; Ret (s @ [i]) }) 
                    (do { test (\<lambda> s. length s > 0) s;  
                          outp Output (hd s); 
                          Ret (tl s)
                        }))"

term "Input?(i) \<rightarrow> (\<lambda> s. Ret (s @ [i])) \<box> Skip"

subsection \<open> Code Generation \<close>

export_code bind_itree diverge loop echo buffer in Haskell module_name ITree

end