theory ITree_Circus
  imports "Interaction_Trees" "Optics.Optics" "UTP.utp_pred"
begin recall_syntax

primcorec diverge :: "('e, 'r) itree" where
"diverge = Tau diverge"

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

term "[x \<mapsto>\<^sub>s &x + 1, y \<mapsto>\<^sub>s True]"

definition assigns :: "'s usubst \<Rightarrow> ('e, 's) ktree" where
"assigns \<sigma> = (\<lambda> s. Ret (\<lbrakk>\<sigma>\<rbrakk>\<^sub>e s))"

syntax
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  ("'(_') := '(_')")  
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=" 62)
  "_mk_usubst"      :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> usubst"

translations
  "_mk_usubst \<sigma> (_svid_unit x) v" \<rightleftharpoons> "\<sigma>(&x \<mapsto>\<^sub>s v)"
  "_mk_usubst \<sigma> (_svid_list x xs) (_uexprs v vs)" \<rightleftharpoons> "(_mk_usubst (\<sigma>(&x \<mapsto>\<^sub>s v)) xs vs)"
  "_assignment xs vs" => "CONST assigns (_mk_usubst id\<^sub>s xs vs)"
  "_assignment x v" <= "CONST assigns (CONST subst_upd id\<^sub>s x v)"
  "_assignment x v" <= "_assignment (_spvar x) v"
  "_assignment x v" <= "_assignment x (_UTP v)"

term "x := e"

corec loop :: "('e, 'r) ktree \<Rightarrow> ('e, 'r) ktree" where
"loop P e = Tau (P e \<bind> loop P)"

lemma bind_diverge: "diverge \<bind> F = diverge"
  by (coinduction, auto simp add: itree.case_eq_if)

definition inp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 'a) itree" where
"inp c = Vis (\<lambda> e. case match\<^bsub>c\<^esub> e of Some v \<Rightarrow> Some (Ret v) | _ \<Rightarrow> None)"

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
      (Tau P', _) \<Rightarrow> Tau (choice P' Q) |
      (_, Tau Q') \<Rightarrow> Tau (choice P Q') |
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

lemma "X \<noteq> Y \<Longrightarrow> choice (Tau (Vis [X \<mapsto> Ret a])) (Tau (Vis [Y \<mapsto> Ret b])) = 
       Tau (Tau (Vis [X \<mapsto> Ret a, Y \<mapsto> Ret b]))"
  by (simp add: choice.code map_prod_merge fun_upd_twist)

text \<open> This requires weak bisimulation \<close>

lemma "\<And> P. (X = choice P P \<and> Y = P) \<or> (X = Y) \<Longrightarrow> X = Y"
  apply (coinduction arbitrary: X Y)
  apply (auto simp add: itree.case_eq_if itree.distinct_disc(1))
  oops

fun Taus :: "nat \<Rightarrow> ('e, 's) itree \<Rightarrow> ('e, 's) itree" where
"Taus 0 P = P" |
"Taus (Suc n) P = Tau (Taus n P)"

lemma is_Ret_Taus [simp]: "is_Ret (Taus n P) \<longleftrightarrow> n = 0 \<and> is_Ret P"
  by (metis Taus.elims itree.disc(2) less_numeral_extra(3) zero_less_Suc)

lemma is_Vis_Taus [simp]: "is_Vis (Taus n P) \<longleftrightarrow> n = 0 \<and> is_Vis P"
  by (metis Taus.elims Taus.simps(1) itree.disc(8))

lemma is_Tau_Taus: "is_Tau (Taus n P) \<longleftrightarrow> (n > 0 \<or> is_Tau P)"
  by (metis Taus.simps(1) is_Ret_Taus is_Vis_Taus itree.exhaust_disc neq0_conv)

lemma un_Tau_Taus [simp]: "un_Tau (Taus n P) = (if n = 0 then un_Tau P else Taus (n - 1) P)"
  by (cases n, simp_all)

lemma Taus_Taus [simp]: "Taus m (Taus n P) = Taus (m + n) P"
  by (induct m, simp_all)

(*
lemma [elim!]: "\<lbrakk> is_Ret (Taus n P); \<lbrakk> n = 0; is_Ret P \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  using is_Ret_Taus by force
  

lemma [elim!]: "\<lbrakk> is_Vis (Taus n P); \<lbrakk> n = 0; is_Vis P \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (metis Taus.elims itree.disc(8))

lemma [elim!]: "\<lbrakk> is_Ret (Taus (m + n) P); \<lbrakk> m = 0; n = 0; is_Ret P \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (metis Taus.simps(1) is_Ret_Taus zero_eq_add_iff_both_eq_0)
  

lemma is_VisE2 [elim!]: "\<lbrakk> is_Vis (Taus (m + n) P); \<lbrakk> m = 0; n = 0; is_Vis P \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (metis Taus.elims itree.disc(8) zero_eq_add_iff_both_eq_0)
*)  

text \<open> A stable process has no possible internal activity \<close>

abbreviation "unstable P \<equiv> is_Tau P"
abbreviation "stable P \<equiv> \<not> unstable P"

translations "CONST stable P" <= "\<not> CONST unstable P"

lemma "unstable diverge"
  by simp

text \<open> A process converges if it stabilises within a finite number of internal events \<close>

definition "converges P = (\<exists> n P'. (P = Taus n P' \<and> stable P'))"

abbreviation "diverges P \<equiv> (\<not> (converges P))"

translations "CONST diverges P" <= "\<not> (CONST converges P)"

lemma diverges_implies_unstable [intro]: "diverges P \<Longrightarrow> unstable P"
  by (metis Taus.simps(1) converges_def)

lemma Taus_injective: "Taus n P = Taus n Q \<Longrightarrow> P = Q"
  by (induct n, simp_all)

lemma Taus_diverge: "Taus n diverge = diverge"
  by (induct n, simp_all, metis diverge.code)

lemma diverges_diverge: "diverges diverge"
  by (auto simp add: converges_def Taus_diverge, metis Taus_diverge Taus_injective diverge.disc_iff)

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
  case (Tau P' Q' P Q)
  then show ?case
    by (metis Taus.simps(2) converges_def)
next
  case (Vis F G P Q)
  then show ?case
    using diverges_implies_unstable itree.disc(6) by blast
qed

lemma Tau_cycle_diverge: "\<lbrakk> is_Tau P; un_Tau P = P \<rbrakk> \<Longrightarrow> P = diverge"
  by (coinduction arbitrary: P, auto)

lemma diverges_then_diverge: "diverges P \<longleftrightarrow> P = diverge"
  using diverges_diverge diverges_implies_equal by blast

lemma choice_diverge: "choice diverge P = diverge"
  by (coinduction arbitrary: P, auto, metis diverge.code itree.simps(11))

lemma choice_Taus: "choice (Taus m P) Q = Taus m (choice P Q)"
  by (induct m, simp_all add: choice.code)

lemma choice_Tau_stable: "stable P \<Longrightarrow> choice P (Tau Q) = Tau (choice P Q)"
  by (cases P, simp_all add: choice.code)

lemma choice_Taus_stable: "stable P \<Longrightarrow> choice P (Taus m Q) = Taus m (choice P Q)"
  by (induct m, simp_all add: choice_Tau_stable)

lemma choice_Taus': "choice P (Taus m Q) = Taus m (choice P Q)"
proof (cases "diverges P")
  case True
  then show ?thesis
    by (metis Taus_diverge choice_diverge diverges_then_diverge) 
next
  case False
  then obtain n P' where "P = Taus n P'" "stable P'"
    using converges_def by blast
  then show ?thesis
    by (simp add: choice_Taus choice_Taus_stable add.commute)
qed

inductive trace_of :: "('e list \<times> ('e, 's) itree) \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" where
trace_of_Nil: "trace_of ([], P) P" | 
trace_of_Tau: "trace_of (tr, P) Q \<Longrightarrow> trace_of (tr, P) (Tau Q)" |
trace_of_Vis: "\<lbrakk> e \<in> dom F; trace_of (tr, P) (the (F e)) \<rbrakk> \<Longrightarrow> trace_of (e # tr, P) (Vis F)"

inductive div_free' :: "(('e, 's) itree \<Rightarrow> bool) \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" where
ret_dfree': "div_free' R (Ret x)" |
tau_dfree': "div_free' R P \<Longrightarrow> div_free' R (Tau P)" |
vis_dfree': "(\<And> t. t \<in> ran F \<Longrightarrow> R t) \<Longrightarrow> div_free' R (Vis F)"

thm div_free'.induct

lemma monotonic_div_free': "div_free' x P \<Longrightarrow> x \<le> y \<Longrightarrow> div_free' y P"
  apply (induct rule: div_free'.induct)
  apply (simp_all add: ret_dfree' tau_dfree' vis_dfree')
  apply (simp add: predicate1D vis_dfree')
  done

lemma mono_div_free' [mono add]: "x \<le> y \<Longrightarrow> div_free' x \<le> div_free' y"
  using monotonic_div_free' by auto
  
coinductive div_free :: "('e, 's) itree \<Rightarrow> bool" where
scons: "div_free' div_free P \<Longrightarrow> div_free P"

(*
theorem itree_coind[elim, consumes 1, case_names wform Ret Tau Vis, induct pred: "HOL.eq"]:
  assumes "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q) \<and> (is_Tau P \<longleftrightarrow> is_Tau Q) \<and> (is_Vis P \<longleftrightarrow> is_Vis Q)" and
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> P Q. \<phi> (Tau P) (Tau Q) \<Longrightarrow> \<phi> P Q" and
  "\<And> F G. \<phi> (Vis F) (Vis G) \<Longrightarrow> (dom(F) = dom(G) \<and> (\<forall> x\<in>dom(F). \<phi> (the (F x)) (the (G x))))"
  shows "P = Q"
  using assms
*)

lemma div_free_coind:
  assumes "\<phi> P"
  and "\<phi> \<le> div_free' \<phi>"
  shows "div_free P"
  using assms
  apply (coinduction arbitrary: P rule: div_free.coinduct)
  apply (auto)
  apply (metis (mono_tags, lifting) mono_div_free' predicate1I rev_predicate1D)
  done

lemma is_Tau_choice: "is_Tau (choice P Q) = (is_Tau P \<or> is_Tau Q)"
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
  case (Tau P' Q' P)
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
  case Tau
  then show ?case
    by (metis choice.sel(2) itree.disc(5) itree.sel(2) itree.simps(11) prod.sel(1))
next
  case Vis
  then show ?case
    by (metis choice.simps(6) deadlock_def itree.disc(9) itree.sel(3) itree.simps(12) map_prod_empty(1) prod.sel(1) snd_conv)
qed


lemma unstableE: "\<lbrakk> unstable P; \<And> P'. P = Tau P' \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  using is_Tau_def by auto

lemma choice_Tau': "choice P (Tau Q) = choice (Tau P) Q"
proof (coinduction arbitrary: P Q rule: itree_strong_coind)
case wform
  then show ?case
    by (meson is_Tau_choice itree.disc(2) itree.disc(8) itree.distinct_disc(1) itree.distinct_disc(6) itree.exhaust_disc)
next
  case Ret
  then show ?case
    by (metis is_Tau_choice itree.disc(4) itree.disc(5)) 
next
  case (Tau P Q P' Q')
  then show ?case
    by (metis (no_types, lifting) choice.sel(2) choice_Tau_stable itree.collapse(2) itree.disc(5) itree.sel(2) itree.simps(11) prod.sel(1))    
next
  case Vis
  then show ?case
    by (metis is_Tau_choice itree.disc(5) itree.disc(6)) 
qed


lemma choice_unstable: "unstable P \<Longrightarrow> choice P Q = Tau (choice (un_Tau P) Q)"
  by (metis (no_types, lifting) choice.ctr(2) itree.collapse(2) itree.simps(11) prod.sel(1))

lemma choice_unstable': "unstable Q \<Longrightarrow> choice P Q = Tau (choice P (un_Tau Q))"
  by (metis choice_Tau' choice_Tau_stable choice_unstable itree.collapse(2))

lemma choice_commutative:
  "choice P Q = choice Q P"
proof (coinduction arbitrary: P Q rule: itree_coind)
  case wform
  then show ?case
    by (metis choice.disc_iff(1) choice.simps(3) is_Tau_choice prod.sel(1) snd_conv)
next
  case Ret
  then show ?case
    by (smt choice.disc_iff(1) choice.simps(3) choice.simps(4) itree.case_eq_if itree.disc(7) itree.sel(1) prod.sel(1) snd_conv un_Ret_def)
next
  case (Tau P Q P' Q')
  then show ?case
  proof (cases "unstable P'")
    case True
    with Tau have "P = choice (un_Tau P') Q'" "Q = choice Q' (un_Tau P')"
      by (simp_all add: choice_unstable choice_unstable')
    thus ?thesis
      by blast
  next
    case False
      then show ?thesis
        by (metis Tau(1) Tau(2) choice_Tau_stable choice_deadlock' choice_unstable is_Tau_choice itree.discI(2) itree.sel(2))
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
"speak = Vis (\<lambda> e. Some (Tau speak))"

lemma "div_free speak"
  (* We need to find the right pattern to find divergence freedom using Tarki theorem *)
  apply (coinduct rule: div_free_coind[where \<phi>="\<lambda> x. \<exists> n. x = Taus n speak"])
  apply (rule_tac x="0" in exI)
  apply (simp)
  apply (auto)
  apply (induct_tac n)
  apply (simp)
  apply (subst speak.code) back
   apply (rule vis_dfree')
   apply (simp add: ran_def)
  apply (rule_tac x="1" in exI, simp)
  apply (simp)
  apply (rule tau_dfree')
  apply (simp)
  done

definition "echo = loop (\<lambda>_. do { i \<leftarrow> inp Input; outp Output i })"


lemma "trace_of ([build\<^bsub>Input\<^esub> 1, build\<^bsub>Output\<^esub> 1], echo ()) (echo ())"
  apply (subst echo_def) back
  apply (subst loop.code)
  apply (subst echo_def[THEN sym])
  apply (rule trace_of_Tau)
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