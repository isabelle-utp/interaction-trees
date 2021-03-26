section \<open> Circus Interaction Tree Semantics \<close>

theory ITree_Circus
  imports "ITree_Divergence" "Optics.Optics" "Shallow-Expressions.Shallow_Expressions"
begin

subsection \<open> Failures and Divergences \<close>

datatype ('e, 's) event = Ev (of_Ev: 'e) | Term 's ("\<cmark>")

type_synonym ('e, 's) trace = "('e, 's) event list"

lemma map_Ev_eq_iff [simp]: "map Ev xs = map Ev ys \<longleftrightarrow> xs = ys"
  by (metis event.inject(1) list.inj_map_strong)

definition traces :: "('e, 's) itree \<Rightarrow> ('e, 's) trace set" where
"traces P = {map Ev tr | tr. \<exists> P'. P \<midarrow>tr\<leadsto> P'} \<union> {map Ev tr @ [\<cmark>(v)] | tr v. P \<midarrow>tr\<leadsto> Ret v}"

definition straces :: "('e, 's) ktree \<Rightarrow> ('s \<Rightarrow> ('e, 's) trace set)" ("traces\<^sub>s") where
"straces K = (\<lambda> s. traces (K s))"

lemma Nil_in_traces [simp]: "[] \<in> traces P"
  by (auto simp add: traces_def)

lemma traces_prefix_in_Ev: "tr @ [\<cmark>(v)] \<in> traces(P) \<Longrightarrow> set tr \<subseteq> range Ev"
  by (auto simp add: traces_def)
     (metis Nil_is_map_conv event.distinct(1) last_map snoc_eq_iff_butlast)

lemma of_Ev_Ev [simp]: "(of_Ev \<circ> Ev) = id"
  by (auto)

lemma map_Ev_of_Ev [simp]: "set tr \<subseteq> range Ev \<Longrightarrow> map (Ev \<circ> of_Ev) tr = tr"
  by (metis (mono_tags, lifting) comp_def event.collapse(1) event.disc(1) map_idI rangeE subset_code(1))

lemma term_trace_iff [simp]: "tr @ [\<cmark>(v)] \<in> traces(P) \<longleftrightarrow> (set tr \<subseteq> range Ev \<and> P \<midarrow>map of_Ev tr\<leadsto> Ret v)"
  apply (auto simp add: traces_def map_idI)
  apply (metis append_eq_map_conv event.disc(2) is_Ev_def map_eq_Cons_D)
   apply (metis Nil_is_map_conv event.distinct(1) last_map snoc_eq_iff_butlast)
  done

lemma in_tracesE [elim]: 
  assumes
  "tr \<in> traces P"
  "\<And> P' tr'. \<lbrakk> tr = map Ev tr'; P \<midarrow>tr'\<leadsto> P' \<rbrakk> \<Longrightarrow> R"
  "\<And> P' tr' v. \<lbrakk> tr = map Ev tr' @ [\<cmark>(v)]; P \<midarrow>tr'\<leadsto> Ret v \<rbrakk> \<Longrightarrow> R"
  shows R
  using assms by (auto simp add: traces_def)

lemma not_in_traces [simp]: "set tr \<subseteq> range Ev \<Longrightarrow> tr \<notin> traces(P) \<longleftrightarrow> \<not> (\<exists> P'. P \<midarrow>map of_Ev tr\<leadsto> P')"
  by (simp add: traces_def, auto)

lemma traces_Ret: "traces (Ret x) = {[], [\<cmark>(x)]}"
  by (auto simp add: traces_def)

lemma traces_Tau: "traces (Sil P) = traces P"
  by (force simp add: traces_def)

lemma traces_Vis: "traces (Vis F) = {[]} \<union> {Ev a # tr | a tr. a \<in> dom(F) \<and> tr \<in> traces(the(F a))}"
  apply (auto elim!: in_tracesE trace_to_VisE)
  apply (auto simp add: traces_def)
  apply (metis domI list.map(2) option.sel trace_to_Vis)
  apply (metis domI list.simps(9) option.sel trace_to_Vis)
  done

lemma diverge_not_Ret [dest]: "diverge = Ret v \<Longrightarrow> False"
  by (metis div_free_Ret div_free_diverge)

lemma diverge_not_Vis [dest]: "diverge = Vis F \<Longrightarrow> False"
  by (metis diverges_diverge stabilises_Vis)

lemma diverge_no_Ret_trans [dest]: "diverge \<midarrow>tr\<leadsto> Ret v \<Longrightarrow> False"
  by (metis diverge_not_Ret diverges_diverge snd_conv trace_of_divergent)
  
lemma traces_diverge: "traces diverge = {[]}"
  by (auto simp add: traces_def dest: trace_of_divergent)

lemma map_of_Ev_append [simp]: "set tr \<subseteq> range Ev \<Longrightarrow> map of_Ev tr = tr\<^sub>1 @ tr\<^sub>2 \<longleftrightarrow> tr = (map Ev tr\<^sub>1 @ map Ev tr\<^sub>2)"
  by (auto, metis map_Ev_of_Ev map_append map_map)

lemma traces_bind: 
  "traces (P \<bind> Q) = 
  (traces(P) \<inter> lists (range Ev)) 
  \<union> {tr\<^sub>1 @ tr\<^sub>2 | tr\<^sub>1 tr\<^sub>2. \<exists> v. tr\<^sub>1 @ [\<cmark>(v)] \<in> traces(P) \<and> tr\<^sub>2 \<in> traces(Q v)}"
  apply (auto elim!: in_tracesE trace_to_bindE)
  apply (auto simp add: traces_def)
  apply (metis (no_types, lifting) Nil_is_map_conv append_Nil2 image_subset_iff list.set_map map_of_Ev_append range_eqI)
  apply (metis bind_RetE)
  apply (metis bind_RetE)
  apply (metis (no_types, lifting) append.right_neutral list.set_map list.simps(8) map_of_Ev_append subset_image_iff top_greatest)
  apply (metis append_Nil2 image_subset_iff list.set_map map_append map_of_Ev_append range_eqI)
  apply (meson trace_to_bind_left)
  apply (metis (no_types, lifting) map_Ev_of_Ev map_append map_map trace_to_bind)
  apply (metis (no_types, lifting) map_Ev_of_Ev map_append map_map trace_to_bind)
  done

text \<open> A failure is recorded when there is a trace leading to a stable interaction tree. At this
  point, the refusal is calculated. \<close>

definition failure_of :: "('e list \<times> 'e set) \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" where
"failure_of = (\<lambda> (tr, E) t. \<exists> t'. t \<midarrow>tr\<leadsto> t' \<and> is_Vis t' \<and> E \<subseteq> (- dom (un_Vis t')))"

definition failures :: "('e, 's) itree \<Rightarrow> ('e list \<times> 'e set) set" where
"failures P = {f. failure_of f P}"

lemma diverge_no_failures [dest]: "failure_of t diverge \<Longrightarrow> False"
  apply (simp add: failure_of_def prod.case_eq_if)
  apply (auto)
  apply (metis diverge.disc_iff diverges_diverge itree.distinct_disc(6) snd_conv trace_of_divergent)
  done

lemma failures_diverge: "failures diverge = {}"
  by (auto simp add: failures_def)

lemma failures_Vis: 
  "failures (Vis F) = {([], E) | E. E \<subseteq> - dom F} \<union> {(a # tr, E) | a tr E. a \<in> dom F \<and> (tr, E) \<in> failures (the (F a))}"
  apply (auto  simp add: failures_def failure_of_def)
    apply blast
  oops

subsection \<open> Main Operators \<close>

definition Skip :: "('e, 'r) ktree" where
"Skip = (\<lambda> s. Ret s)"

expr_ctr subst_id

lemma straces_Skip: "traces\<^sub>s (Skip) = ({[], [\<cmark> [\<leadsto>]]})\<^sub>e"
  by (simp add: Skip_def straces_def traces_Ret, expr_simp)

abbreviation Div :: "('e, 'r) ktree" where
"Div \<equiv> (\<lambda> s. diverge)"

text \<open> Deadlock is an interaction with no visible event \<close>

definition deadlock :: "('e, 'r) itree" where
"deadlock = Vis [\<mapsto>]"

lemma traces_deadlock: "traces(deadlock) = {[]}"
  by (auto simp add: deadlock_def)

abbreviation 
"Stop \<equiv> (\<lambda> s. deadlock)"

corec test :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) ktree" where
"test b = (\<lambda> s. if (b s) then Ret s else deadlock)"

lemma "test (\<lambda> s. False) = Stop"
  by (simp add: test.code)

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

definition inp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 'a) itree" where
"inp c = Vis (\<lambda> e. match\<^bsub>c\<^esub> e \<bind> Some \<circ> Ret)"

lemma traces_inp: "wb_prism c \<Longrightarrow> traces (inp c) = {[]} \<union> {[Ev (build\<^bsub>c\<^esub> v)] | v. True} \<union> {[Ev (build\<^bsub>c\<^esub> v), \<cmark> v] | v. True}" 
  apply (simp add: inp_def traces_Vis traces_Ret)
  apply (auto simp add: inp_def bind_eq_Some_conv elim!: in_tracesE trace_to_VisE)
   apply (meson wb_prism.build_match)
  apply (simp add: traces_Ret)
  done 

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

lemma choice_diverge: "choice diverge P = diverge"
  by (coinduction arbitrary: P, auto, metis diverge.code itree.simps(11))

lemma choice_Sils: "choice (Sils m P) Q = Sils m (choice P Q)"
  by (induct m, simp_all add: choice.code)

lemma choice_Sil_stable: "stable P \<Longrightarrow> choice P (Sil Q) = Sil (choice P Q)"
  by (cases P, simp_all add: choice.code)

lemma choice_Sils_stable: "stable P \<Longrightarrow> choice P (Sils m Q) = Sils m (choice P Q)"
  by (induct m, simp_all add: choice_Sil_stable)

lemma choice_Sils': "choice P (Sils m Q) = Sils m (choice P Q)"
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

lemma trace_of_deadlock: "deadlock \<midarrow>t\<leadsto> P \<Longrightarrow> (t, P) = ([], deadlock)"
  by (auto simp add: deadlock_def)

lemma deadlock_failure: "failure_of f deadlock \<Longrightarrow> \<exists> E. f = ([], E)"
  by (auto simp add: failure_of_def prod.case_eq_if, metis eq_fst_iff trace_of_deadlock)

lemma failures_deadlock: "failures deadlock = {([], E) | E. True}"
  apply (auto simp add: failures_def )
  apply (meson deadlock_failure prod.inject)
  apply (metis (mono_tags, lifting) compl_le_swap1 deadlock_def dom_empty empty_subsetI failure_of_def itree.disc(9) itree.sel(3) old.prod.case trace_to_Nil)
  done

text \<open> A (minimal) divergence trace is recorded when there is a trace that leads to a divergent state. \<close>

definition min_divergence_of :: "'e list \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" where
"min_divergence_of tr P = P \<midarrow>tr\<leadsto> diverge"

lemma min_divergence_diverge [intro]: "min_divergence_of [] diverge"
  by (simp add: min_divergence_of_def trace_to_Nil)


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