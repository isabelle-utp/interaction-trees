section \<open> CSP Operators \<close>

theory ITree_CSP
  imports ITree_Choice ITree_Parallel
begin

subsection \<open> Basic Constructs \<close>

definition skip :: "('e, unit) itree" where
"skip = Ret ()"

lemma skip_stable_genchoice_left: 
  "stable P \<Longrightarrow> genchoice \<M> skip P = skip"
  by (simp add: Ret_unit_stable_genchoice_left skip_def)
  
lemma skip_stable_genchoice_right:
  assumes "stable P"
  shows "genchoice \<M> P skip = skip"
  by (simp add: Ret_unit_stable_genchoice_right assms skip_def)

definition inp_in_where :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('e, 'a) itree" where
"inp_in_where c A P = Vis (prism_fun c A (\<lambda> x. (P x, Ret x)))"

abbreviation "inp_in c A \<equiv> inp_in_where c A (\<lambda> s. True)"

abbreviation "inp_where c P \<equiv> inp_in_where c UNIV P"

lemma retvals_inp_in_where: "wb_prism c \<Longrightarrow> \<^bold>R(inp_in_where c A P) = {x \<in> A. P x}"
  by (auto simp add: inp_in_where_def prism_fun_def)
     (metis image_insert insertCI insert_Diff option.sel retvals_Ret wb_prism.match_build)

lemma retvals_inp_in: "wb_prism c \<Longrightarrow> \<^bold>R(inp_in c A) = A"
  by (simp add: retvals_inp_in_where)

lemma div_free_inp_in: "div_free (inp_in c A)"
  by (auto simp add: inp_in_where_def prism_fun_def div_free_Vis)

abbreviation inp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e)\<Rightarrow> ('e, 'a) itree" where
"inp c \<equiv> inp_in c UNIV"

definition inp_list :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a list \<Rightarrow> ('e, 'a) itree" where
"inp_list c B = Vis (pfun_of_alist (map (\<lambda>x. (build\<^bsub>c\<^esub> x, \<checkmark> (the (match\<^bsub>c\<^esub> (build\<^bsub>c\<^esub> x))))) (filter (\<lambda>x. build\<^bsub>c\<^esub> x \<in> dom match\<^bsub>c\<^esub> ) B)))"

definition inp_list_where :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('e, 'a) itree" where
"inp_list_where c B P = Vis (pfun_of_alist (map (\<lambda>x. (build\<^bsub>c\<^esub> x, \<checkmark> x)) (filter P B)))"

definition inp_map_in_where :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('e, 'a) itree" where
"inp_map_in_where c B P = Vis (pfun_of_map (\<lambda> e. case match\<^bsub>c\<^esub> e of 
                                                  Some v \<Rightarrow> if (v \<in> B \<and> P v) then Some (Ret v) else None | 
                                                  None \<Rightarrow> None))"

definition inp_map :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e)\<Rightarrow> ('e, 'a) itree" where
"inp_map c = Vis (pfun_of_map (\<lambda> e. case match\<^bsub>c\<^esub> e of Some v \<Rightarrow> Some (Ret v) | None \<Rightarrow> None))"

lemma inp_in_where_map_code [code_unfold]:
  "wb_prism c \<Longrightarrow> inp_in_where c A P = inp_map_in_where c A P"
  apply (auto simp add: inp_in_where_def prism_fun_def inp_map_in_where_def fun_eq_iff pfun_eq_iff domI pdom.abs_eq option.case_eq_if)
  apply (metis (no_types, opaque_lifting) imageI option.distinct(1) option.exhaust_sel wb_prism_def)
  done

lemma inp_in_where_list_code [code_unfold]:
  "wb_prism c \<Longrightarrow> inp_in_where c (set xs) P = inp_list_where c xs P"
  unfolding inp_in_where_def prism_fun_def inp_list_where_def
  by (simp only: set_map [THEN sym] inter_set_filter pabs_set filter_map comp_def, simp add: comp_def)

lemma inp_map_in_where_list_code [code_unfold]:
  "wb_prism c \<Longrightarrow> inp_map_in_where c (set xs) P = inp_list_where c xs P"
  by (metis inp_in_where_list_code inp_in_where_map_code)

(*
lemma inp_where_code [code_unfold]:
  "wb_prism c \<Longrightarrow>inp_where c P = Vis (pfun_of_map (\<lambda> e. case match\<^bsub>c\<^esub> e of Some v \<Rightarrow> if (P v) then Some (Ret v) else None | None \<Rightarrow> None))"
  apply (auto simp add: inp_in_where_def fun_eq_iff pfun_eq_iff domI pdom.abs_eq option.case_eq_if)
  apply (metis domIff option.simps(3) wb_prism.range_build)
  apply (meson option.distinct(1) option.exhaust_sel)
*)

lemma build_in_dom_match [simp]: "wb_prism c \<Longrightarrow> build\<^bsub>c\<^esub> x \<in> dom match\<^bsub>c\<^esub>"
  by (simp add: dom_def)

text \<open> Is there a way to use this optimise the above definition when applied to a well-behaved prism? \<close>

lemma inp_list_wb_prism: "wb_prism c \<Longrightarrow> inp_list c B = Vis (pfun_of_alist (map (\<lambda>x. (build\<^bsub>c\<^esub> x, \<checkmark> x)) B))"
  by (simp add: inp_list_def)

lemma inp_where_enum [code_unfold]:
  assumes "wb_prism c"
  shows "inp_where c P = inp_list_where c enum_class.enum P"
proof -
  have "inp_where c P = inp_in_where c (set enum_class.enum) P"
    by (simp add:  enum_class.UNIV_enum)
  also have "... = inp_list_where c enum_class.enum P"
    by (simp add: assms inp_in_where_list_code)
  finally show ?thesis .
qed

lemma inp_map_where_enum [code_unfold]:
  assumes "wb_prism c"
  shows "inp_map_in_where c UNIV P = inp_list_where c enum_class.enum P"
  using inp_where_enum[of c P] by (simp add: inp_in_where_map_code assms)

(*
lemma inp_alist [code]:
  "inp_in c (set B) = inp_list c B"
  unfolding inp_in_where_def inp_list_def
  by (simp only: set_map[THEN sym] inter_set_filter pabs_set filter_map comp_def, simp add: comp_def)

lemma inp_enum [code_unfold]:
  "wb_prism c \<Longrightarrow> inp c = inp_list c enum_class.enum"
  apply (simp add: inp_list_def inp_in_where_def wb_prism.range_build[THEN sym] enum_class.UNIV_enum)
  apply (simp only: image_set pabs_set)
  apply (simp add: comp_def)
  done

lemma inp_in_coset [code_unfold]: 
  "wb_prism c \<Longrightarrow> inp_in c (List.coset []) = Vis (pfun_of_map (\<lambda> e. case match\<^bsub>c\<^esub> e of Some v \<Rightarrow> Some (Ret v) | None \<Rightarrow> None))"
  by (auto simp add: inp_in_def pabs_def pfun_entries_def pdom_res_def pfun_of_map_inject restrict_map_def fun_eq_iff domIff wb_prism.range_build)
*)

definition outp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a \<Rightarrow> ('e, unit) itree" where
"outp c v = Vis (pfun_of_alist [(build\<^bsub>c\<^esub> v, Ret())])"

lemma outp_as_inp: "outp c v = (inp_in c {v} \<then> Ret ())"
  by (simp add: outp_def inp_in_where_def prism_fun_def pabs_insert_maplet)

definition sync :: "(unit \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, unit) itree" where
"sync c = Vis (pfun_of_alist [(build\<^bsub>c\<^esub> (), Ret())])"

definition guard :: "bool \<Rightarrow> ('e, unit) itree" where
"guard b = (if b then Ret () else deadlock)"

subsection \<open> External Choice \<close>

text \<open> Combine two partial functions accepting only the disjoint parts of each. \<close>

definition excl_comb :: "('a \<Zpfun> 'b) \<Rightarrow> ('a \<Zpfun> 'b) \<Rightarrow> ('a \<Zpfun> 'b)" (infixr "\<odot>" 100) where
"excl_comb f g = (pdom(g) \<Zndres> f) \<oplus> (pdom(f) \<Zndres> g)"

lemma excl_comb_commute: "x \<odot> y = y \<odot> x"
  apply (auto simp add: fun_eq_iff excl_comb_def option.case_eq_if)
  apply (metis Compl_iff IntD1 IntD2 pdom_pdom_res pfun_override_commute_weak)
  done

lemma excl_comb_empty [simp]: "x \<odot> {}\<^sub>p = x" "{}\<^sub>p \<odot> x = x"
  by (simp_all add: excl_comb_def)

lemma excl_comb_merge: 
  "f(x \<mapsto> v)\<^sub>p \<odot> g = 
  (if (x \<notin> pdom(g)) then (f \<odot> g)(x \<mapsto> v)\<^sub>p else {x} \<Zndres> (f \<odot> g))"
  by (auto simp add: excl_comb_def)
     (metis (no_types, opaque_lifting) Compl_Un insert_absorb insert_is_Un)

lemma excl_comb_as_ovrd:
  assumes "pdom(f) \<inter> pdom(g) = {}"
  shows "f \<odot> g = f \<oplus> g"
  by (simp add: excl_comb_def assms inf.commute pdom_nres_disjoint)

lemma excl_comb_pfun_of_map [code]:
  "excl_comb (pfun_of_map f) (pfun_of_map g) = 
     pfun_of_map (\<lambda> x. case (f x, g x) of
                       (Some _, Some _) \<Rightarrow> None |
                       (Some y, None) \<Rightarrow> Some y |
                       (None, Some y) \<Rightarrow> Some y |
                       (None, None) \<Rightarrow> None)"
  by (auto simp add: excl_comb_def pdom_def pdom_res_def restrict_map_def oplus_pfun_def map_add_def 
      pfun_of_map_inject fun_eq_iff option.case_eq_if)

lemma excl_comb_pfun_of_alist [code]:
  "excl_comb (pfun_of_alist xs) (pfun_of_alist ys) =
    pfun_of_alist (AList.restrict (- fst ` set xs) ys @ AList.restrict (- fst ` set ys) xs)"
  by (simp add: excl_comb_def pdom_res_alist plus_pfun_alist)

lemma excl_comb_pfun_of_map_alist [code]: "(pfun_of_map f) \<odot> (pfun_of_alist xs) 
  = pfun_of_map
     (\<lambda>x. case f x of None \<Rightarrow> (case map_of xs x of None \<Rightarrow> None | Some x \<Rightarrow> Some x) 
        | Some xa \<Rightarrow> (case map_of xs x of None \<Rightarrow> Some xa | Some x \<Rightarrow> Map.empty x))"
  by (simp add: pfun_of_alist.abs_eq excl_comb_pfun_of_map)

lemma excl_comb_pfun_of_alist_map [code]: "(pfun_of_alist xs) \<odot> (pfun_of_map p)
  = pfun_of_map
     (\<lambda>x. case map_of xs x of None \<Rightarrow> (case p x of None \<Rightarrow> None | Some x \<Rightarrow> Some x)
        | Some xa \<Rightarrow> (case p x of None \<Rightarrow> Some xa | Some x \<Rightarrow> Map.empty x))"
  by (simp add: pfun_of_alist.abs_eq excl_comb_pfun_of_map)

lemma excl_comb_Nil_alist [code]: 
  "(pfun_of_alist []) \<odot> P = P"
  "P \<odot> (pfun_of_alist []) = P"
  by simp_all

definition excl_combs :: "('a \<Zpfun> 'b) list \<Rightarrow> 'a \<Zpfun> 'b" where
"excl_combs Ps = foldr (\<odot>) Ps {}\<^sub>p"

text \<open> This is like race-free behaviour \<close>

class extchoice = 
  fixes extchoice :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<box>" 59)

text \<open> This is an completion of Hoare's bar operator. \<close>

instantiation itree :: (type, type) extchoice 
begin

text \<open> cf. RAISE language "interlock" operator -- basic operators of CCS vs. CSP operators. Can
  this be expressed in terms of operators? \<close>

definition extchoice_itree :: "('e, 'a) itree \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'a) itree"  where
"extchoice_itree = genchoice (\<odot>)"

instance ..

end

lemma choice_Vis_Vis [simp]: "(Vis F) \<box> (Vis G) = Vis (F \<odot> G)"
  by (simp add: extchoice_itree_def)

lemma choice_diverge: "diverge \<box> P = diverge"
  by (simp add: extchoice_itree_def genchoice_diverge)

lemma is_Sil_choice: "is_Sil (P \<box> Q) = (is_Sil P \<or> is_Sil Q)"
  by (metis extchoice_itree_def is_Sil_genchoice)
  
lemma choice_Vis_iff: 
  "P \<box> Q = Vis H \<longleftrightarrow> ((\<exists> F G. P = Vis F \<and> Q = Vis G \<and> H = (F \<odot> G)) \<or> (\<exists> x y. P = Ret x \<and> Q = Ret y \<and> x \<noteq> y \<and> H = {}\<^sub>p))"
  by (simp add: extchoice_itree_def genchoice_Vis_iff)
  
lemma choice_VisE [elim]:
  assumes "Vis H = P \<box> Q"
  "\<And> F G. \<lbrakk> P = Vis F; Q = Vis G; H = (F \<odot> G) \<rbrakk> \<Longrightarrow> R"
  "\<And> x y. \<lbrakk> P = Ret x; Q = Ret y; x \<noteq> y; H = {}\<^sub>p \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms(1) assms(2) assms(3) choice_Vis_iff)

lemma choice_Sils: "(Sils m P) \<box> Q = Sils m (P \<box> Q)"
  by (simp add: extchoice_itree_def genchoice_Sils)

lemma choice_Sil_stable: "stable P \<Longrightarrow> P \<box> (Sil Q) = Sil (P \<box> Q)"
  by (simp add: extchoice_itree_def genchoice_Sil_stable)

lemma choice_Sils_stable: "stable P \<Longrightarrow> P \<box> (Sils m Q) = Sils m (P \<box> Q)"
  by (simp add: extchoice_itree_def genchoice_Sils_stable)

lemma choice_Sils': "P \<box> (Sils m Q) = Sils m (P \<box> Q)"
  by (simp add: extchoice_itree_def genchoice_Sils')

text \<open> External Choice test cases \<close>

lemma "X \<noteq> Y \<Longrightarrow> (Vis {X \<mapsto> Ret a}\<^sub>p) \<box> (Vis {Y \<mapsto> Ret b}\<^sub>p) = 
       Vis {X \<mapsto> Ret a, Y \<mapsto> Ret b}\<^sub>p"
  by (auto simp add: genchoice.code excl_comb_merge pfun_upd_comm)

lemma "(Vis {X \<mapsto> Ret a}\<^sub>p) \<box> (Vis {X \<mapsto> Ret b}\<^sub>p) = 
       deadlock"
  by (simp add: deadlock_def excl_comb_merge)

lemma "X \<noteq> Y \<Longrightarrow> (Sil (Vis {X \<mapsto> Ret a}\<^sub>p)) \<box> (Sil (Vis {Y \<mapsto> Ret b}\<^sub>p)) = 
       Sil (Sil (Vis {X \<mapsto> Ret a, Y \<mapsto> Ret b}\<^sub>p))"
  by (simp add: genchoice.code extchoice_itree_def excl_comb_merge pfun_upd_comm)

text \<open> This requires weak bisimulation \<close>

lemma "\<And> P. (X = (P :: ('e, 's) itree) \<box> P \<and> Y = P) \<or> (X = Y) \<Longrightarrow> X = Y"
  apply (coinduction arbitrary: X Y)
  apply (auto simp add: itree.case_eq_if itree.distinct_disc(1))
  oops

lemma choice_deadlock [simp]: "deadlock \<box> P = P"
  by (simp add: extchoice_itree_def)

lemma choice_deadlock' [simp]: "P \<box> deadlock = P"
  by (simp add: extchoice_itree_def)

lemma choice_unstable: "unstable P \<Longrightarrow> P \<box> Q = Sil ((un_Sil P) \<box> Q)"
  by (simp add: extchoice_itree_def genchoice_unstable)

lemma choice_unstable': "unstable Q \<Longrightarrow> P \<box> Q = Sil (P \<box> (un_Sil Q))"
  by (simp add: extchoice_itree_def genchoice_unstable')

lemma choice_commutative:
  fixes P Q :: "('e, 's) itree"
  shows "P \<box> Q = Q \<box> P"
  by (simp add: extchoice_itree_def genchoice_commutative excl_comb_commute)

text \<open> External choice is commutative, but currently not associative. This is because when we
  have two competing return values, external choice deadlocks. However, since a return takes 
  priority over a visible event, that means the order in which deadlocks are produced and 
  returns occur is significant. Perhaps competing returns should lead to a divergence, which
  would then take priority over a return. \<close>

lemma skip_stable_choice: 
  assumes "stable P"
  shows "skip \<box> P = skip"
  by (simp add: assms extchoice_itree_def skip_stable_genchoice_left)

lemma choice_RetE [elim]:
  assumes "P \<box> Q = \<checkmark> x" 
    "\<lbrakk> P = Ret x; Q = Ret x\<rbrakk> \<Longrightarrow> R"
    "\<lbrakk> P = Ret x; is_Vis Q \<rbrakk> \<Longrightarrow> R"
    "\<lbrakk> Q = Ret x; is_Vis P \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) extchoice_itree_def genchoice_RetE)

lemma extchoice_Vis_bind:
  "(Vis F \<box> Vis G) \<bind> R = (Vis F \<bind> R) \<box> (Vis G \<bind> R)"
  by (simp add: excl_comb_def)

lemma 
  assumes "is_Vis P" "is_Vis Q" "\<^bold>I(P) \<inter> \<^bold>I(Q) = {}"
  shows "\<^bold>R(P \<box> Q) = \<^bold>R(P) \<union> \<^bold>R(Q)"
proof -
  obtain F G where P: "P = Vis F" and Q: "Q = Vis G"
    by (meson assms(1) assms(2) is_VisE)
  hence "pdom(F) \<inter> pdom(G) = {}"
    using assms(3) by force
  thus ?thesis
    by (simp add: P Q excl_comb_as_ovrd Un_commute pdom_nres_disjoint)
qed

lemma trace_to_Nil_extchoice: "P \<midarrow>[]\<leadsto> P' \<Longrightarrow> P \<box> Q \<midarrow>[]\<leadsto> P' \<box> Q"
  using choice_Sils trace_to_Nil_iff by blast

lemma choice_Ret_Ret: "\<checkmark> x \<box> \<checkmark> y = (if x = y then \<checkmark> x else deadlock)"
  by (auto simp add: extchoice_itree_def genchoice.ctr(1) deadlock_def genchoice_Vis_iff)

lemma choice_Ret_Vis: "\<checkmark> x \<box> Vis G = \<checkmark> x"
  by (simp add: extchoice_itree_def genchoice.ctr(1))

lemma pran_excl_comb: "pran (F \<odot> G) \<subseteq> pran F \<union> pran G"
  by (auto simp add: excl_comb_def)
     (metis Un_iff pfun_split_domain pran_override)+

lemma stabilises_retvals_extchoice:
  assumes "stabilises P" "stabilises Q"
  shows "\<^bold>R(P \<box> Q) \<subseteq> \<^bold>R(P) \<union> \<^bold>R(Q)"
proof -
  obtain m n P' Q' where PQ: "P = Sils m P'" "stable P'" "Q = Sils n Q'" "stable Q'"
    by (metis assms(1) assms(2) stabilises_def)
  show ?thesis
  proof (cases "P'")
    case (Ret x)
    note Ret_P' = this
    then show ?thesis
    proof (cases Q')
      case (Ret y)
      with Ret_P' PQ show ?thesis
        by (simp add: choice_Sils choice_Sils' choice_Ret_Ret)
    next
      case (Sil _)
      then show ?thesis
        using PQ(4) by auto
    next
      case (Vis G)
      with Ret_P' PQ show ?thesis
        by (simp add: choice_Sils choice_Sils')
           (metis choice_Ret_Vis insertCI retvals_Ret singletonD subsetI)
    qed
  next
    case (Sil _)
    then show ?thesis
      using PQ(2) by auto
  next
    case (Vis F)
    note Vis_P' = this
    then show ?thesis
    proof (cases Q')
      case (Ret y)
      then show ?thesis
        by (metis PQ(1) PQ(3) Vis_P' choice_Ret_Vis choice_commutative extchoice_itree_def genchoice_Sils' le_supI2 retvals_Sils set_eq_subset)
    next
      case (Sil _)
      then show ?thesis
        using PQ(4) by auto
    next
      case (Vis G)
      with Vis_P' PQ show ?thesis
        by (auto simp add: choice_Sils choice_Sils')
           (meson Un_iff in_mono pran_excl_comb)
    qed
  qed
qed

lemma retvals_extchoice: "\<^bold>R(P \<box> Q) \<subseteq> \<^bold>R(P) \<union> \<^bold>R(Q)"
  by (metis Un_upper1 choice_commutative choice_diverge diverges_then_diverge le_supE retvals_diverge stabilises_retvals_extchoice sup_bot.right_neutral)

subsection \<open> Parallel Composition \<close>

text \<open> The following function combines two choice functions for parallel composition. \<close>

definition emerge :: "('a \<Zpfun> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<Zpfun> 'c) \<Rightarrow> ('a \<Zpfun> ('b, 'c) andor)" where
"emerge f A g = 
  map_pfun Both (A \<Zdres> pfuse f g) \<oplus> map_pfun Left ((A \<union> pdom(g)) \<Zndres> f) \<oplus> map_pfun Right ((A \<union> pdom(f)) \<Zndres> g)"

lemma emerge_alt_def:
  "emerge F E G =
     (\<lambda> e \<in> pdom(F) \<inter> pdom(G) \<inter> E \<bullet> Both(F(e), G(e)))
     \<oplus> (\<lambda> x \<in> pdom(F) - (E \<union> pdom(G)) \<bullet> Left(F x))
     \<oplus> (\<lambda> x \<in> pdom(G) - (E \<union> pdom(F)) \<bullet> Right(G x))"
proof -
  have 1: "map_pfun Both (E \<Zdres> pfuse F G) = (\<lambda> e \<in> pdom(F) \<inter> pdom(G) \<inter> E \<bullet> Both(F(e), G(e)))"
    by (auto intro!: pabs_cong simp add: map_pfun_as_pabs pfuse_def)
  have 2: "map_pfun Left ((E \<union> pdom(G)) \<Zndres> F) = (\<lambda> x \<in> pdom(F) - (E \<union> pdom(G)) \<bullet> Left(F x))"
    by (auto intro: pabs_cong simp add: map_pfun_as_pabs)
  have 3: "map_pfun Right ((E \<union> pdom(F)) \<Zndres> G) = (\<lambda> x \<in> pdom(G) - (E \<union> pdom(F)) \<bullet> Right(G x))"
    by (auto intro: pabs_cong simp add: map_pfun_as_pabs)
  show ?thesis
    by (simp only: emerge_def 1 2 3)
qed

lemma pdom_emerge_commute: "pdom (emerge f A g) = pdom (emerge g A f)"
  by (auto simp add: emerge_def)

text \<open> Remove merge function; it can be done otherwise. \<close>

abbreviation "par \<equiv> genpar emerge"

abbreviation "merge_Vis \<equiv> pmerge_Vis emerge"

lemma merge_Vis_both [simp]: "\<lbrakk> e \<in> E; e \<in> pdom F; e \<in> pdom G \<rbrakk> \<Longrightarrow> merge_Vis F E G(e)\<^sub>p = par (F(e)\<^sub>p) E (G(e)\<^sub>p)"
  by (simp add: pmerge_Vis_def emerge_def)

lemma merge_Vis_left [simp]: "\<lbrakk> e \<notin> E; e \<in> pdom F; e \<notin> pdom G \<rbrakk> \<Longrightarrow> merge_Vis F E G(e)\<^sub>p = par (F(e)\<^sub>p) E (Vis G)"
  by (simp add: pmerge_Vis_def emerge_def)

lemma merge_Vis_right [simp]: "\<lbrakk> e \<notin> E; e \<notin> pdom F; e \<in> pdom G \<rbrakk> \<Longrightarrow> merge_Vis F E G(e)\<^sub>p = par (Vis F) E (G(e)\<^sub>p)"
  by (simp add: pmerge_Vis_def emerge_def)

lemma par_commute: "par P E Q = (par Q E P) \<bind> (\<lambda> (a, b). Ret (b, a))"
  apply (coinduction arbitrary: P Q rule: itree_strong_coind)
     apply (auto elim!: is_RetE unstableE bind_RetE' bind_SilE' stableE simp add: genpar_Ret_iff)
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
    apply (smt (verit, ccfv_threshold) map_pfun_apply merge_Vis_both pdom.rep_eq pdom_emerge_commute pdom_map_pfun pdom_pmerge_Vis pfun_app.rep_eq)
   apply (metis (no_types, lifting) map_pfun_apply merge_Vis_left merge_Vis_right pdom.rep_eq pdom_emerge_commute pdom_map_pfun pdom_pmerge_Vis pfun_app.rep_eq)
  apply (metis (no_types, lifting) map_pfun_apply merge_Vis_left merge_Vis_right pdom.rep_eq pdom_emerge_commute pdom_map_pfun pdom_pmerge_Vis pfun_app.rep_eq)
  done  

consts 
  interleave :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<interleave>" 55)
  gparallel :: "'a \<Rightarrow> 'e set \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<parallel>\<^bsub>_\<^esub> _" [55, 0, 56] 56)

term parallel

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
  by (metis bind_diverge gpar_csp_def genpar_diverge)

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

definition Interleave :: "'i set \<Rightarrow> ('i \<Rightarrow> ('e, unit) itree) \<Rightarrow> ('e, unit) itree" where
"Interleave I P = Finite_Set.fold (\<interleave>) skip (P ` I)"

subsection \<open> Maximal Synchronous Parallel Composition \<close>

definition syncmerge :: "('a \<Zpfun> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<Zpfun> 'c) \<Rightarrow> ('a \<Zpfun> ('b, 'c) andor)" where
"syncmerge f A g = map_pfun Left ((pdom f \<inter> pdom g) \<Zndres> f) \<oplus> map_pfun Right ((pdom f \<inter> pdom g) \<Zndres> g) \<oplus> map_pfun Both (pfuse f g)"

lemma syncmerge_alt_def:
  "syncmerge F A G =
     ((\<lambda> x \<in> pdom(F) - pdom(G) \<bullet> Left(F x))
     \<oplus> (\<lambda> x \<in> pdom(G) - pdom(F) \<bullet> Right(G x))
     \<oplus> (\<lambda> e \<in> pdom(F) \<inter> pdom(G) \<bullet> Both(F(e), G(e))))"
proof -
  have 1: "map_pfun Left ((pdom F \<inter> pdom G) \<Zndres> F) = (\<lambda> x \<in> pdom(F) - pdom(G) \<bullet> Left(F x))"
    by (auto intro!: pabs_cong simp add: map_pfun_as_pabs pfuse_def)
  have 2: "map_pfun Right ((pdom F \<inter> pdom G) \<Zndres> G) = (\<lambda> x \<in> pdom(G) - pdom(F) \<bullet> Right(G x))"
    by (auto intro: pabs_cong simp add: map_pfun_as_pabs)
  have 3: "map_pfun Both (pfuse F G) = (\<lambda> x \<in> pdom(F) \<inter> pdom(G) \<bullet> Both (F(x), G(x)))"
    by (auto intro: pabs_cong simp add: map_pfun_as_pabs)
  show ?thesis
    by (simp only: syncmerge_def 1 2 3)
qed

subsection \<open> Hiding \<close>

text \<open> Could we prioritise events to keep determinism? \<close>

corec hide :: "('e, 'a) itree \<Rightarrow> 'e set \<Rightarrow> ('e, 'a) itree" (infixl "\<setminus>" 90) where
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

lemma is_Ret_loop [simp]: "is_Ret (loop F s) = False"
  by (metis bind_itree.disc_iff(1) comp_apply itree.disc(2) iterate.code)

lemma is_Ret_hide [simp]: "is_Ret (P \<setminus> A) = is_Ret P"
  by (auto simp add: hide.code deadlock_def itree.case_eq_if)

lemma is_Sil_hide [simp]: "is_Sil (hide P E) = (is_Sil P \<or> (is_Vis P \<and> card (E \<inter> pdom(un_Vis P)) = 1))"
  by (auto elim!: stableE simp add: hide.code deadlock_def itree.case_eq_if)

lemma is_Vis_hide [simp]: "is_Vis (hide P E) = (is_Vis P \<and> (card (E \<inter> pdom(un_Vis P)) \<noteq> 1 \<or> E \<inter> pdom(un_Vis P) = {}))"
  by (auto elim!: stableE simp add: hide.code itree.case_eq_if deadlock_def)

lemma hide_Sil [simp]: "(\<tau> P) \<setminus> A = \<tau> (P \<setminus> A)"
  by (metis (no_types, lifting) hide.code itree.simps(11))

lemma hide_sync: "(sync a \<bind> P) \<setminus> {build\<^bsub>a\<^esub> ()} = \<tau> (P ()) \<setminus> {build\<^bsub>a\<^esub> ()}"
  by (simp add: sync_def hide.code)

lemma hide_sync_loop_diverge: "hide (iter (sync a)) {build\<^bsub>a\<^esub> ()} = diverge"
  apply (coinduction rule:itree_coind, auto)
  apply (simp add: iterate.code, simp add: sync_def)
  apply (metis One_nat_def hide_sync is_Sil_hide itree.disc(5) iterate.code)
     apply (metis One_nat_def hide_sync is_Sil_hide itree.disc(5) itree.distinct_disc(6) iterate.code)
  apply (smt (verit) disjoint_iff empty_iff hide_sync insert_iff is_Vis_hide itree.disc(8) iterate.code)
  apply (smt (verit) Sil_Sil_drop comp_apply hide_Sil hide_sync itree.inject(2) iterate.code)
  apply (metis diverge.code itree.inject(2))
  done

lemma hide_empty: "hide P {} = P"
  apply (coinduction arbitrary: P rule: itree_coind)
     apply (auto)
      apply (simp add: hide.code)
     apply (simp add: hide.code)
    apply (simp add: hide.code)
   apply (simp add: hide.code)
  apply (auto simp add: itree.case_eq_if)
  apply (metis (no_types, lifting) hide.code itree.case_eq_if)
  oops

subsection \<open> Interruption \<close>

primcorec interrupt :: "('e, 'a) itree \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'a) itree" (infixl "\<triangle>" 59) where
"interrupt P Q =
   (case (P, Q) of
     (Sil P, _) \<Rightarrow> Sil (interrupt P Q) |
     (_, Sil Q) \<Rightarrow> Sil (interrupt P Q) |
     (Ret x, _) \<Rightarrow> Ret x |
     (_, Ret y) \<Rightarrow> Ret y |
     (Vis F, Vis G) \<Rightarrow> 
        Vis (map_pfun 
              (\<lambda>x. case x of 
                     Left P' \<Rightarrow> interrupt P' Q \<comment> \<open> Left side acts independently \<close>
                   | Right Q' \<Rightarrow> Q' \<comment> \<open> Right side acts independently \<close>)
              (emerge (pdom(G) \<Zndres> F) {} G)))"

lemma diverge_interrupt_left [simp]: "diverge \<triangle> P = diverge"
  by (coinduction arbitrary: P, auto, metis diverge.ctr itree.case(2))

lemma diverge_interrupt_right [simp]: "P \<triangle> diverge = diverge"
  by (coinduction arbitrary: P, auto simp add: itree.case_eq_if, meson itree.exhaust_disc)

lemma Sils_interrupt_left [simp]: "Sils n P \<triangle> Q = Sils n (P \<triangle> Q)"
  by (induct n, simp_all add: interrupt.code)

lemma Sil_interrupt_right_stable [simp]: "stable P \<Longrightarrow> P \<triangle> Sil Q = Sil (P \<triangle> Q)"
  by (cases P, simp_all, auto simp add: interrupt.code)

lemma Sils_interrupt_right_stable [simp]: "stable P \<Longrightarrow> P \<triangle> Sils n Q = Sils n (P \<triangle> Q)"
  by (induct n, auto)

lemma Sils_interrupt_right [simp]: "P \<triangle> Sils n Q = Sils n (P \<triangle> Q)"
proof (cases "stabilises P")
  case True
  then obtain m P' where P: "P = Sils m P'" "stable P'"
    by (metis stabilises_def)
  then have "Sils m P' \<triangle> Sils n Q = Sils (m + n) (P' \<triangle> Q)"
    by (simp)
  then show ?thesis
    by (simp add: P(1) add.commute)
next
  case False
  then show ?thesis
    by (metis Sils_diverge diverge_interrupt_left diverges_then_diverge)
qed

lemma deadlock_interrupt_stable: "stable P \<Longrightarrow> deadlock \<triangle> P = P"
  by (cases P, simp_all add: deadlock_def interrupt.code emerge_def pfun_eq_iff)

lemma deadlock_interrupt: "deadlock \<triangle> P = P"
proof (cases "stabilises P")
  case True
  then show ?thesis
    by (metis Sils_interrupt_right deadlock_interrupt_stable stabilises_def)
next
  case False
  then show ?thesis
    by (metis diverge_interrupt_right diverges_then_diverge)
qed

subsection \<open> Exception \<close>

primcorec exception :: "('e, 'a) itree \<Rightarrow> 'e set \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'a) itree" (infixl "\<lbrakk>_\<Zrres>" 65) where
"exception P A Q =
  (case P of
    Ret x  \<Rightarrow> Ret x |
    Sil P' \<Rightarrow> Sil (exception P' A Q) |
    Vis F  \<Rightarrow> 
      Vis (map_pfun 
              (\<lambda>x. case x of 
                     Left P' \<Rightarrow> exception P' A Q \<comment> \<open> Left side acts independently \<close>
                   | Right Q' \<Rightarrow> Q' \<comment> \<open> Right side acts independently \<close>)
              (emerge 
                \<comment> \<open> Non-exceptional behaviours from @{term P}\<close>
                (A \<Zndres> F)
                \<comment> \<open> No synchronisation\<close> 
                {} 
                \<comment> \<open> Exceptional behaviours: events in @{term A} enables by @{term P}, leading to @{term Q}\<close>
                (pfun_entries (A \<inter> pdom(F)) ((\<lambda> _. Q))))))"

subsection \<open> Renaming \<close>

primcorec rename :: "('e\<^sub>1 \<leftrightarrow> 'e\<^sub>2) \<Rightarrow> ('e\<^sub>1, 'a) itree \<Rightarrow> ('e\<^sub>2, 'a) itree" where
"rename \<rho> P = 
  (case P of
    Ret x \<Rightarrow> Ret x |
    Sil P \<Rightarrow> Sil (rename \<rho> P) |
    Vis F \<Rightarrow> Vis (map_pfun (rename \<rho>) (F \<circ>\<^sub>p graph_pfun ((pdom F \<lhd>\<^sub>r \<rho>)\<inverse>))))"

abbreviation rename':: "('e\<^sub>1, 'a) itree \<Rightarrow> ('e\<^sub>1 \<leftrightarrow> 'e\<^sub>2) \<Rightarrow> ('e\<^sub>2, 'a) itree" ("_\<lbrace>_\<rbrace>" 59) where
"rename' P \<rho> \<equiv> rename \<rho> P"

lemma rename_deadlock [simp]: "rename \<rho> deadlock = deadlock"
  by (simp add: deadlock_def rename.code)

subsection \<open> Restriction \<close>

text \<open> Restrict the events that an ITree can perform to a subset \<close>

primcorec evres :: "'e set \<Rightarrow> ('e, 's) itree \<Rightarrow> ('e, 's) itree" where
"evres E P = 
  (case P of
     Ret x \<Rightarrow> Ret x | Sil P' \<Rightarrow> Sil (evres E P') | Vis F \<Rightarrow> Vis (map_pfun (evres E) (E \<Zdres> F)))"

end