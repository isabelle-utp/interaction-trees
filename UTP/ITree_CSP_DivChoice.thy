theory ITree_CSP_DivChoice
  imports ITree_CSP
begin           

text \<open> An alternative way of characterising external choice that avoids introducing non-determinism.
  Instead of ignoring choices where the event is present on both sides, we instead diverge
  after making that choice. This introduces more overhead, but has a simpler domain and is
  likely associative. \<close>

hide_const Map.dom

definition dcmerge :: "('e, 'r) chomerge" (infixr "\<otimes>" 100) where
"dcmerge F G = (\<lambda> x\<in>pdom F \<union> pdom G \<bullet> if x \<notin> pdom G then F(x)\<^sub>p else if x \<notin> pdom F then G(x)\<^sub>p else diverge)" 

lemma dcmerge_alt_def: "f \<otimes> g = (pdom(g) \<Zndres> f) \<oplus> (pdom(f) \<Zndres> g) \<oplus> (\<lambda> x\<in>pdom(f) \<inter> pdom(g) \<bullet> diverge)"
  by (auto simp add: dcmerge_def pfun_eq_iff)

lemma dcmerge_commute: "x \<otimes> y = y \<otimes> x"
  by (auto simp add: dcmerge_def pfun_eq_iff)

lemma dcmerge_empty [simp]: "x \<otimes> {}\<^sub>p = x" "{}\<^sub>p \<otimes> x = x"
  by (simp_all add: dcmerge_def pfun_eq_iff)

lemma dcmerge_update: 
  "f(x \<mapsto> v)\<^sub>p \<otimes> g = 
  (if (x \<notin> pdom(g)) then (f \<otimes> g)(x \<mapsto> v)\<^sub>p else (f \<otimes> g)(x \<mapsto> diverge)\<^sub>p)"
  by (auto simp add: dcmerge_def pfun_eq_iff)

lemma dcmerge_as_ovrd:
  assumes "pdom(f) \<inter> pdom(g) = {}"
  shows "f \<otimes> g = f \<oplus> g"
  using assms by (auto simp add: dcmerge_def pfun_eq_iff)

lemma dcmerge_pfun_of_map [code]:
  "dcmerge (pfun_of_map f) (pfun_of_map g) = 
     pfun_of_map (\<lambda> x. case (f x, g x) of
                       (Some _, Some _) \<Rightarrow> Some diverge |
                       (Some y, None) \<Rightarrow> Some y |
                       (None, Some y) \<Rightarrow> Some y |
                       (None, None) \<Rightarrow> None)"
  by (simp add: dcmerge_def pfun_eq_iff)
     (auto simp add: option.case_eq_if pdom_def pdom_res_def)


lemma dcmerge_lemma: 
  "fst ` set xs \<inter> fst ` set ys = set (filter (\<lambda>x. x \<in> set (map fst xs)) (map fst ys))"
  by auto

lemma excl_comb_pfun_of_alist [code]:
  "dcmerge (pfun_of_alist xs) (pfun_of_alist ys) =
    pfun_of_alist ( map (\<lambda> x. (x, diverge)) (filter (\<lambda>x. x \<in> set (map fst xs)) (map fst ys))
                  @ AList.restrict (- fst ` set xs) ys 
                  @ AList.restrict (- fst ` set ys) xs)"
  apply (simp add: dcmerge_alt_def pdom_res_alist plus_pfun_alist pabs_set)
  apply (simp only: dcmerge_lemma pabs_set plus_pfun_alist)
  apply simp
  done

(*
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
*)

end