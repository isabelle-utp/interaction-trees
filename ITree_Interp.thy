section \<open> Interpretation Combinators \<close>

theory ITree_Interp
  imports ITree_Iteration
begin

subsection \<open> Call-only Interpretation \<close>

corec interp_C :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 'b) itree) \<Rightarrow> ('e, 'r) itree \<Rightarrow> ('e, 'r) itree" where
"interp_C a P Q = 
  (case Q of 
    Ret x  \<Rightarrow> Ret x 
  | Sil Q' \<Rightarrow> Sil (interp_C a P Q') 
  | Vis F  \<Rightarrow> if pfun_singleton F \<and> pdom F \<subseteq> range build\<^bsub>a\<^esub>
              then let (e, Q') = dest_pfsingle F 
                   in \<tau> (interp_C a P (P (the (match\<^bsub>a\<^esub> e)) \<bind> (\<lambda> _. Q')))
              else Vis (map_pfun (interp_C a P) F))"

subsection \<open> Remote Procedure Calls \<close>

definition RPC :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('b \<Rightarrow> ('e, 'r) itree) \<Rightarrow> ('e, 'r) itree" where
"RPC a v b P = Vis {build\<^bsub>a\<^esub> v \<mapsto> Vis {b x \<Rightarrow> P x}\<^sub>p}" 

lemma RPC_pfun_alist [code_unfold]: 
  "RPC a v b P = Vis (pfun_of_alist [(build\<^bsub>a\<^esub> v, Vis {b x \<Rightarrow> P x}\<^sub>p)])"
  by (simp add: RPC_def pabs_insert_maplet)  

lemma is_Vis_RPC [simp]: "is_Vis (RPC a v b P)"
  by (simp add: RPC_def)

lemma RPC_val_eq: "wb_prism a \<Longrightarrow> RPC a v1 b P1 = RPC a v2 b P2 \<Longrightarrow> v1 = v2"
  by (metis RPC_def dest_pfsingle_maplet itree.simps(3) option.simps(1) prod.simps(1) wb_prism.match_build)

lemma RPC_cont_eq: "wb_prism b \<Longrightarrow> RPC a v b P1 = RPC a v b P2 \<Longrightarrow> P1 = P2"
  by (simp add: RPC_def pfun_eq_iff prism_fun_def prism_fun_upd_def fun_eq_iff)

(*
definition is_RPC :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 'r) itree \<Rightarrow> bool" where
"is_RPC a b P = (case P of
                   Vis F \<Rightarrow> (if pfun_singleton F
                             then (let (e, P') = dest_pfsingle F 
                                   in if matches\<^bsub>a\<^esub> e
                                      then case F e of 
                                             Vis F' \<Rightarrow> matches\<^bsub>b\<^esub> ` dom F' = {True} | 
                                             _ \<Rightarrow> False
                                      else False)
                             else False) | 
                   _ \<Rightarrow> False)"
*)

definition is_RPC :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 'r) itree \<Rightarrow> bool" where
"is_RPC a P = (case P of
                   Vis F \<Rightarrow> (if pfun_singleton F
                             then (let (e, P') = dest_pfsingle F 
                                   in matches\<^bsub>a\<^esub> e \<and> is_Vis P')
                             else False) | 
                   _ \<Rightarrow> False)"

lemma is_RPC_RPC [simp]: "wb_prism a \<Longrightarrow> is_RPC a (RPC a v b P)"
  by (auto simp add: RPC_def is_RPC_def prism_fun_def prism_fun_upd_def)

lemma not_RPC_deadlock [simp]: "\<not> is_RPC a deadlock"
  by (simp add: deadlock_def is_RPC_def pfun_singleton_dom)

lemma not_RPC_diverge [simp]: "\<not> is_RPC a diverge"
  by (simp add: is_RPC_def itree.case_eq_if)

lemma RPC_pdom_in_build: "\<lbrakk> wb_prism a; is_RPC a (Vis F) \<rbrakk> \<Longrightarrow> pdom F \<subseteq> range build\<^bsub>a\<^esub>"
  apply (cases "pfun_singleton F")
  apply (auto simp add: is_RPC_def)
  apply (metis dest_pfsingle_maplet domIff fst_conv pdom_upd pdom_zero pfun_singleton_def prism_matches_def singletonD wb_prism.range_build)
  done 

definition dest_RPC :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 'r) itree \<Rightarrow> ('a \<times> ('b \<Rightarrow> ('e, 'r) itree))" where
"dest_RPC a b P = (let F = un_Vis P; 
                      (e, P') = dest_pfsingle F;  
                      F' = un_Vis P' 
                      in (the (match\<^bsub>a\<^esub> e), \<lambda> v. F' (build\<^bsub>b\<^esub> v)))"

lemma dest_RPC_RPC [simp]: "\<lbrakk> wb_prism a; wb_prism b \<rbrakk> \<Longrightarrow> dest_RPC a b (RPC a v b P) = (v, P)"
  by (simp add: dest_RPC_def RPC_def)

lemma case_itree_RPC: "case_itree R S V (RPC a v b P) = (V (un_Vis (RPC a v b P)))"
  by (simp add: RPC_def)
          
subsection \<open> RPC Interpretation \<close>

corec interp_RPC :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 'b) itree) \<Rightarrow> ('e, 'r) itree \<Rightarrow> ('e, 'r) itree" where
"interp_RPC a b P Q = 
  (case Q of 
    Ret x  \<Rightarrow> Ret x 
  | Sil Q' \<Rightarrow> Sil (interp_RPC a b P Q') 
  | Vis F  \<Rightarrow> if is_RPC a (Vis F)
              then let (v, Q') = dest_RPC a b (Vis F)
                   in \<tau> (interp_RPC a b P (P v \<bind> Q'))
              else Vis (map_pfun (interp_RPC a b P) F))"

lemma interp_RPC_diverge: "interp_RPC a b P diverge = diverge"
  by (metis (no_types, lifting) Sil_fp_divergent diverge.sel interp_RPC.code is_Ret_diverge itree.case_eq_if unstable_diverge)

lemma interp_RPC_deadlock: "interp_RPC a b P deadlock = deadlock"
  by (simp add: deadlock_def interp_RPC.code)
     (metis deadlock_def not_RPC_deadlock)

(*
definition interp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 'b) itree) \<Rightarrow> ('e, 'r) itree \<Rightarrow> ('e, 'r) itree" where
"interp c d I P = 
  iter (\<lambda> Q::('e, 'r) itree. 
    (case Q of 
      Sil Q' \<Rightarrow> Ret (Inl Q') |
      Ret x \<Rightarrow> Ret (Inr x) |
      Vis F \<Rightarrow> if pfun_singleton F
               then (let (e, P') = dest_pfsingle F in 
                     case P' of 
                       Vis F' \<Rightarrow> )
               else diverge)) P"
*)

(*
map_itree ((\<lambda> a. if (build\<^bsub>c\<^esub> a \<in> pdom(F))
                           then Inl (F (build\<^bsub>c\<^esub>a)\<^sub>p) 
                           else Inl deadlock) :: 'a \<Rightarrow> ('e, 'r) itree + 'r) I
    )) P"
*)

subsection \<open> Control Interpretation \<close>

text \<open> Here, I is effectively pushing the buttons of P, by providing the events that P needs
  to continue. The loop (@{const iter}) steps through each constructor of @{term P}, returning
  the successor ITree at each step, or terminating if a return is encountered. If a visible event
  is encountered, the ITree @{term I} is executed to provide an event input for @{term P}. \<close>

definition interpO :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'r) itree \<Rightarrow> ('e, 'r) itree" where
"interpO c I P = 
  iter (\<lambda> Q::('e, 'r) itree. 
    (case Q of 
      Sil Q' \<Rightarrow> Ret (Inl Q') |
      Ret x \<Rightarrow> Ret (Inr x) |
      Vis F \<Rightarrow> map_itree ((\<lambda> a. if (build\<^bsub>c\<^esub> a \<in> pdom(F)) 
                           then Inl (F (build\<^bsub>c\<^esub>a)\<^sub>p) 
                           else Inl deadlock) :: 'a \<Rightarrow> ('e, 'r) itree + 'r) I
    )) P"

record ('e, 'r) interp =
  interp_evs :: "'e set"
  interp_fun :: "'r \<Rightarrow> ('e, 'e \<times> 'r) itree"

definition interp_st'
  :: "('e, 's) itree \<Rightarrow> ('e, 'r) interp \<Rightarrow> 'r \<Rightarrow> ('e, 's \<times> 'r) itree" where
"interp_st' P I s = 
  iter (\<lambda> (s\<^sub>0 :: 'r, Q :: (_, 's) itree). 
    (case Q of 
      Sil Q' \<Rightarrow> Ret (Inl (s\<^sub>0, Q')) |
      Ret x \<Rightarrow> Ret (Inr (x, s\<^sub>0)) |
      Vis F \<Rightarrow> if pdom F \<inter> interp_evs I = {}
               then Vis (\<lambda> e\<in>pdom(F) \<bullet> Ret (Inl (s\<^sub>0, F e)))
               else map_itree (\<lambda> (e::'e, s\<^sub>I::'r).
                           Inl (if (e \<in> pdom(F)) 
                                then (s\<^sub>I, F e) 
                                else (s\<^sub>I, deadlock))) (interp_fun I s\<^sub>0)
    )) (s, P)"

definition prism_interp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('r \<Rightarrow> ('e, 'a \<times> 'r) itree) \<Rightarrow> ('e, 'r) interp" where
"prism_interp c I = \<lparr> interp_evs = range build\<^bsub>c\<^esub>, 
                      interp_fun = \<lambda> s. map_itree (\<lambda> (a, s\<^sub>0). (build\<^bsub>c\<^esub> a, s\<^sub>0)) (I s) \<rparr>" 


definition interp_st
  :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 's) itree \<Rightarrow> ('r \<Rightarrow> ('e, 'a \<times> 'r) itree) \<Rightarrow> 'r \<Rightarrow> ('e, 's \<times> 'r) itree" where
"interp_st c P I s = 
  iter (\<lambda> (s\<^sub>0 :: 'r, Q :: (_, 's) itree). 
    (case Q of 
      Sil Q' \<Rightarrow> Ret (Inl (s\<^sub>0, Q')) |
      Ret x \<Rightarrow> Ret (Inr (x, s\<^sub>0)) |
      Vis F \<Rightarrow> if range build\<^bsub>c\<^esub> \<inter> pdom(F) = {}
               then Vis (\<lambda> e\<in>pdom(F) \<bullet> Ret (Inl (s\<^sub>0, F e)))
               else map_itree ((\<lambda> (a::'a, s\<^sub>I::'r).
                           Inl (if (build\<^bsub>c\<^esub> a \<in> pdom(F)) 
                                then (s\<^sub>I, F (build\<^bsub>c\<^esub>a)\<^sub>p) 
                                else (s\<^sub>I, deadlock)))) (I s\<^sub>0)
    )) (s, P)"


(*
definition interp_st 
  :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('st \<Rightarrow> ('e, 'r \<times> 'st) itree) \<Rightarrow> ('st \<Rightarrow> ('e, 'a \<times> 'st) itree) \<Rightarrow> ('st \<Rightarrow> ('e, 'r \<times> 'st) itree)" where
"interp_st c Ps I s = 
  iter (\<lambda> (s\<^sub>0 :: 'st , Q :: ('e, 'r \<times> 'st) itree). 
    (case Q of 
      Sil Q' \<Rightarrow> Ret (Inl (s\<^sub>0, Q')) |
      Ret x \<Rightarrow> Ret (Inr x) |
      Vis F \<Rightarrow> map_itree ((\<lambda> (a::'a, s\<^sub>I::'st). 
                           Inl (if (build\<^bsub>c\<^esub> a \<in> pdom(F)) 
                                then (s\<^sub>I, F (build\<^bsub>c\<^esub>a)\<^sub>p :: ('e, 'r \<times> 'st) itree) 
                                else (s\<^sub>I, deadlock)))) (I s\<^sub>0)
    )) (s, Ps s)"
*)

(*
chantype ch =
  a :: int
  ar :: int

code_datatype pfun_entries pfun_of_alist pfun_of_map

declare prism_fun_as_map [code_unfold]
declare prism_fun_def [code_unfold del]

value "interp_RPC a ar (\<lambda> n. if n = 0 \<or> n = 1 then Ret 1 else RPC a (n - 1) ar (\<lambda> r. Ret (n + r))) (RPC a 8 ar Ret)"

def_consts MAX_SIL_STEPS = 1000

execute "(\<lambda> x::unit. interp_RPC a ar (\<lambda> n. if n = 0 \<or> n = 1 then Ret 1 else RPC a (n - 1) ar (\<lambda> r. Ret (n + r))) (RPC a 8 ar Ret))"

lemma "interp_RPC a ar (\<lambda> n. Ret (n + 1)) (RPC a 5 ar Ret) = \<tau> (\<checkmark> 6)"
  apply (subst interp_RPC.code)
  apply (simp add: case_itree_RPC)
  apply (subst interp_RPC.code)
  apply (simp add: case_itree_RPC)
  done

chantype ch2 =
  cnt :: int
  b :: int
  br :: unit

definition pfx :: "'e \<Rightarrow> ('e, 's) itree \<Rightarrow>('e, 's) itree" where
"pfx e P = Vis {e \<mapsto> P}"


lemma "interp_C b (\<lambda> n. pfx (build\<^bsub>cnt\<^esub> n) (RPC b (n + 1) br (\<lambda> _. Ret ()))) (RPC b 0 br (\<lambda> _. Ret ())) = undefined"
  apply (subst interp_C.code)
  apply (simp add: case_itree_RPC)
  apply (subst interp.code)
  apply (simp add: case_itree_RPC pfx_def)
  apply (simp add: RPC_pdom_in_build)

  oops
*)

end