theory ITree_Interp
  imports ITrees "Optics.Optics"
begin

definition iter :: "('a \<Rightarrow> ('e, 'a + 'b) itree) \<Rightarrow> 'a \<Rightarrow> ('e, 'b) itree"
  where "iter P s = iterate (\<lambda> s. \<not> isl s) (P \<circ> projl) (Inl s) \<bind> Ret \<circ> projr"

text \<open> Here, I is effectively pushing the buttons of P, by providing the events that P needs
  to continue. \<close>

definition interp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'r) itree \<Rightarrow> ('e, 'r) itree" where
"interp c I P = 
  iter (\<lambda> Q::('e, 'r) itree. 
    (case Q of 
      Sil Q' \<Rightarrow> Ret (Inl Q') |
      Ret x \<Rightarrow> Ret (Inr x) |
      Vis F \<Rightarrow> map_itree ((\<lambda> a. if (build\<^bsub>c\<^esub> a \<in> pdom(F)) 
                           then Inl (F (build\<^bsub>c\<^esub>a)\<^sub>p) 
                           else Inl deadlock) :: 'a \<Rightarrow> ('e, 'r) itree + 'r) I
    )) P"

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

end