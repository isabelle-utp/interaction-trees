theory ITree_Interp
  imports ITrees "Optics.Optics"
begin

term map_pfun

term map_pfun

term loop

term isl

typ "'a + 'b"

term "(P :: ('a \<Rightarrow> ('e, 'a + 'b) itree)) \<circ> projl"

consts iter :: "('a \<Rightarrow> ('e, 'a + 'b) itree) \<Rightarrow> 'a \<Rightarrow> ('e, 'b) itree"

(*
definition iter :: "('a \<Rightarrow> ('e, 'a + 'b) itree) \<Rightarrow> 'a \<Rightarrow> ('e, 'b) itree"
  where "iter P s = iterate (\<lambda> s. \<not> isl s) (P \<circ> projl) (Inl s) \<bind> Ret \<circ> projr"
*)




(*
corec itree_st 
  :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> 'st \<Rightarrow> 'st) \<Rightarrow> ('e, 'st) itree \<Rightarrow> ('st \<Rightarrow> ('e, 'st) itree)" where
"itree_st c f P s =
  (case P of
    Sil P' \<Rightarrow> Sil (itree_st c f P' s) |
    Vis F  \<Rightarrow> )"
*)

(*
corec itree_interp 
  :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> 'st \<Rightarrow> ('e, 'a \<times> 'st) itree) \<Rightarrow> ('e, 't) itree \<Rightarrow> 'st \<Rightarrow> ('e, 't \<times> 'st) itree" where
"itree_interp c f P s = 
  (case P of
    Sil P' \<Rightarrow> Sil (itree_interp c f P' s))"
*)

definition "rmap f P = (P \<bind> Fun.comp Ret f)"

definition interp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 'a) itree \<Rightarrow> ('e, 'r) itree \<Rightarrow> ('e, 'r) itree" where
"interp c I P = 
  iter (\<lambda> Q::('e, 'r) itree. 
    (case Q of 
      Sil Q' \<Rightarrow> Ret (Inl Q') |
      Ret x \<Rightarrow> Ret (Inr x) |
      Vis F \<Rightarrow> rmap ((\<lambda> a. if (build\<^bsub>c\<^esub> a \<in> pdom(F)) 
                           then Inl (F (build\<^bsub>c\<^esub>a)\<^sub>p) 
                           else Inl deadlock) :: 'a \<Rightarrow> ('e, 'r) itree + 'r) I
    )) P"


end