section \<open> RoboChart semantics \<close>

theory ITree_RoboChart
  imports "ITree_CSP" "Enum_Type" "Z_Toolkit.Relation_Toolkit"
begin

subsection \<open> CSP operators \<close>
definition par_hide where
"par_hide P s Q = (hide (P \<parallel>\<^bsub> s \<^esub> Q) s)"

definition prhide where
"prhide P es = foldl (\<lambda> Q e. hide Q {e}) P es"

definition discard_state where
"discard_state P = do {P ; skip}"

subsection \<open> RoboChart types \<close>
type_synonym core_int = integer

fun int2integer_list :: "int list \<Rightarrow> integer list" where
"int2integer_list Nil = Nil" |
"int2integer_list (Cons x xs) 
  = Cons (integer_of_int x) (int2integer_list xs)"

definition int_to_integer_list :: "int list \<Rightarrow> integer list" where
"int_to_integer_list = map (integer_of_int)"

lemma "int2integer_list xs = int_to_integer_list xs"
  apply (simp add: int_to_integer_list_def)
  apply (induction xs)
  apply simp
  by simp

subsection \<open> RoboChart CSP datatypes \<close>

datatype InOut = din | dout

definition "InOut_list = [din, dout]"
definition "InOut_set = set InOut_list"

(* enumtype Din = c1 | c2 *)

subsection \<open> Memory \<close>
definition mem_of_svar :: "('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> ('b, 'a) itree" where
"mem_of_svar outc inlc insc iset = loop (\<lambda> s.
  (do {outp outc s; Ret (s)} \<box> 
   do {x \<leftarrow> inp_in inlc iset; Ret (x)} \<box>
   do {x \<leftarrow> inp_in insc iset; Ret (x)})
)"

definition mem_of_lvar :: "('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> ('b, 'a) itree" where
"mem_of_lvar outc inc iset = loop (\<lambda> s.
  (do {outp outc s; Ret (s)} \<box> 
   do {x \<leftarrow> inp_in inc iset; Ret (x)})
)"

definition cmem_of_var :: "('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> ('b, 'a) itree" where
"cmem_of_var inlc insc iset = loop (\<lambda> s.
  ( do {x \<leftarrow> inp_in inlc iset; Ret (x)} \<box>
   do {x \<leftarrow> inp_in insc iset; Ret (x)})
)"

ML \<open> 
($$ "h") (Symbol.explode "hello");
val hw = Scan.one (fn x => x = "h" orelse x = "o");
hw (Symbol.explode "hello");
hw (Symbol.explode "ollo");
\<close>

term "map_pfun"
term "fun_pfun"
term "F \<circ>\<^sub>p Q"
term "(F \<circ>\<^sub>p fun_pfun \<rho>)"
term "R\<^sup>\<sim>"
(*
R = a \<rightarrow> P(a) [] b \<rightarrow> Q(b)    {(a, P), (b, Q)}

R [[a <- c, b <- d]]
= [(a, c), (b, d)]

Case 1:
  [(a, c), (a, d)]
    -- introduce external choice (c \<rightarrow> P [] d \<rightarrow> P) [] b \<rightarrow> Q
  What about if there is a (d \<rightarrow> PP) in the original process R? 
  Partial function is not a right representation.
Case 2: 
    [(a, c), (b, c)]
    -- (c \<rightarrow> R(P(a)) [] c \<rightarrow> R(Q(b)))
*)
(*
primcorec rename :: "('e\<^sub>1 \<leftrightarrow> 'e\<^sub>2) \<Rightarrow> ('e\<^sub>1, 'a) itree \<Rightarrow> ('e\<^sub>2, 'a) itree" where
"rename R P = 
  (case P of
    Ret x \<Rightarrow> Ret x |
    Sil P \<Rightarrow> Sil (rename \<rho> P) |
    Vis F \<Rightarrow> Vis (map_pfun (rename \<rho>) (F \<circ>\<^sub>p fun_pfun (R\<sim>))))"
*)
end