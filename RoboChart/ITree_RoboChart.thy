section \<open> RoboChart semantics \<close>

theory ITree_RoboChart
  imports "Interaction_Trees.ITree_Extraction" "HOL-Library.Numeral_Type" 
          "ITree_UTP.ITree_CSP_Biased"
begin

unbundle Z_Relation_Syntax

subsection \<open> CSP operators \<close>

definition par_hide where
"par_hide P s Q = (hide (P \<parallel>\<^bsub> s \<^esub> Q) s)"

text \<open> Events are hidden based on their order in a list. \<close>
definition hidep (infixl "\<setminus>\<^sub>p" 90) where 
"hidep P es = foldl (\<lambda> Q e. hide Q {e}) P es"

definition par_hidep where
"par_hidep P s Q = (hidep (P \<parallel>\<^bsub> set s \<^esub> Q) s)"

text \<open> A process's state must be discarded before being in parallel composition. \<close>
definition discard_state where
"discard_state P = do {P ; skip}"

term "map_pfun"
term "rename a"

text \<open> Domain restriction of an associative list \<close>
definition rel_domres_l :: "'a set \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" (infixr "\<lhd>\<^sub>r\<^sub>l" 85) where
"rel_domres_l A al = [m. m \<leftarrow> al, fst m \<in> A]"

text \<open> Drop pairs @{text "(x,y)"} where @{text "y"} is in @{text "A"}. 

With this definition, we can give priority to the pair with a small index and remove remaining pairs 
with the same value in the image. 

For example, @{text "filter_out [(a1, b1), (a2, b2), (a3, b1)] = [(a1, b1), (a2, b2)]"}
where @{text "(a3, b1)"} is filtered out because @{text "b1"} is mapped to @{text "a1"} in the 
beginning of the list.
\<close>
primrec drop_dup :: "('a \<times> 'b) list \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) list" where 
"drop_dup [] A = []" |
"drop_dup (x#xs) A = 
  (if (snd x) \<in> A then (drop_dup xs A) 
 else (x # (drop_dup xs (A \<union> {snd x}))))"

value "drop_dup [(1, 2), (2, 3), (3, 2)] {}::(int \<times> int) list"

abbreviation "drop_dup' l \<equiv> drop_dup l {}"

text \<open> Another form of renaming whose renaming maps are an associative list. Priority, therefore, 
can be given to the pairs in the beginning of the list when renaming causes nondeterminism. 
\<close>
primcorec renamep :: "('e\<^sub>1 \<times> 'e\<^sub>2) list \<Rightarrow> ('e\<^sub>1, 'a) itree \<Rightarrow> ('e\<^sub>2, 'a) itree" where
"renamep \<rho> P = 
  (case P of
    Ret x \<Rightarrow> Ret x |
    Sil P \<Rightarrow> Sil (renamep \<rho> P) |
    Vis F \<Rightarrow> Vis (map_pfun (renamep \<rho>) (F \<circ>\<^sub>p graph_pfun ((set (drop_dup' (pdom F \<lhd>\<^sub>r\<^sub>l \<rho>)))\<inverse>))))"

abbreviation renamep':: "('e\<^sub>1, 'a) itree \<Rightarrow> ('e\<^sub>1 \<times> 'e\<^sub>2) list \<Rightarrow> ('e\<^sub>2, 'a) itree" ("_\<lbrace>_\<rbrace>\<^sub>p" 59) where
"renamep' P \<rho> \<equiv> renamep \<rho> P"

subsection \<open> RoboChart types \<close>
type_synonym core_bool = bool
type_synonym core_nat = natural
type_synonym core_int = integer
type_synonym core_real = integer
type_synonym core_string = String.literal

subsubsection \<open> Primitive types \<close>
datatype ('sm, 'a::finite) PrimType = PrimTypeC (un_prim:'a)

lemma distinct_PrimType: "distinct x \<longrightarrow> distinct (map PrimTypeC x)"
  by (simp add: distinct_conv_nth)

instantiation PrimType :: (type, enum) enum
begin

definition enum_PrimType :: "('a, 'b) PrimType list" where
"enum_PrimType = map PrimTypeC Enum.enum"

definition enum_all_PrimType :: "(('a, 'b) PrimType \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_PrimType P = (\<forall>b :: ('a, 'b) PrimType \<in> set enum_class.enum. P b)"

definition enum_ex_PrimType :: "(('a, 'b) PrimType \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_PrimType P = (\<exists>b :: ('a, 'b) PrimType \<in> set enum_class.enum. P b)"

instance
proof (intro_classes)
  show "distinct (enum_class.enum :: ('a, 'b) PrimType list)"
    apply (simp add: enum_PrimType_def)
    by (simp add: enum_distinct distinct_PrimType)

  show univ_eq: "(UNIV :: ('a, 'b) PrimType set) = set enum_class.enum"
    apply (auto simp add: enum_PrimType_def image_iff)
    apply (rule_tac x="un_prim x" in bexI, auto)
    apply (auto simp add: lists_eq_set enum_UNIV)
    done

  fix P :: "('a,'b) PrimType \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P"
    by(simp_all add: enum_all_PrimType_def enum_ex_PrimType_def univ_eq)
qed
end

subsection \<open> Locale \<close>
text \<open> A locale for reuse of RoboChart configurations (corresponding to instantiation.csp). 
This will be extended and interpreted in theories for each RoboChart model. 
We add common types and definitions here.
\<close>
locale robochart_confs = 
  fixes min_int::"integer" 
    and max_int::"integer"
    and max_nat::"natural"
    and min_real::"integer"
    and max_real::"integer"
begin 

abbreviation "core_int_list \<equiv> 
  map (integer_of_int) [(int_of_integer min_int)..(int_of_integer max_int)]"

abbreviation "core_int_set \<equiv> set core_int_list"

abbreviation "core_nat_list \<equiv> 
  map (natural_of_nat \<circ> nat) [(of_nat 0)..(of_nat (nat_of_natural max_nat))]"

abbreviation "core_nat_set \<equiv> set core_nat_list"

abbreviation "core_real_list \<equiv> 
  map (integer_of_int) [(int_of_integer min_real)..(int_of_integer max_real)]"

abbreviation "core_real_set \<equiv> set core_real_list"

definition Plus where
"Plus e1 e2 T = (if (e1+e2) \<in> T then (e1+e2) else e1)"

definition Minus where
"Minus e1 e2 T = (if (e1-e2) \<in> T then (e1-e2) else e1)"

definition Mult where
"Mult e1 e2 T = (if (e1*e2) \<in> T then (e1*e2) else e1)"

definition Div where
"Div e1 e2 T = (if (e1/e2) \<in> T then (e1/e2) else e1)"

definition Neg where
"Neg e1 T = (if (-e1) \<in> T then (-e1) else e1)"

definition Modulus where
"Modulus e1 e2 T = (if (e1 mod e2) \<in> T then (e1 mod e2) else e1)"

end

print_locale! robochart_confs

subsection \<open> RoboChart CSP datatypes \<close>

datatype InOut = din | dout

definition "InOut_list = [din, dout]"
definition "InOut_set = set InOut_list"

instantiation InOut :: enum
begin
definition enum_InOut :: "InOut list" where
"enum_InOut = InOut_list"

definition enum_all_InOut :: "(InOut \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_InOut P = (\<forall>b :: InOut \<in> set enum_class.enum. P b)"

definition enum_ex_InOut :: "(InOut \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_InOut P = (\<exists>b ::  InOut \<in> set enum_class.enum. P b)"

instance
proof (intro_classes)
  show "distinct (enum_class.enum :: InOut list)"
    by (simp add: enum_InOut_def InOut_list_def)

  show univ_eq: "UNIV = set (enum_class.enum:: InOut list)"
    apply (simp add: enum_InOut_def InOut_list_def)
    apply (auto simp add: enum_UNIV)
    by (meson InOut.exhaust)

  fix P :: "InOut \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P" 
    by (simp_all add: univ_eq enum_all_InOut_def enum_ex_InOut_def)
qed
end

subsection \<open> Channels and Events\<close>
text \<open> The @{text "mapfc"} and @{text "mapf"} together are used to enumerate events 
for a collection of channels. \<close>

definition mapfc :: "('c \<times> 'a \<Rightarrow> 'b) list \<Rightarrow> 'c list \<Rightarrow> ('a \<Rightarrow> 'b) list" where
"mapfc fs xs = concat (map (\<lambda> f. map f xs) (map curry fs))"

definition mapf  :: "('b \<Rightarrow> 'a) list \<Rightarrow> 'b list \<Rightarrow> 'a list" where
"mapf fs xs = concat (map (\<lambda> f. map f xs) (fs))"

text \<open> The @{text "enumchan1 ch a"} enumerates events for a channel @{text "ch"}, whose type is 
single (not tuple), based on the list of values @{text "a"}. 
The @{text "enumchans1 chs a"} supports enumerations of multiple channels.
Other definitions with suffix 2, 3, and 4 are similar, but for the channels whose types are pairs, 
triples, and quadruples.

We note such functions are not necessary in the future.
At this moment, we use these functions to explicitly enumerate events. We observe that 
the CSP-M syntax @{verbatim "{| c |}"} is simpler and more familiar. There is a better syntax 
(like @{text "\<lbrace> c v. v \<in> T_list \<rbrace>"}) introduced in the beginning of @{verbatim "ITree_CSP.thy"}. 
However, in order to make this syntax work, we need to instantiate the type of @{term v} for 
@{class enum} and @{class equal}. Otherwise, an error will be raised: @{verbatim 
"Type ... not of sort {enum,equal}"} when generating code. So this can be improved.
\<close>
abbreviation "enumchan1 ch a \<equiv> mapf [ch] a"
abbreviation "enumchan2 ch a b \<equiv> mapf (mapfc [ch] a) b"
abbreviation "enumchan3 ch a b c \<equiv> mapf (mapfc (mapfc [ch] a) b) c"
abbreviation "enumchan4 ch a b c d \<equiv> mapf (mapfc (mapfc (mapfc [ch] a) b) c) d"
abbreviation "enumchans1 chs a \<equiv> mapf chs a"
abbreviation "enumchans2 chs a b \<equiv> mapf (mapfc chs a) b"
abbreviation "enumchans3 chs a b c \<equiv> mapf (mapfc (mapfc chs a) b) c"
abbreviation "enumchans4 chs a b c d \<equiv> mapf (mapfc (mapfc (mapfc chs a) b) c) d"

subsubsection \<open> Renaming \<close>
text \<open> The @{text "mapfpc"} and @{text "mapfp"} together are used to construct pairs of 
all enumerate events for a collection of channels. These pairs represent renaming maps like 
[(e1.a.b.c, e1.a.b.c), ...].
 \<close>
definition mapfpc :: "('c \<times> 'a \<Rightarrow> 'b) list \<Rightarrow> 'c list \<Rightarrow> ('a \<Rightarrow> 'b \<times> 'b) list" where
"mapfpc fs xs = concat (map (\<lambda> f. map f xs) (map (curry \<circ> (\<lambda>f. \<lambda>x. (f x, f x))) fs))"

definition mapfp :: "('b \<Rightarrow> 'a) list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'a) list" where
"mapfp fs xs = concat (map (\<lambda> f. map f xs) (map (\<lambda>f. \<lambda>x. (f x, f x)) fs))"

text \<open> @{text "enumchanp1"} and @{text "enumchansp1"} are similar to @{text "enumchan1"} and 
@{text "enumchans1"}, but for pairs, of which the first and the second elements are the same. \<close>
abbreviation "enumchanp1 ch a \<equiv> mapfp [ch] a"
abbreviation "enumchanp2 ch a b \<equiv> mapf (mapfpc [ch] a) b"
abbreviation "enumchanp3 ch a b c \<equiv> mapf (mapfc (mapfpc [ch] a) b) c"
abbreviation "enumchanp4 ch a b c d \<equiv> mapf (mapfc (mapfc (mapfpc [ch] a) b) c) d"
abbreviation "enumchansp1 chs a \<equiv> mapfp chs a"
abbreviation "enumchansp2 chs a b \<equiv> mapf (mapfpc chs a) b"
abbreviation "enumchansp3 chs a b c \<equiv> mapf (mapfc (mapfpc chs a) b) c"
abbreviation "enumchansp4 chs a b c d \<equiv> mapf (mapfc (mapfc (mapfpc chs a) b) c) d"

text \<open> @{text "forget_first"} maps an event @{text "e_"} to another @{text "e"} by forgetting 
the first element (a transition id, @{text "tid"}) of @{text "e_"}. This is used for the event 
renaming like @{text "[(e1__stm0.tid.dir.n, e1_stm0.dir.n), ...]"}.
\<close>
definition forget_first where
"forget_first e_' e xs = (\<lambda>(dir). 
        (enumchan1 (\<lambda>tid. (e_' (tid, dir), e (dir))) xs))"

definition forget_first2 where
"forget_first2 e_' e xs = (\<lambda>(dir, n). 
        (enumchan1 (\<lambda>tid. (e_' (tid, dir, n), e (dir, n))) xs))"

text \<open> The @{text "mapfpc2"} and @{text "mapfp2"} together are used to construct pairs of 
all enumerate events for two channels. These pairs represent renaming maps like 
[(e1.a.b.c, e2.a.b.c), ...]. 
\<close>
definition mapfpc2 :: "(('d \<times> 'a \<Rightarrow> 'b) \<times> ('d \<times> 'a \<Rightarrow> 'c)) list \<Rightarrow> 'd list \<Rightarrow> ('a \<Rightarrow> 'b \<times> 'c) list" where
"mapfpc2 fs xs = concat (map (\<lambda> f. map f xs) (map (curry \<circ> (\<lambda>f. \<lambda>x. ((fst f) x, (snd f) x))) fs))"

definition mapfp2 :: "(('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'b)) list \<Rightarrow> 'c list \<Rightarrow> ('a \<times> 'b) list" where
"mapfp2 fs xs = concat (map (\<lambda> f. map f xs) (map (\<lambda>f. \<lambda>x. ((fst f) x, (snd f) x)) fs))"

text \<open> @{text "enumchanp2_1"} and @{text "enumchansp2_1"} are for pairs, of which the first and 
the second elements are different. 

Similarly, these functions are also not necessary in the future. A better syntax 
(@{text "\<lbrace>c1 (v1, v2) \<mapsto> c2 (v1, v2) | (v1, v2). v1 \<in> T1_list \<and> v2 \<in> T2_list \<rbrace>"}) is present. 
For the same reason, the type (@{term "T1 \<times> T2"}) of @{term c1} should be instantiated for 
@{class enum} and @{class equal}.
\<close>

abbreviation "enumchanp2_1 ch a \<equiv> mapfp2 [ch] a"
abbreviation "enumchanp2_2 ch a b \<equiv> mapf (mapfpc2 [ch] a) b"
abbreviation "enumchanp2_3 ch a b c \<equiv> mapf (mapfc (mapfpc2 [ch] a) b) c"
abbreviation "enumchanp2_4 ch a b c d \<equiv> mapf (mapfc (mapfc (mapfpc2 [ch] a) b) c) d"
abbreviation "enumchansp2_1 chs a \<equiv> mapfp2 chs a"
abbreviation "enumchansp2_2 chs a b \<equiv> mapf (mapfpc2 chs a) b"
abbreviation "enumchansp2_3 chs a b c \<equiv> mapf (mapfc (mapfpc2 chs a) b) c"
abbreviation "enumchansp2_4 chs a b c d \<equiv> mapf (mapfc (mapfc (mapfpc2 chs a) b) c) d"

subsection \<open> Memory \<close>
text \<open> The memory cell for a shared variable. \<close>
definition mem_of_svar :: "('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> ('b, 'a) itree" where
"mem_of_svar outc inlc insc iset = loop (\<lambda> s.
  (do {outp outc s; Ret (s)} \<box> 
   do {x \<leftarrow> inp_in inlc iset; Ret (x)} \<box>
   do {x \<leftarrow> inp_in insc iset; Ret (x)})
)"

text \<open> The memory cell for a local variable. \<close>
definition mem_of_lvar :: "('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> ('b, 'a) itree" where
"mem_of_lvar outc inc iset = loop (\<lambda> s.
  (do {outp outc s; Ret (s)} \<box> 
   do {x \<leftarrow> inp_in inc iset; Ret (x)})
)"

subsection \<open> Transition Identifiers \<close>

text \<open> A generic way to create a @{text "TrID"} type for transition identifiers. 
This type has two variables: @{text "'sm"} denoting a state machine and 
@{text "'tid"} for an enumerable type to denote transition ids. We note @{text "'sm"}
 is not used in the definition, and its purpose is to make this type instantiated 
for different state machines. One example to construct such type is 
@{text "typedef Movement = \"{()}\" by auto"}. One advantage of this generic type, when compared to 
enumerations by datatype, is the declaration of a new transition id type being easily parsed and 
resolved in Isabelle because a datatype with many enumerations (transition ids) makes Isabelle 
hard to resolve.
\<close>

typedef ('sm, 'tid::enum) TrID = "UNIV :: 'tid set"
  morphisms Rep_TrID mk_trid
  by auto

definition MkTrid :: "'sm itself \<Rightarrow> ('tid::enum) \<Rightarrow> ('sm, 'tid) TrID" where
"MkTrid sm tid = mk_trid tid"

instantiation TrID :: (type, enum) equal
begin

definition equal_TrID :: "('a, 'b) TrID \<Rightarrow> ('a, 'b) TrID \<Rightarrow> bool" where
"equal_TrID m1 m2 \<longleftrightarrow> (Rep_TrID m1 = Rep_TrID m2)"

instance by (intro_classes, auto simp add: equal_TrID_def, transfer, simp add: Rep_TrID_inject)
end

(*
instantiation TrID :: (type, enum) enum
begin

definition enum_TrID :: "('a, 'b) TrID list" where
"enum_TrID = map (MkTrid TYPE('a)  \<circ> (\<lambda>i. (Abs_bit0' i))) (upt 0 CARD('b))"

end
*)

end