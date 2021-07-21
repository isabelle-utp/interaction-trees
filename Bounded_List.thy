theory Bounded_List
  imports "HOL-Library.Numeral_Type"
begin

text \<open> The term @{term "CARD('n)"} retrieves the cardinality of a finite type @{typ 'n}. Examples
  include the types @{typ 1}, @{typ 2} and @{typ 3}.\<close>

typedef ('a, 'n::finite) blist = "{xs :: 'a list. length xs \<le> CARD('n)}"
  morphisms list_of_blist blist_of_list
  by (rule_tac x="[]" in exI, auto)

syntax "_blist" :: "type \<Rightarrow> type \<Rightarrow> type" ("_ [_]blist" [100, 0] 100)
translations (type) "'a ['n]blist" == (type) "('a, 'n) blist"

text \<open> We construct various functions using the lifting package to lift corresponding list functions. \<close>

setup_lifting type_definition_blist

lift_definition blength :: "'a['n::finite]blist \<Rightarrow> nat" is length .

lift_definition bappend :: "'a['m::finite]blist \<Rightarrow> 'a['n::finite]blist \<Rightarrow> 'a['m + 'n]blist" (infixr "@\<^sub>s" 65) is append
  by auto

lift_definition bmake :: "'n itself \<Rightarrow> 'a list \<Rightarrow> 'a['n::finite]blist" is "\<lambda> _. take CARD('n)"
  by auto

code_datatype bmake

thm "blist_of_list_inverse"
thm "list_of_blist"
lemma bmake_length_card:
  "blength (bmake TYPE('n::finite) xs) = (if length xs \<le> CARD('n) then length xs else CARD('n))"
  apply (simp add: blength_def bmake_def, auto)
  by (simp add: blist_of_list_inverse)+

lemma blist_always_bounded:
  "length (list_of_blist (bl::'a['n::finite]blist)) \<le> CARD('n)"
  using list_of_blist by blast

lemma blist_remove_head:
  fixes bl :: "'a['n::finite]blist"
  assumes "blength bl > 0"
  shows "blength (bmake TYPE('n::finite) (tl (list_of_blist (bl::'a['n::finite]blist)))) < blength bl"
  by (metis One_nat_def Suc_pred assms blength.rep_eq bmake_length_card length_tl less_Suc_eq_le linear)

text \<open> This proof is performed by transfer \<close>

lemma bappend_bmake [code]: 
  "bmake TYPE('a::finite) xs @\<^sub>s bmake TYPE('b::finite) ys 
    = bmake TYPE('a + 'b) (take CARD('a) xs @ take CARD('b) ys)"
  by (transfer, simp add: min.absorb2)

term "list_of_blist"
term "blist_of_list"

instantiation blist :: (type, finite) equal
begin

definition equal_blist :: "'a ['b]blist \<Rightarrow> 'a ['b]blist \<Rightarrow> bool" where
"equal_blist m1 m2 \<longleftrightarrow> (list_of_blist m1 = list_of_blist m2)"

instance by (intro_classes, auto simp add: equal_blist_def, transfer, auto)
end

lemma list_of_blist_code [code]:
  "list_of_blist (bmake TYPE('n::finite) xs) = take CARD('n) xs"
  by (transfer, simp)+

(*
fun bseq where
"bseq s 0 = {[]}" |
"bseq s (Suc 0) = {[q] | q. q \<in> s}" |
"bseq s (Suc n) = {q # qs | q qs. q \<in> s \<and> qs \<in> (bseq s n)}"

fun bseqn where
"bseqn s 0 = bseq s 0" |
"bseqn s (Suc n) = (bseqn s n) \<union> (bseq s (Suc n))"

instantiation blist :: (type, finite) enum
begin
definition enum_blist :: "('a ['b]blist) list" where
"enum_blist = lists {bmake TYPE('b) l | l. l \<in> bseqn {x::'a. True} CARD('b)}"

end
*)

end