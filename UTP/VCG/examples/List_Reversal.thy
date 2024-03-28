section \<open> List Reversal -- Different Approaches \<close>

theory List_Reversal
  imports "ITree_VCG.ITree_VCG"
begin 

zstore state = lvar +
  xs :: "int list"
  ys :: "int list"

program reverse0 "XS :: int list" over state =
"ys := []; 
 (var i::nat.
 i := 0;
 while i < length XS inv ys = rev (take i XS)
 do 
    ys := XS!i # ys; 
    i := i + 1 
 od)"

program reverse1 "XS :: int list" over state =
"ys := [];
 for x in XS inv j. ys = rev (take j XS) do ys := x # ys od"

program reverse2 "XS :: int list" over state =
"xs := XS; ys := [];
 while xs \<noteq> [] 
 inv ys = rev (take (length XS - length xs) XS) \<and> xs = drop (length XS - length xs) XS
 var length xs
 do 
    ys := hd xs # ys;
    xs := tl xs 
 od"

program reverse2a "XS :: int list" over state =
"xs := XS; ys := [];
 while xs \<noteq> [] 
 inv XS = rev ys @ xs var length xs
 do 
    ys := hd xs # ys;
    xs := tl xs 
 od"

program reverse2b "XS :: int list" over state =
"xs := XS; ys := [];
 while xs \<noteq> [] 
 inv length XS = length xs + length ys \<and> (\<forall> i < length ys. XS!i = ys ! (length ys - Suc i)) \<and> (\<forall> i\<in>{length ys..<length XS}. XS!i = xs ! (i - length ys))
 var length xs
 do 
    ys := hd xs # ys;
    xs := tl xs 
 od"

execute "reverse0 [1,2,3,4]"
execute "reverse1 [1,2,3,4]"
execute "reverse2 [1,2,3,4]"

lemma reverse0_correct: "H{True} reverse0 XS {ys = rev XS}"
  by (vcg, simp add: take_Suc_conv_app_nth)

lemma reverse1_correct: "H[True] reverse1 XS [ys = rev XS]"
  by (vcg, simp add: take_Suc_conv_app_nth)

lemma reverse2_correct: "H[True] reverse2 XS [ys = rev XS]"
proof vcg
  fix xs :: "\<int> list"
  assume 
    "xs = drop (length XS - length xs) XS" and
    "xs \<noteq> []"
  thus "hd xs # rev (take (length XS - length xs) XS) = rev (take (length XS - (length xs - Suc 0)) XS)"
    by (smt (verit, del_insts) Cons_nth_drop_Suc Suc_pred diff_le_self diff_less drop_all drop_rev hd_drop_conv_nth leD length_drop length_greater_0_conv length_rev not_less_eq rev_nth)
    
next
  fix xs :: "\<int> list"
  assume 
    "xs = drop (length XS - length xs) XS" and
    "xs \<noteq> []"
  thus "tl xs = drop (length XS - (length xs - Suc 0)) XS"
    by (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc_diff_eq_diff_pred Suc_diff_le diff_le_self diff_less drop_Nil length_drop length_greater_0_conv list.exhaust_sel list.inject)    
qed

lemma reverse2a_correct: "H[True] reverse2a XS [ys = rev XS]"
  by vcg

lemma reverse2b_correct: "H[True] reverse2b XS [ys = rev XS]"
  apply vcg
  apply (metis add_diff_cancel_right atLeastLessThan_iff diff_self_eq_0 hd_conv_nth le_add_diff_inverse2 length_greater_0_conv less_Suc_eq less_Suc_eq_le less_add_same_cancel2 nth_Cons_0 nth_Cons_pos plus_1_eq_Suc)
  apply (metis Suc_diff_Suc Suc_le_lessD list.exhaust_sel nth_Cons_Suc)
  apply (simp add: list_eq_iff_nth_eq) 
  apply (simp add: rev_nth)
  done

end