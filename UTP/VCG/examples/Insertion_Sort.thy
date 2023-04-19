section \<open> Insertion Sort \<close>

theory Insertion_Sort
  imports "ITree_VCG.ITree_VCG" "HOL-Library.Multiset"
begin  

subsection \<open> Verification Lemmas \<close>

lemma minus_Suc_same [simp]: "j - Suc 0 = j - Suc (Suc 0) \<longleftrightarrow> j \<le> 1"
  by force

lemma neq_minus_Suc_Suc [simp]: "i \<noteq> i - Suc n \<longleftrightarrow> i \<ge> 1"
  by linarith

lemma minus_Suc_Suc_neq [simp]: "i - Suc n \<noteq> i \<longleftrightarrow> i \<ge> 1"
  by linarith

lemma take_Suc_list_update: "i < length a \<Longrightarrow> (take (Suc i) a)[i \<leftarrow> v] = take i a @ [v]"
  using less_Suc_eq_0_disj by (induct a arbitrary: i v; fastforce)

lemma mem_set_take: "i < length a \<Longrightarrow> x \<in> set (take i a) \<longleftrightarrow> (\<exists> k<i. x = a!k)"
  by (metis (no_types, lifting) in_set_conv_nth leD length_take min_def nth_take)

lemma length_gr_implies_not_Nil [simp]: "k < length xs \<Longrightarrow> xs \<noteq> []"
  using gr_implies_not_zero by blast

declare nths_atLeastLessThan_0_take [simp]
declare nths_single [simp]

subsection \<open> State and Program \<close>

zstore state =
  arr :: "int list"
  i :: nat
  j :: nat

procedure insert_elem "xs :: int list" over state =
"j := i;
 while (0 < j \<and> arr!j < arr ! (j-1)) 
  invariant j \<le> i \<and> i < length arr \<and> sorted(nths arr {0..<j}) \<and> sorted(nths arr {j..i}) \<and> 
    (0<j \<and> j<i \<longrightarrow> arr ! (j-1) \<le> arr ! (j+1)) \<and> mset arr = mset xs
  variant j
  do
    (arr[j-1], arr[j]) := ($arr[j], $arr[j-1]);
    j := j - 1
  od"

procedure insertion_sort "xs :: int list" over state =
"arr := xs ; 
 i := 1 ;
 while (i < length arr) 
   invariant 0 < i \<and> sorted(nths arr {0..i-1}) \<and> mset arr = mset xs
 do 
    insert_elem xs; i := i + 1
 od"

execute "insertion_sort [66, 3, 25, 8, 1]"
execute "insertion_sort [100, 25, 66, 1, 2,50,89,5500,6,9,24,-7,3,13,5000,5050,70,54,24,99]"

subsection \<open> Verification \<close>

lemma insert_elem_correct:
  "H{i < length arr \<and> sorted(nths arr {0..<i}) \<and> mset arr = mset xs}
    insert_elem xs 
   {mset arr = mset xs \<and> sorted(nths arr {0..i})}"
proof vcg
  fix arr :: "\<int> list" and i :: "\<nat>"
  assume 
    "i < length arr" and
    "sorted (take i arr)" and
    "mset arr = mset xs" and
    "0 < i" and
    "arr ! i < arr ! (i - Suc 0)"
  thus "sorted (take (i - Suc 0) arr)" 
    by (auto simp add: sorted_iff_nth_Suc nths_atLeastAtMost_eq_drop_take take_update_swap drop_update_swap)
next
  fix arr :: "\<int> list" and i :: "\<nat>"
  assume 
    "i < length arr" and
    "sorted (take i arr)" and
    "mset arr = mset xs" and
    "0 < i" and
    "arr ! i < arr ! (i - Suc 0)"
  thus "sorted (nths (arr[i \<leftarrow> arr ! (i - Suc 0), i - Suc 0 \<leftarrow> arr ! i]) {i - Suc 0..i})"
    by (auto simp add: sorted_iff_nth_Suc nths_atLeastAtMost_eq_drop_take take_update_swap drop_update_swap)
next
  fix arr :: "\<int> list" and i :: "\<nat>"
  assume 
    "i < length arr" and
    "sorted (take i arr)" and
    "mset arr = mset xs" and
    "arr ! i < arr ! (i - Suc 0)" and
    "Suc 0 < i"
  thus "arr ! (i - Suc (Suc 0)) \<le> arr ! (i - Suc 0)"
    by (auto simp add: sorted_iff_nth_Suc nths_atLeastAtMost_eq_drop_take take_update_swap drop_update_swap)
       (metis Suc_diff_Suc Suc_lessD diff_Suc_less)
next
  fix arr :: "\<int> list" and i :: "\<nat>"
  assume 
    "i < length arr" and
    "sorted (take i arr)" and
    "mset arr = mset xs" and
    "0 < i" and
    "arr ! i < arr ! (i - Suc 0)"
  thus "mset (arr[i \<leftarrow> arr ! (i - Suc 0), i - Suc 0 \<leftarrow> arr ! i]) = mset xs"
    by (auto simp add: sorted_iff_nth_Suc nths_atLeastAtMost_eq_drop_take take_update_swap drop_update_swap)
       (metis less_imp_diff_less mset_swap)
next
  fix arr :: "\<int> list" and i :: "\<nat>" and j :: "\<nat>"
  assume 
    "j \<le> i" and
    "i < length arr" and
    "sorted (take j arr)" and
    "sorted (nths arr {j..i})" and
    "mset arr = mset xs" and
    "0 < j" and
    "arr ! j < arr ! (j - Suc 0)" and
    "arr ! (j - Suc 0) \<le> arr ! Suc j"
  show "sorted (take (j - Suc 0) arr)"
    by (meson \<open>sorted (take j arr)\<close> diff_le_self sorted_prefix take_prefix) 
next
  fix arr :: "\<int> list" and i :: "\<nat>" and j :: "\<nat>"
  assume 
    "j \<le> i" and
    "i < length arr" and
    "sorted (take j arr)" and
    "sorted (nths arr {j..i})" and
    "mset arr = mset xs" and
    "0 < j" and
    "arr ! j < arr ! (j - Suc 0)" and
    "arr ! (j - Suc 0) \<le> arr ! Suc j"
  thus "sorted (nths (arr[j \<leftarrow> arr ! (j - Suc 0), j - Suc 0 \<leftarrow> arr ! j]) {j - Suc 0..i})"
    by (auto simp add: sorted_iff_nth_Suc nths_atLeastAtMost_eq_drop_take take_update_swap drop_update_swap)
       (smt (verit, best) Nat.add_diff_assoc Suc_diff_diff Suc_leI Suc_pred add_gr_0 zero_less_diff)
next
  fix arr :: "\<int> list" and i :: "\<nat>" and j :: "\<nat>"
  assume 
    "j \<le> i" and
    "i < length arr" and
    "sorted (take j arr)" and
    "sorted (nths arr {j..i})" and
    "mset arr = mset xs" and
    "arr ! j < arr ! (j - Suc 0)" and
    "arr ! (j - Suc 0) \<le> arr ! Suc j" and
    "Suc 0 < j" and
    "j - Suc 0 < i"
  thus "arr ! (j - Suc (Suc 0)) \<le> arr ! (j - Suc 0)"
    by (auto simp add: sorted_iff_nth_Suc nths_atLeastAtMost_eq_drop_take take_update_swap drop_update_swap)
       (metis Suc_diff_Suc Suc_lessD diff_Suc_less)
next
  fix arr :: "\<int> list" and i :: "\<nat>" and j :: "\<nat>"
  assume 
    "j \<le> i" and
    "i < length arr" and
    "sorted (take j arr)" and
    "sorted (nths arr {j..i})" and
    "mset arr = mset xs" and
    "0 < j" and
    "arr ! j < arr ! (j - Suc 0)" and
    "arr ! (j - Suc 0) \<le> arr ! Suc j"
  show "mset (arr[j \<leftarrow> arr ! (j - Suc 0), j - Suc 0 \<leftarrow> arr ! j]) = mset xs"
    by (metis Suc_lessD Suc_pred \<open>0 < j\<close> \<open>i < length arr\<close> \<open>j \<le> i\<close> \<open>mset arr = mset xs\<close> mset_swap order_le_less_trans)
next
  fix arr :: "\<int> list" and i :: "\<nat>" and j :: "\<nat>"
  assume 
    "j \<le> i" and
    "i < length arr" and
    "sorted (take j arr)" and
    "sorted (nths arr {j..i})" and
    "mset arr = mset xs" and
    "\<not> arr ! j < arr ! (j - Suc 0)" and
    "\<not> sorted (nths arr {0..i})"
  thus "0 < j"
    by (metis gr0I)
next
  fix arr :: "\<int> list" and i :: "\<nat>" and j :: "\<nat>"
  assume 
    "j \<le> i" and
    "i < length arr" and
    "sorted (take j arr)" and
    "sorted (nths arr {j..i})" and
    "mset arr = mset xs" and
    "\<not> arr ! j < arr ! (j - Suc 0)" and
    "\<not> sorted (nths arr {0..i})"
  thus "j < i"
    by (auto simp add: sorted_iff_nth_Suc nths_atLeastAtMost_eq_drop_take take_update_swap drop_update_swap)
       (metis Suc_diff_Suc Suc_lessI cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel linorder_not_le nat_less_le)
next
  fix arr :: "\<int> list" and i :: "\<nat>" and j :: "\<nat>"
  assume 
    "j \<le> i" and
    "i < length arr" and
    "sorted (take j arr)" and
    "sorted (nths arr {j..i})" and
    "mset arr = mset xs" and
    "\<not> arr ! j < arr ! (j - Suc 0)" and
    "arr ! (j - Suc 0) \<le> arr ! Suc j"
  show "sorted (nths arr {0..i})"
    by (smt (verit) Nat.add_diff_assoc Nat.add_diff_assoc2 Nat.diff_diff_right One_nat_def \<open>\<not> arr ! j < arr ! (j - Suc 0)\<close> \<open>i < length arr\<close> \<open>j \<le> i\<close> \<open>sorted (nths arr {j..i})\<close> \<open>sorted (take j arr)\<close> add_le_cancel_left add_mono_thms_linordered_semiring(3) cancel_ab_semigroup_add_class.add_diff_cancel_left cancel_ab_semigroup_add_class.add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel diff_Suc_less diff_add_0 diff_less_mono dual_order.strict_trans2 le_add1 le_add_same_cancel1 le_diff_iff le_diff_iff' le_numeral_extra(3) less_SucI less_Suc_eq less_Suc_eq_0_disj less_diff_iff less_eq_Suc_le less_or_eq_imp_le linorder_le_less_linear nth_take nths_atLeastLessThan_0_take nths_upt_le_append_split nths_upt_le_nth nths_upt_length order_le_imp_less_or_eq plus_1_eq_Suc sorted_append_middle take_eq_Nil2 zero_less_one zero_less_one_class.zero_le_one)
qed

text \<open> Remove the definitional theorem for @{term insert_elem} and add the correctness proof as a lemma \<close>

declare insert_elem_def [prog_defs del]

declare hl_conseq[OF insert_elem_correct, hoare_lemmas]

lemma insertion_sort_correct: "H{True} insertion_sort xs {sorted arr}"
  apply vcg
  apply (metis Suc_pred nths_atLeastAtMost_0_take)
  apply (simp add: nths_atLeastAtMost_0_take)
  done  

end

