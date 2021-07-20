section \<open> Matrix Syntax \<close>

theory Nat_Of
  imports "HOL-Library.Numeral_Type"
begin

text \<open> The following class allows us to link natural numbers and numeral indices. Essentially
  this shows an isomorphism between a numeral type and a finite range of naturals. \<close>

class nat = finite + numeral + zero +
  fixes nat_of :: "'a \<Rightarrow> nat"
  assumes nat_of: "nat_of ` UNIV = {0..<CARD('a)}"
  and nat_of_0 [simp]: "nat_of 0 = 0"
  and nat_of_1 [simp]: "CARD('a) > 1 \<Longrightarrow> nat_of 1 = 1"
  and nat_of_numeral: "nat_of (numeral n) = numeral n mod CARD('a)"
begin

abbreviation "of_nat' \<equiv> inv nat_of"

lemma nat_of_less_CARD [simp]: "nat_of x < CARD('a)"
  using nat_of by auto

lemma nat_of_range: "nat_of i \<in> {0..<CARD('a)}"
  using nat_of by auto

lemma inj_nat_of: "inj nat_of"
  using nat_of
  apply (rule_tac inj_onI)
  apply (auto)
  by (simp add: eq_card_imp_inj_on inj_eq)

lemma nat_of_inv [simp]: "of_nat' (nat_of x) = x"
  by (simp add: inj_nat_of)

lemma of_nat'_inv [simp]: "x < CARD('a) \<Longrightarrow> nat_of (of_nat' x) = x"
  by (simp add: f_inv_into_f local.nat_of)

lemma bij_nat_of: "bij_betw nat_of UNIV {0..<CARD('a)} "
  using bij_betw_def inj_nat_of local.nat_of by blast

lemma nat_of_numeral' [simp]: "numeral n < CARD('a) \<Longrightarrow> nat_of (numeral n) = numeral n"
  by (simp add: local.nat_of_numeral)

end

text \<open> Instances of the @{class nat} class for concrete numerals. \<close>

abbreviation "Abs_bit0n \<equiv> (\<lambda> x. Abs_bit0 (int x))"
abbreviation "Rep_bit0n \<equiv> (\<lambda> x. nat (Rep_bit0 x))"

abbreviation "Abs_bit1n \<equiv> (\<lambda> x. Abs_bit1 (int x))"
abbreviation "Rep_bit1n \<equiv> (\<lambda> x. nat (Rep_bit1 x))"

lemma Rep_bit1n:
  fixes x :: "'a::finite bit1"
  shows "Rep_bit1n x \<in> {0..<1 + 2 * CARD('a)}"
  by (auto, metis (full_types) bit1.Rep_0 bit1.Rep_less_n card_bit1 int_nat_eq nat_less_as_int)

interpretation bit0n_type:
  type_definition "Rep_bit0n :: 'a::finite bit0 \<Rightarrow> nat" Abs_bit0n "{0..<2 * CARD('a)}"
proof
  fix x :: "'a bit0"
  show "Rep_bit0n x \<in> {0::nat..<(2::nat) * CARD('a)}"
    by (auto, metis bit0.Rep_0 bit0.Rep_less_n card_bit0 int_nat_eq nat_less_as_int)
  show "Abs_bit0n (Rep_bit0n x) = x"
    using Rep_bit0 Rep_bit0_inverse by auto
  show "\<And>y::nat. y \<in> {0::nat..<(2::nat) * CARD('a)} \<Longrightarrow> Rep_bit0n (Abs_bit0n y :: 'a bit0) = y"
    by (auto simp add: bit0.Abs_inverse)
qed

interpretation bit1n_type:
  type_definition "Rep_bit1n :: 'a::finite bit1 \<Rightarrow> nat" Abs_bit1n "{0..<1 + 2 * CARD('a)}"
proof
  fix x :: "'a bit1"
  show "Rep_bit1n x \<in> {0::nat..<1 + (2::nat) * CARD('a)}"
    by (auto, metis (full_types) bit1.Rep_0 bit1.Rep_less_n card_bit1 int_nat_eq nat_less_as_int)
  show "Abs_bit1n (Rep_bit1n x) = x"
    using Rep_bit1 Rep_bit1_inverse by auto    
  show "\<And> y. y \<in> {0..<1 + 2 * CARD('a)} \<Longrightarrow> Rep_bit1n (Abs_bit1n y :: 'a bit1) = y"
    by (auto simp add: bit1.Abs_inverse)
qed

instantiation num1 :: nat
begin
definition "nat_of_num1 (x::num1) = (0::nat)"
instance
  by (intro_classes, simp_all add: nat_of_num1_def)
end

instantiation bit0 :: (finite) nat
begin
definition "nat_of_bit0 = Rep_bit0n"
instance
  by (intro_classes, simp_all add: nat_of_bit0_def bit0n_type.Rep_range bit0.Rep_0 bit0.Rep_1
     ,simp add: bit0.Rep_numeral nat_int_comparison(1) of_nat_mod)
end

instantiation bit1 :: (finite) nat
begin
definition "nat_of_bit1 = Rep_bit1n"
instance
  by (intro_classes, simp_all add: nat_of_bit1_def bit1n_type.Rep_range bit1.Rep_0 bit1.Rep_1
     ,metis bit1.Rep_numeral card_bit1 int_ops(3) nat_int of_nat_mod)
end

end
