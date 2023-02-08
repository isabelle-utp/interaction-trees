section \<open>Rational types for code generation\<close>

theory Code_Rational
  imports "HOL.Real" "HOL-Library.Code_Target_Nat"
begin

subsection \<open>Type of target language rationals\<close>

typedef rational = "UNIV :: rat set"
  morphisms rat_of_rational rational_of_rat ..

setup_lifting type_definition_rational

lemma rational_eq_iff:
  "k = l \<longleftrightarrow> rat_of_rational k = rat_of_rational l"
  by transfer rule

lemma rational_eqI:
  "rat_of_rational k = rat_of_rational l \<Longrightarrow> k = l"
  using rational_eq_iff [of k l] by simp

lemma rat_of_rational_rational_of_rat [simp]:
  "rat_of_rational (rational_of_rat k) = k"
  by transfer rule

lemma rational_of_rat_rat_of_rational [simp]:
  "rational_of_rat (rat_of_rational k) = k"
  by transfer rule

instantiation rational :: ring_1
begin

lift_definition zero_rational :: rational
  is "0 :: rat"
  .

declare zero_rational.rep_eq [simp]

lift_definition one_rational :: rational
  is "1 :: rat"
  .

declare one_rational.rep_eq [simp]

lift_definition plus_rational :: "rational \<Rightarrow> rational \<Rightarrow> rational"
  is "plus :: rat \<Rightarrow> rat \<Rightarrow> rat"
  .

declare plus_rational.rep_eq [simp]

lift_definition uminus_rational :: "rational \<Rightarrow> rational"
  is "uminus :: rat \<Rightarrow> rat"
  .

declare uminus_rational.rep_eq [simp]

lift_definition minus_rational :: "rational \<Rightarrow> rational \<Rightarrow> rational"
  is "minus :: rat \<Rightarrow> rat \<Rightarrow> rat"
  .

declare minus_rational.rep_eq [simp]

lift_definition times_rational :: "rational \<Rightarrow> rational \<Rightarrow> rational"
  is "times :: rat \<Rightarrow> rat \<Rightarrow> rat"
  .

declare times_rational.rep_eq [simp]

instance proof
qed (transfer, simp add: algebra_simps)+

end

instance rational :: Rings.dvd ..

instantiation rational :: field
begin

lift_definition inverse_rational :: "rational \<Rightarrow> rational"
  is "inverse :: rat \<Rightarrow> rat" 
  .

lift_definition divide_rational :: "rational \<Rightarrow> rational \<Rightarrow> rational"
  is "divide :: rat \<Rightarrow> rat \<Rightarrow> rat" 
  .

declare inverse_rational.rep_eq [simp]

instance proof
qed (transfer, simp add: field_simps)+

end

instantiation rational :: "{linordered_idom, equal}"
begin

lift_definition abs_rational :: "rational \<Rightarrow> rational"
  is "abs :: rat \<Rightarrow> rat"
  .

declare abs_rational.rep_eq [simp]

lift_definition sgn_rational :: "rational \<Rightarrow> rational"
  is "sgn :: rat \<Rightarrow> rat"
  .

declare sgn_rational.rep_eq [simp]

lift_definition less_eq_rational :: "rational \<Rightarrow> rational \<Rightarrow> bool"
  is "less_eq :: rat \<Rightarrow> rat \<Rightarrow> bool"
  .

lemma rational_less_eq_iff:
  "k \<le> l \<longleftrightarrow> rat_of_rational k \<le> rat_of_rational l"
  by (fact less_eq_rational.rep_eq)

lift_definition less_rational :: "rational \<Rightarrow> rational \<Rightarrow> bool"
  is "less :: rat \<Rightarrow> rat \<Rightarrow> bool"
  .

lemma rational_less_iff:
  "k < l \<longleftrightarrow> rat_of_rational k < rat_of_rational l"
  by (fact less_rational.rep_eq)

lift_definition equal_rational :: "rational \<Rightarrow> rational \<Rightarrow> bool"
  is "HOL.equal :: rat \<Rightarrow> rat \<Rightarrow> bool"
  .

instance
  by standard (transfer, simp add: algebra_simps equal less_le_not_le [symmetric] mult_strict_right_mono linear)+

end

instance rational :: linordered_field ..

context
  includes lifting_syntax
  notes transfer_rule_numeral [transfer_rule]
begin

lemma [transfer_rule]:
  "(pcr_rational ===> pcr_rational ===> (\<longleftrightarrow>)) (dvd) (dvd)"
  by (unfold dvd_def) transfer_prover

lemma [transfer_rule]:
  "((\<longleftrightarrow>) ===> pcr_rational) of_bool of_bool"
  by (unfold of_bool_def) transfer_prover

lemma [transfer_rule]:
  "((=) ===> pcr_rational) numeral numeral"
  by transfer_prover

lemma [transfer_rule]:
  "((=) ===> (=) ===> pcr_rational) Num.sub Num.sub"
  by (unfold Num.sub_def) transfer_prover

lemma [transfer_rule]:
  "(pcr_rational ===> (=) ===> pcr_rational) (^) (^)"
  by (unfold power_def) transfer_prover

end

lemma "(numeral x :: rat) / numeral y = Frct(numeral x, numeral y)"
  using Frct_code_post(6) by force

context
includes integer.lifting
begin

lift_definition Frct_integer :: "integer \<times> integer \<Rightarrow> rational"
  is "Frct :: int \<times> int \<Rightarrow> rat" .

definition rational_of_integer :: "integer \<Rightarrow> rational" where
"rational_of_integer x = Frct_integer (x, 1)"

lemma numeral_rational_integer: "numeral n = rational_of_integer (numeral n)"
  unfolding rational_of_integer_def
  by (transfer, simp only: Frct_code_post(4)[THEN sym])

lemma divide_integer_rational:
  "rational_of_integer x / rational_of_integer y = Frct_integer (x, y)"
  unfolding rational_of_integer_def
  by (transfer, simp add: Fract_of_int_quotient)

lemma uminus_Frct_integer: "- Frct_integer (x, y) = Frct_integer (- x, y)"
  by (transfer, simp)

lemma rational_power: "(rational_of_integer x :: rational) ^ n = rational_of_integer (x ^ n)"
  unfolding rational_of_integer_def
  by (transfer, simp add: Fract_of_int_eq)

end

declare numeral_rational_integer [code_unfold]
declare divide_integer_rational [code_unfold]
declare rational_power [code_unfold]
declare uminus_Frct_integer [code_unfold]

code_printing code_module Rational \<rightharpoonup> (Haskell)
 \<open>module Rational(fract, numerator, denominator) where

  import qualified Data.Ratio
  import Data.Ratio(numerator, denominator)

  fract (a, b) = a Data.Ratio.% b\<close>

code_printing
  type_constructor rational \<rightharpoonup> (Haskell) "Prelude.Rational"
  | class_instance rational :: "HOL.equal" \<rightharpoonup> (Haskell) -
  | constant "0 :: rational" \<rightharpoonup> (Haskell) "(0::Rational)"
  | constant "1 :: rational" \<rightharpoonup> (Haskell) "(1::Rational)"
  | constant "Frct_integer" \<rightharpoonup> (Haskell) "Rational.fract (_)"
  | constant "HOL.equal :: rational \<Rightarrow> rational \<Rightarrow> bool" \<rightharpoonup>
    (Haskell) "(_) == (_)"
  |  constant "(<) :: rational \<Rightarrow> rational \<Rightarrow> bool" \<rightharpoonup>
    (Haskell) "_ < _"
  |  constant "(\<le>) :: rational \<Rightarrow> rational \<Rightarrow> bool" \<rightharpoonup>
    (Haskell) "_ <= _"
  | constant "(+) :: rational \<Rightarrow> rational \<Rightarrow> rational" \<rightharpoonup>
    (Haskell) "(_) + (_)"
  | constant "(-) :: rational \<Rightarrow> rational \<Rightarrow> rational" \<rightharpoonup>
    (Haskell) "(_) - (_)"
  | constant "(*) :: rational \<Rightarrow> rational \<Rightarrow> rational" \<rightharpoonup>
    (Haskell) "(_) * (_)"
  | constant "(/) :: rational \<Rightarrow> rational \<Rightarrow> rational" \<rightharpoonup>
    (Haskell) "(_) '/ (_)"
 | constant "uminus :: rational \<Rightarrow> rational" \<rightharpoonup>
    (Haskell) "Prelude.negate"

text \<open> We add a specific version of integer powers, so we can map these to the target function. \<close>

definition integer_power :: "'a::power \<Rightarrow> integer \<Rightarrow> 'a" where
"integer_power x y = x ^ (nat_of_integer y)"

lemma power_nat_of_integer [code_unfold]: "x ^ (nat_of_integer y) = integer_power x y"
  by (simp add: integer_power_def nat_of_integer_def)

code_printing
  constant "integer_power" \<rightharpoonup> (Haskell) "(_) ^ (_)"

definition numerator :: "rational \<Rightarrow> integer" where
"numerator x = integer_of_int (fst (quotient_of (rat_of_rational x)))"

definition denominator :: "rational \<Rightarrow> integer" where
"denominator x = integer_of_int (snd (quotient_of (rat_of_rational x)))"

code_printing
  constant numerator \<rightharpoonup> (Haskell) "numerator"
| constant denominator \<rightharpoonup> (Haskell) "denominator" 

end