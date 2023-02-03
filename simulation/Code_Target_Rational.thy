theory Code_Target_Rational
  imports Code_Rational "HOL-Library.Code_Target_Int" 
begin

code_datatype rat_of_rational

declare [[code drop: rational_of_rat]]

lemma numeral_rat_of_rational [code_unfold]: 
  "(numeral x :: rat) = rat_of_rational (numeral x)"
  by (transfer, simp)

lemma rat_of_int_int_of_integer [code_unfold]: 
  "Rat.of_int (int_of_integer x) = rat_of_rational (rational_of_integer x)"
  unfolding rational_of_integer_def
  by (simp add: Frct_integer.rep_eq Rat.of_int_def of_int_rat)

lemma plus_rat_of_rational [code]:
  "(rat_of_rational x) + (rat_of_rational y) = rat_of_rational (x + y)"
  by (transfer, simp)

lemma uminus_rat_of_rational [code]:
  "- (rat_of_rational x) = rat_of_rational (- x)"
  by (transfer, simp)

lemma minus_rat_of_rational [code]:
  "(rat_of_rational x) - (rat_of_rational y) = rat_of_rational (x - y)"
  by (transfer, simp)

lemma times_rat_of_rational [code]:
  "(rat_of_rational x) * (rat_of_rational y) = rat_of_rational (x * y)"
  by (transfer, simp)

lemma divide_rat_of_rational [code]:
  "(rat_of_rational x) / (rat_of_rational y) = rat_of_rational (x / y)"
  by (transfer, simp)

lemma [code]: "0 = rat_of_rational 0"
  by simp

lemma [code]: "1 = rat_of_rational 1"
  by simp

lemma rat_of_rational_power: "rat_of_rational x ^ n = rat_of_rational (x ^ n)"
  by (induct n, simp_all)

lemma [code_unfold]: "power (rat_of_rational x) (nat_of_integer y) 
       = rat_of_rational (integer_power x y)"
  by (simp add: integer_power_def rat_of_rational_power)

(*
definition vel :: "real \<Rightarrow> real" where
"vel t = 10 * t^2 + 8"

definition "myrat = (7.896 :: rat)"

export_code myrat vel in Haskell
*)

end