section \<open> Verification of Numerical Algorithms \<close>

theory ITree_Numeric_VCG
  imports "Hybrid-Library.Vector_Syntax" "ITree_VCG.ITree_VCG" "HOL-Number_Theory.Number_Theory"
begin

declare UNIV_enum [code_unfold del]

text \<open> We need instance of default for rat and real to enable code generation \<close>

instantiation rat :: default
begin          
definition "default_rat = (0::rat)"
instance ..
end

instantiation real :: default
begin          
definition "default_real = (0::real)"
instance ..
end

text \<open> The following print translation makes real and rational fractions print using floating point
  notation. This is purely for printing purposes, and does not alter the term structure. We only
  pretty print terms that are ground fractions (i.e. numeral / numeral). \<close>

typed_print_translation \<open>
  let open Numeral; open Syntax
      fun float_term x = Syntax.const \<^syntax_const>\<open>_Float\<close> $ free (string_of_real x)

      (* We recognise a division, and then check what the numerator and denominator are *)
      fun float_tr' ctx [Const (@{const_syntax "numeral"}, _) $ m, Const (@{const_syntax "numeral"}, _) $ n]
            = float_term (real (dest_num_syntax m) / real (dest_num_syntax n)) |
          float_tr' ctx [Const (@{const_syntax "Groups.zero"}, _), _]
            = float_term (real 0) |
          float_tr' ctx [Const (@{const_syntax "Groups.one"}, _), Const (@{const_syntax "Groups.one"}, _)]
            = float_term (real 1) |
          float_tr' ctx [Const (@{const_syntax "Groups.one"}, _), Const (@{const_syntax "numeral"}, _) $ n]
            = float_term (real 1 / real (dest_num_syntax n))

      fun check_type_float_tr' ctx T ts = 
        if T = @{typ real} --> @{typ real} --> @{typ real} orelse T = @{typ rat} --> @{typ rat} --> @{typ rat}
        then float_tr' ctx ts
        else raise Match;

  in
  [(@{const_syntax "inverse_divide"}, check_type_float_tr')]
  end
\<close>

end