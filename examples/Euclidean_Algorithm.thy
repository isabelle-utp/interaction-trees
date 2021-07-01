theory Euclidean_Algorithm
  imports "../ITree_Extraction"
begin lit_vars

datatype (discs_sels) ('inp, 'outp) MethodOp = Call_C 'inp | Return_C 'outp

definition [lens_defs]: "Call = ctor_prism Call_C is_Call_C un_Call_C"
definition [lens_defs]: "Return = ctor_prism Return_C (Not \<circ> is_Call_C) un_Return_C"

lemma Call_wb_prism [simp, code_unfold]: "wb_prism Call" by (unfold_locales, auto simp add: lens_defs)
lemma Return_wb_prism [simp, code_unfold]: "wb_prism Return" by (unfold_locales, auto simp add: lens_defs)

alphabet gcd = 
  a :: integer
  b :: integer

record_default gcd

definition eucl :: "((integer \<times> integer, integer) MethodOp, gcd) htree" where
"eucl = Call?(A, B) \<rightarrow> (a, b) := (A, B) \<Zcomp> while a \<noteq> b do if a > b then a := a - b else b := b - a fi od \<Zcomp> Return!(a) \<rightarrow> Skip"

definition eucl_gcd where "eucl_gcd = proc [\<leadsto>] (eucl \<box> Stop)"

definition inp' :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e)\<Rightarrow> ('e, 'a) itree" where
"inp' c = Vis (pfun_of_map (\<lambda> e. case match\<^bsub>c\<^esub> e of Some v \<Rightarrow> Some (Ret v) | None \<Rightarrow> None))"

definition "input' c P = (\<lambda>s. inp' c \<bind> (\<lambda>x. P x s))"

lemma inp_in_coset [code_unfold]: 
  "wb_prism c \<Longrightarrow> inp_in c (List.coset []) = Vis (pfun_of_map (\<lambda> e. case match\<^bsub>c\<^esub> e of Some v \<Rightarrow> Some (Ret v) | None \<Rightarrow> None))"
  by (auto simp add: inp_in_def pabs_def pfun_entries_def pdom_res_def pfun_of_map_inject restrict_map_def fun_eq_iff domIff wb_prism.range_build)

lemma input_code_unfold [code_unfold]: 
  "wb_prism c \<Longrightarrow> input c P = input' c P"
  using inp_in_coset by (fastforce simp add: input_def input'_def inp_in_coset inp'_def)

lemma map_pfun_of_map [code]: "map_pfun f (pfun_of_map g) = pfun_of_map (\<lambda> x. map_option f (g x))"
  by (auto simp add: map_pfun_def pfun_of_map_inject fun_eq_iff)

lemma "map_prod (pfun_of_map f) (pfun_of_map g) = undefined"


text \<open> We need better code equations for @{const map_prod} for this to work\<close>

export_code eucl_gcd in Haskell module_name Euclidean_Algorithm (string_classes)

end