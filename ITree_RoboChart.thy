section \<open> RoboChart semantics \<close>

theory ITree_RoboChart
  imports "ITree_Extraction"
begin

subsection \<open> CSP operators \<close>
definition stop where "stop = deadlock"

definition par_hide where
"par_hide P s Q = (hide (P \<parallel>\<^bsub> s \<^esub> Q) s)"

text \<open> Events are hidden based on their order in a list. \<close>
definition prhide where
"prhide P es = foldl (\<lambda> Q e. hide Q {e}) P es"

text \<open> A process's state must be discarded before being in parallel composition. \<close>
definition discard_state where
"discard_state P = do {P ; skip}"

subsection \<open> RoboChart types \<close>
type_synonym core_bool = bool
type_synonym core_nat = natural
type_synonym core_int = integer
type_synonym core_real = integer
type_synonym core_string = String.literal

text \<open> A locale for reuse of RoboChart configurations (corresponding to instantiation.csp). 
This will be interpreted in each RoboChart theory.
We can also add common definitions here.
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

abbreviation "core_real_list \<equiv> 
  map (integer_of_int) [(int_of_integer min_real)..(int_of_integer max_real)]"

abbreviation "core_real_set \<equiv> set core_real_list"

end

subsection \<open> RoboChart CSP datatypes \<close>

datatype InOut = din | dout

definition "InOut_list = [din, dout]"
definition "InOut_set = set InOut_list"

(* enumtype Din = c1 | c2 *)

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

end