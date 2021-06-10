section \<open> Fibonacci Circus Model \<close>

theory Fib
  imports "../ITree_Circus"
begin lit_vars

alphabet FibState = 
  x :: "nat"
  y :: "nat"

instantiation FibState_ext :: (default) default
begin
  definition default_FibState_ext :: "'a FibState_scheme" where
    "default_FibState_ext = FibState.extend 
      (FibState.make 0 0) default"

instance ..
end

chantype chan =
  out :: "nat"

definition Init :: "FibState subst" where
  "Init = [ x \<leadsto> 0, y \<leadsto> 0]"

definition 
  "InitFib = out!(1) \<rightarrow> out!(1) \<rightarrow> (x := 1 \<Zcomp> y := 1)"

definition
  "OutFib = out!(x+y) \<rightarrow> (\<langle>[ x \<leadsto> y, y \<leadsto> x+y]\<rangle>\<^sub>a)"

definition Fib :: "chan process" where 
"Fib = proc Init (InitFib \<Zcomp> loop (OutFib))"

export_code Fib in Haskell module_name Fib (string_classes)

end