section \<open> ITree Circus Examples \<close>

theory ITree_Circus_Examples
  imports "../ITree_Circus" "../ITree_Extraction" "../ITree_Eval" "../ITree_Simulation" 
begin

lit_vars

subsection \<open> Buffer \<close>

alphabet State = 
  buf :: "integer list"

record_default State

chantype Chan =
  Input :: integer
  Output :: integer
  State :: "integer list"

definition "buffer I
  = process
      ([buf \<leadsto> []] :: State \<Rightarrow> State)
      (loop ((Input?(i):I \<rightarrow> buf := (buf @ [i]))
            \<box> ((length(buf) > 0) & Output!(hd buf) \<rightarrow> (buf := (tl buf)))
            \<box> State!(buf) \<rightarrow> Skip))"

subsection \<open> Other Examples \<close>

definition "mytest = loop (Input?(i):(set [0,1,2]) \<rightarrow> (\<lambda> s. Ret (s @ [i])) \<box> Stop)"

definition "bitree = loop (\<lambda> s. inp_list Input [0,1,2,3] \<bind> outp Output)"

chantype schan = 
  a :: unit b :: unit c :: unit

definition "partest = 
  (\<lambda> s. hide
        (gpar_csp (loop (\<lambda> s. (do { outp a (); outp b (); Ret () })) s) {build\<^bsub>b\<^esub> ()} 
                  (loop (\<lambda> s. (do { outp b (); outp c (); Ret () })) s)) {build\<^bsub>b\<^esub> ()})" 

subsection \<open> Code Generation \<close>

simulate buffer

export_code mytest bitree buffer partest diverge deadlock in Haskell module_name ITree_Examples (string_classes)

end