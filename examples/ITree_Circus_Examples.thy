section \<open> ITree Circus Examples \<close>

theory ITree_Circus_Examples
  imports "../ITree_Circus"
begin

lit_vars

subsection \<open> Buffer \<close>

alphabet State = 
  buf :: "integer list"

instantiation State_ext :: (default) default
begin
  definition default_State_ext :: "'a State_scheme" where
    "default_State_ext = State.extend (State.make []) default"

instance ..
end

chantype Chan =
  Input :: integer
  Output :: integer
  State :: "integer list"

definition "buffer 
  = proc 
      ([buf \<leadsto> []] :: State \<Rightarrow> State)
      (loop ((Input?(i):[0,1,2,3] \<rightarrow> buf := (buf @ [i]))
            \<box> ((length(buf) > 0) & Output!(hd buf) \<rightarrow> buf := (tl buf) \<Zcomp> State!(buf) \<rightarrow> Skip)
            \<box> State!(buf) \<rightarrow> Skip))"

subsection \<open> Other Examples \<close>

definition "mytest = loop (Input?(i) \<rightarrow> (\<lambda> s. Ret (s @ [i])) \<box> Stop)"

definition "bitree = loop (\<lambda> s. inp_list Input [0,1,2,3] \<bind> outp Output)"

chantype schan = 
  a :: unit b :: unit c :: unit

definition "partest = 
  (\<lambda> s. hide
        (gpar_csp (loop (\<lambda> s. (do { outp a (); outp b (); Ret () })) s) {build\<^bsub>b\<^esub> ()} 
                  (loop (\<lambda> s. (do { outp b (); outp c (); Ret () })) s)) {build\<^bsub>b\<^esub> ()})" 

subsection \<open> Code Generation \<close>
             
export_code mytest bitree buffer partest diverge deadlock in Haskell module_name ITree_Examples (string_classes)


end