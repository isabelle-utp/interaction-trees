section \<open> Buffer in Circus \<close>

theory Buffer_Circus
  imports "ITree_UTP.ITree_Circus" "ITree_Simulation.ITree_Simulation" 
begin

lit_vars

subsection \<open> Buffer \<close>

zstore State = 
  buf :: "integer list"

chantype Chan =
  Input :: integer
  Output :: integer
  State :: "integer list"

setup \<open> Show_Channel.mk_chan_show_inst "Chan" ["Input", "Output", "State"] \<close>

consts INP :: "integer list"

definition "buffer
  = anim_process
      ([buf \<leadsto> []] :: State \<Rightarrow> State)
      (loop ((Input?(i):set INP \<rightarrow> buf := (buf @ [i]))
            \<box> ((length(buf) > 0) & Output!(hd buf) \<rightarrow> (buf := (tl buf)))
            \<box> State!(buf) \<rightarrow> Skip))"

(*
definition "buffer I
  = evres (\<lbrace>Input i. i \<in> set I\<rbrace> \<union> \<lbrace>Output i. i \<in> set I\<rbrace> \<union> \<lbrace>State xs. xs \<in> {[],[0],[0,0]}\<rbrace>) (process
      ([buf \<leadsto> []] :: State \<Rightarrow> State)
      (loop ((Input?(i) \<rightarrow> buf := (buf @ [i]))
            \<box> ((length(buf) > 0) & Output!(hd buf) \<rightarrow> (buf := (tl buf)))
            \<box> State!(buf) \<rightarrow> Skip)))"
*)

subsection \<open> Code Generation \<close>

def_consts INP = "[0,1,2,3]"

animate buffer

end