theory Incubator
  imports "Interaction_Trees.ITree_Simulation" "Interaction_Trees.ITree_Eval"
    "Z_Toolkit.Z_Toolkit" "../ITree_Machine" "HOL-Library.Code_Target_Int"
begin

lit_vars

unbundle Circus_Syntax

consts MAX_TEMP :: int
consts MIN_TEMP :: int

definition "TEMP = {MIN_TEMP..MAX_TEMP}"

def_const MAX_TEMP "30"
def_const MIN_TEMP "15"

schema IncubatorMonitor = 
  temp :: int
  where "MIN_TEMP \<le> temp" "temp \<le> MAX_TEMP"

record_default IncubatorMonitor

chantype chan = 
  increment :: unit
  decrement :: unit
  currentTemp :: int

(*
lemma Collect_set [code_unfold]: "{f x| x. x \<in> set xs} = set (map f xs)"
  by (auto)

lemma evcollect_set [code_unfold]: "\<lbrace>f t. t \<in> set xs\<rbrace> = set (map build\<^bsub>f\<^esub> xs)" 
  by (auto simp add: evcollect_def Collect_set)
*)

definition Increment :: "(chan, IncubatorMonitor) htree" where
"Increment = moperation increment (UNIV)\<^sub>e (\<lambda> _. (temp < MAX_TEMP)\<^sub>e) (\<lambda> _. (True)\<^sub>e) [temp \<leadsto> temp + 1]"

(* (temp < MAX_TEMP & increment?() \<rightarrow> temp := temp + 1) *)

definition Decrement :: "(chan, IncubatorMonitor) htree" where
"Decrement = moperation decrement (UNIV)\<^sub>e (\<lambda> _. (temp > MIN_TEMP)\<^sub>e) (\<lambda> _. (True)\<^sub>e) [temp \<leadsto> temp - 1]"

(*
definition Decrement :: "(chan, IncubatorMonitor) htree" where
"Decrement = (temp > MIN_TEMP & decrement?() \<rightarrow> temp := temp - 1)"
*)


(*
operation Decrement where
  guard ...
  update ...
  post ...
*)

definition GetTemp :: "(chan, IncubatorMonitor) htree" where
"GetTemp = moperation currentTemp (TEMP)\<^sub>e (\<lambda> t. (temp = t)\<^sub>e) (\<lambda> _. (True)\<^sub>e) [\<leadsto>]"


(*
definition GetTemp :: "(chan, IncubatorMonitor) htree" where
"GetTemp = currentTemp!(temp) \<rightarrow> Skip"
*)

(*
machine Incubator =
  init ...
  operations ...
*)


definition "Incubator = process [temp \<leadsto> 20] (loop (Increment \<box> Decrement \<box> GetTemp))"

code_datatype pfun_of_alist pfun_of_map

simulate Incubator


end
  