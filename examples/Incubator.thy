theory Incubator
  imports "Interaction_Trees.ITree_Simulation" "Interaction_Trees.ITree_Eval"
    "Z_Toolkit.Z_Toolkit" "../ITree_Machine" "HOL-Library.Code_Target_Int"
begin

lit_vars

unbundle Circus_Syntax

consts MAX_TEMP :: int
consts MIN_TEMP :: int

definition "TEMP = {MIN_TEMP..MAX_TEMP}"

def_consts 
  MAX_TEMP = 30
  MIN_TEMP = 15

schema IncubatorMonitor = 
  temp :: int
  where "MIN_TEMP \<le> temp" "temp \<le> MAX_TEMP"

record_default IncubatorMonitor

zmachine Incubator =
  over IncubatorMonitor
  init "[temp \<leadsto> 20]"
  operations

    Increment =
      guard "temp < MAX_TEMP"
      update "[temp \<leadsto> temp + 1]"

    Decrement =
      guard "temp > MIN_TEMP"
      update "[temp \<leadsto> temp - 1]"

    GetTemp =
      params currentTemp \<in> TEMP
      post "temp = currentTemp"

(*
chantype chan = 
  increment :: unit
  decrement :: unit
  currentTemp :: int

definition Increment :: "(chan, IncubatorMonitor) htree" where
"Increment = moperation increment UNIV (\<lambda> _. (temp < MAX_TEMP)\<^sub>e) (\<lambda> _. (True)\<^sub>e) (\<lambda> _. [temp \<leadsto> temp + 1])"

(* (temp < MAX_TEMP & increment?() \<rightarrow> temp := temp + 1) *)

definition Decrement :: "(chan, IncubatorMonitor) htree" where
"Decrement = moperation decrement UNIV (\<lambda> _. (temp > MIN_TEMP)\<^sub>e) (\<lambda> _. (True)\<^sub>e) (\<lambda> _. [temp \<leadsto> temp - 1])"

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
"GetTemp = moperation currentTemp TEMP (\<lambda> t. (temp = t)\<^sub>e) (\<lambda> _. (True)\<^sub>e) (\<lambda> _. [\<leadsto>])"

(*
definition GetTemp :: "(chan, IncubatorMonitor) htree" where
"GetTemp = currentTemp!(temp) \<rightarrow> Skip"
*)



definition "Incubator = process [temp \<leadsto> 20] (loop (Increment \<box> Decrement \<box> GetTemp))"
*)

code_datatype pfun_of_alist pfun_of_map


simulate Incubator


end
  