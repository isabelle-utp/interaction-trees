theory Incubator
  imports "Interaction_Trees.ITree_Simulation" "Interaction_Trees.ITree_Eval"
    "Z_Toolkit.Z_Toolkit"
begin

unbundle Circus_Syntax

abbreviation "MAX_TEMP \<equiv> 30::integer"
abbreviation "MIN_TEMP \<equiv> 15::integer"

schema IncubatorMonitor = 
  temp :: integer
  where "MIN_TEMP \<le> temp" "temp \<le> MAX_TEMP"

record_default IncubatorMonitor

chantype chan = 
  increment :: unit
  decrement :: unit
  currentTemp :: integer

definition Increment :: "(chan, IncubatorMonitor) htree" where
"Increment = (temp < MAX_TEMP & increment?() \<rightarrow> temp := temp + 1)"

definition Decrement :: "(chan, IncubatorMonitor) htree" where
"Decrement = (temp > MIN_TEMP & decrement?() \<rightarrow> temp := temp - 1)"

definition GetTemp :: "(chan, IncubatorMonitor) htree" where
"GetTemp = currentTemp!(temp) \<rightarrow> Skip"

definition "Incubator = process [temp \<leadsto> 20] (loop (Increment \<box> Decrement \<box> GetTemp))"

code_datatype pfun_of_alist pfun_of_map

simulate Incubator


end
  