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

zoperation Increment =
  over IncubatorMonitor
  guard "temp < MAX_TEMP"
  update "[temp \<leadsto> temp + 1]"

zoperation Decrement =
  over IncubatorMonitor
  guard "temp > MIN_TEMP"
  update "[temp \<leadsto> temp - 1]"

zoperation GetTemp =
  over IncubatorMonitor
  params currentTemp \<in> TEMP
  post "temp = currentTemp"

zmachine Incubator =
  init "[temp \<leadsto> 20]"
  operations Increment Decrement GetTemp


code_datatype pfun_of_alist pfun_of_map


simulate Incubator


end
  