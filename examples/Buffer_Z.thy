section \<open> Buffer in Z \<close>

theory Buffer_Z
  imports "Interaction_Trees.ITree_Simulation" "Interaction_Trees.ITree_Machine"
    "Interaction_Trees.ITree_Eval" "HOL-Library.Code_Test"
begin lit_vars

consts VAL :: "integer set"

schema Buffer_state =
  buf :: "integer list"

record_default Buffer_state

zoperation Input =
  over Buffer_state
  params v \<in> VAL
  update "[buf \<leadsto> buf @ [v]]"

zoperation Output =
  over Buffer_state
  params v \<in> VAL
  pre "length buf > 0 \<and> v = hd buf"
  update "[buf \<leadsto> tl buf]"

zoperation State =
  over Buffer_state
  params st \<in> "{buf}"

zmachine Buffer =
  init "[buf \<leadsto> []]"
  operations Input Output State

def_consts VAL = "{0,1,2,3}"

ML \<open> open Export \<close>

simulate Buffer

end