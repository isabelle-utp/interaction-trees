section \<open> Dwarf Signal \<close>

theory DwarfSignal
  imports "../ITree_Circus"
begin lit_vars

datatype LampId = L1 | L2 | L3

type_synonym Signal = "LampId set"

datatype ProperState = dark | stop | warning | drive

definition "ProperState = {dark, stop, warning, drive}"

fun signalLamps :: "ProperState \<Rightarrow> LampId set" where
"signalLamps dark = {}" |
"signalLamps stop = {L1, L2}" |
"signalLamps warning = {L1, L3}" |
"signalLamps drive = {L2, L3}"

text \<open> Could we have separate processes for the actual lamp and its controller? We would then
  try to verify that the controller preserves the lamp-based safety properties. The current
  set up doesn't preserve them. \<close>

alphabet Dwarf = 
  last_proper_state :: "ProperState"
  turn_off :: "LampId set"
  turn_on  :: "LampId set"
  last_state :: "Signal"
  current_state :: "Signal"
  desired_proper_state :: "ProperState"

definition Dwarf_inv :: "Dwarf \<Rightarrow> bool" where
  "Dwarf_inv = 
  ((current_state - turn_off) \<union> turn_on = signalLamps desired_proper_state
  \<and> turn_on \<inter> turn_off = {})\<^sub>e"

instantiation Dwarf_ext :: (default) default
begin
  definition default_Dwarf_ext :: "'a Dwarf_scheme" where
    "default_Dwarf_ext = Dwarf.extend (Dwarf.make dark {} {} (signalLamps stop) (signalLamps stop) stop) default"

instance ..
end

chantype chan =
  shine :: "LampId set"
  setNewProperState :: ProperState
  turnOff :: "LampId"
  turnOn :: "LampId"

definition Init :: "Dwarf subst" where
  "Init = 
  [ last_proper_state \<leadsto> stop
  , turn_off \<leadsto> {}
  , turn_on \<leadsto> {}
  , last_state \<leadsto> signalLamps stop
  , current_state \<leadsto> signalLamps stop
  , desired_proper_state \<leadsto> stop ]"

lemma Init_establishes_inv: "Init \<dagger> Dwarf_inv = (True)\<^sub>e"
  by (simp add: Dwarf_inv_def Init_def usubst_eval)

definition 
  "SetNewProperState = 
    \<questiondown>current_state = signalLamps desired_proper_state? \<Zcomp> 
    setNewProperState?(st):(ProperState - {desired_proper_state}) \<rightarrow> 
      (last_proper_state := desired_proper_state \<Zcomp>
       turn_off := (current_state - signalLamps st) \<Zcomp>
       turn_on := (signalLamps st - current_state) \<Zcomp>
       last_state := current_state \<Zcomp>
       desired_proper_state := st)"

definition
  "TurnOff =
   turnOff?(l):turn_off \<rightarrow> 
    (turn_off := (turn_off - {l}) \<Zcomp>
     turn_on := (turn_on - {l}) \<Zcomp>
     last_state := current_state \<Zcomp>
     current_state := (current_state - {l}))"

definition
  "TurnOn =
   turnOn?(l):turn_on \<rightarrow> 
    (turn_off := (turn_off - {l}) \<Zcomp>
     turn_on := (turn_on - {l}) \<Zcomp>
     last_state := current_state \<Zcomp>
     current_state := (current_state \<union> {l}))"

definition "Shine = shine!(current_state) \<rightarrow> Skip"

definition "Dwarf
  = proc Init (loop (SetNewProperState \<box> TurnOn \<box> TurnOff \<box> Shine))"

export_code Dwarf in Haskell module_name DwarfSignal (string_classes)

end