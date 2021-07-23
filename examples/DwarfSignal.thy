section \<open> Dwarf Signal \<close>

theory DwarfSignal
  imports "../ITree_Simulation" "../ITree_Eval" "../ITree_Circus"
begin                

subsection \<open> State Space \<close>

enumtype LampId = L1 | L2 | L3

type_synonym Signal = "LampId set"

enumtype ProperState = dark | stop | warning | drive

definition "ProperState = {dark, stop, warning, drive}"

fun signalLamps :: "ProperState \<Rightarrow> LampId set" where
"signalLamps dark = {}" |
"signalLamps stop = {L1, L2}" |
"signalLamps warning = {L1, L3}" |
"signalLamps drive = {L2, L3}"

text \<open> Could we have separate processes for the actual lamp and its controller? We would then
  try to verify that the controller preserves the lamp-based safety properties. The current
  set up doesn't preserve them. \<close>

schema Dwarf = 
  last_proper_state :: "ProperState"
  turn_off :: "LampId set"
  turn_on  :: "LampId set"
  last_state :: "Signal"
  current_state :: "Signal"
  desired_proper_state :: "ProperState"
  where 
    "(current_state - turn_off) \<union> turn_on = signalLamps desired_proper_state"
    "turn_on \<inter> turn_off = {}"

record_default Dwarf

definition "NeverShowAll = (@Dwarf \<and> current_state \<noteq> {L1, L2, L3})\<^sub>e"

definition "MaxOneLampChange = 
  (@Dwarf \<and> 
  (\<exists> l. current_state - last_state = {l} \<or> last_state - current_state = {l} \<or> last_state = current_state))\<^sub>e"

definition "ForbidStopToDrive =
  (@Dwarf \<and> (last_proper_state = stop \<longrightarrow> desired_proper_state \<noteq> drive))\<^sub>e"

definition "DarkOnlyToStop =
  (@Dwarf \<and> (last_proper_state = dark \<longrightarrow> desired_proper_state = stop))\<^sub>e"

definition "DarkOnlyFromStop =
  (@Dwarf \<and> (desired_proper_state = dark \<longrightarrow> last_proper_state = stop))\<^sub>e"

definition "DwarfReq = 
  (@NeverShowAll 
  \<and> @MaxOneLampChange 
  \<and> @ForbidStopToDrive 
  \<and> @DarkOnlyToStop 
  \<and> @DarkOnlyFromStop)\<^sub>e"

chantype chan =
  shine :: "LampId set"
  setNewProperState :: ProperState
  turnOff :: "LampId"
  turnOn :: "LampId"
  violation :: String.literal

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

definition "CheckReq = 
  (\<questiondown>\<not> @NeverShowAll? \<Zcomp> violation!(STR ''NeverShowAll'') \<rightarrow> Skip) \<box>
  (\<questiondown>\<not> @MaxOneLampChange? \<Zcomp> violation!(STR ''MaxOneLampChange'') \<rightarrow> Skip) \<box>
  (\<questiondown>\<not> @ForbidStopToDrive? \<Zcomp> violation!(STR ''ForbidStopToDrive'') \<rightarrow> Skip) \<box>
  (\<questiondown>\<not> @DarkOnlyToStop? \<Zcomp> violation!(STR ''DarkOnlyToStop'') \<rightarrow> Skip) \<box>
  (\<questiondown>\<not> @DarkOnlyFromStop? \<Zcomp> violation!(STR ''DarkOnlyFromStop'') \<rightarrow> Skip)"

term "setNewProperState?(st):(ProperState - {desired_proper_state}) \<rightarrow> 
      (last_proper_state := desired_proper_state \<Zcomp>
       turn_off := current_state - signalLamps st \<Zcomp>
       turn_on := signalLamps st - current_state \<Zcomp>
       last_state := current_state \<Zcomp>
       desired_proper_state := st)"

definition 
  "SetNewProperState = 
    \<questiondown>current_state = signalLamps desired_proper_state? \<Zcomp> 
    setNewProperState?(st):(ProperState - {desired_proper_state}) \<rightarrow> 
      (last_proper_state := desired_proper_state \<Zcomp>
       turn_off := current_state - signalLamps st \<Zcomp>
       turn_on := signalLamps st - current_state \<Zcomp>
       last_state := current_state \<Zcomp>
       desired_proper_state := st)"

definition
  "TurnOff =
   turnOff?(l):turn_off \<rightarrow> 
    (turn_off := turn_off - {l} \<Zcomp>
     turn_on := turn_on - {l} \<Zcomp>
     last_state := current_state \<Zcomp>
     current_state := current_state - {l})"

definition
  "TurnOn =
   turnOn?(l):turn_on \<rightarrow> 
    (turn_off := turn_off - {l} \<Zcomp>
     turn_on := turn_on - {l} \<Zcomp>
     last_state := current_state \<Zcomp>
     current_state := current_state \<union> {l})"

definition "Shine = shine!(current_state) \<rightarrow> Skip"

definition "DwarfSignal
  = process Init (loop (CheckReq \<box> SetNewProperState \<box> TurnOn \<box> TurnOff \<box> Shine))"

simulate DwarfSignal


ML \<open> Code.read_const @{theory} "DwarfSignal" \<close>

ML \<open> 


\<close>

local_setup \<open>
  ITree_Simulator.simulate "DwarfSignal"
\<close>

local_setup \<open> 
Code_Target.export_code true [@{const_name DwarfSignal}] [((("Haskell", ""), SOME ({physical = false}, (Path.explode "simulate", Position.none))), (Token.explode (Thy_Header.get_keywords' @{context}) Position.none "string_classes"))] 
#>
ITree_Simulator.prep_simulation "DwarfSignal"
\<close>

(* [(("Haskell", ""), SOME ({physical = false}, (Path.explode "simulate", Position.none)), [])] *)

(*
local_setup \<open>
fn ctx =>
  Generated_Files.generate_file (Path.binding0 (Path.make ["code", "simulate", "Simulation.hs"]), \<open>\<close>) ctx |>
  (fn ctx => let val _ = Generated_Files.export_generated_files ctx [([], Local_Theory.exit_global ctx)] in ctx end)
\<close>
*)

local_setup \<open>  \<close>


                          
ML \<open> ITree_Simulator.run_simulation @{theory} \<close>
(*
compile_generated_files _ and "code/simulate/Simulate.hs" (in ITree_Simulation) where 
\<open>     fn path => let val n = @{print} (Path.implode path); val ret = Isabelle_System.bash ("/home/simonfoster/Isabelle/simulate.sh " ^ n ^ "/code/simulate"  ^ " DwarfSignal.hs") in  () end
  \<close>
*)

ML \<open> Isabelle_System.getenv "ISABELLE_TMP" \<close>

text \<open> Testing SML lazy code evaluation \<close>

code_lazy_type itree

lemma "trres \<langle>setNewProperState warning, turnOff L2, turnOn L3, shine {L1, L3}\<rangle> 20 DwarfSignal = VisR {shine_C {L1, L3}, setNewProperState_C dark, setNewProperState_C stop, setNewProperState_C drive}"
  by eval




end