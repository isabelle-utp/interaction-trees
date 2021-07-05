subsection \<open> Simple Discrete Water Tank\<close>

theory WaterTank
  imports "../ITree_Extraction"
begin lit_vars

alphabet TankState =
  flowOn   :: bool \<comment> \<open> Whether the tap is on or off \<close>
  level    :: integer \<comment> \<open> The current water level \<close>
  finished :: bool \<comment> \<open> Internal flag to indicate that the current communication round has finished \<close>

record_default TankState

chantype chan =
  tock      :: unit \<comment> \<open> Discrete passage of time \<close>
  viewLevel :: "integer" \<comment> \<open> Observe the current level \<close>
  switch    :: unit

definition "rate = (5::integer)"

definition "tstep = (1::integer)"

text \<open> Communications once the ODE has completed an evolution round \<close>

definition Comms :: "(chan, TankState) htree" where
"Comms = 
    finished := False \<Zcomp> 
    while (\<not> finished) do
      (viewLevel!(level) \<rightarrow> Skip 
      \<box> switch!(()) \<rightarrow> (flowOn := (\<not> flowOn))
      \<box> tock!(()) \<rightarrow> (finished := True))
    od"

text \<open> Discrete representation of a simple ODE. The level can rise and fall, but it cannot fall below 0. \<close>

definition ODE :: "(chan, TankState) htree" where
"ODE = level := level + tstep * (if flowOn then rate else (if level = 0 then 0 else -rate))"

definition Tank :: "(chan, TankState) htree" where
"Tank = ODE \<Zcomp> Comms"

definition WaterTank :: "chan process" where
"WaterTank = process [level \<leadsto> 0] (loop Tank)"

export_code WaterTank in Haskell module_name WaterTank (string_classes)


end