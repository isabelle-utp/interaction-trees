section \<open> Simulation of a very basic RoboChart model \<close>
text \<open> This theory aims for simulation of a trivial RoboChart model based on its CSP
 semantics. We use the @{term "rename"} operator for renaming.
\<close>
theory RoboChart_ChemicalDetector_autonomous_microcontroller
  imports "RoboChart_ChemicalDetector_autonomous_general"
begin

declare [[show_types]]

subsection \<open> Movement \<close>
subsubsection \<open> Constants \<close>
abbreviation const_Movement_lv :: "core_real" where
"const_Movement_lv \<equiv> 0"

abbreviation const_Movement_evadeTime :: "core_nat" where
"const_Movement_evadeTime \<equiv> 0"

abbreviation const_Movement_stuckPeriod :: "core_nat" where
"const_Movement_stuckPeriod \<equiv> 0"

abbreviation const_Movement_stuckDist :: "core_real" where
"const_Movement_stuckDist \<equiv> 0"

abbreviation const_Movement_outPeriod :: "core_nat" where
"const_Movement_outPeriod \<equiv> 0"

subsubsection \<open> Types \<close>
enumtype SIDS_Movement = SID_Movement
	              | SID_Movement_Waiting
	              | SID_Movement_Going
	              | SID_Movement_Found
	              | SID_Movement_j1
	              | SID_Movement_Avoiding
	              | SID_Movement_TryingAgain
	              | SID_Movement_AvoidingAgain
	              | SID_Movement_GettingOut

definition "SIDS_Movement_list = enum_SIDS_Movement_inst.enum_SIDS_Movement"
definition "SIDS_Movement_set = set SIDS_Movement_list"
definition "SIDS_Movement_nodes = (removeAll SID_Movement SIDS_Movement_list)"
definition "SIDS_Movement_no_Waiting = (removeAll SID_Movement_Waiting SIDS_Movement_list)"
definition "SIDS_Movement_no_Going = (removeAll SID_Movement_Going SIDS_Movement_list)"
definition "SIDS_Movement_no_Found = (removeAll SID_Movement_Found SIDS_Movement_list)"
definition "SIDS_Movement_no_Avoiding = (removeAll SID_Movement_Avoiding SIDS_Movement_list)"
definition "SIDS_Movement_no_j1 = (removeAll SID_Movement_j1 SIDS_Movement_list)"
definition "SIDS_Movement_no_TryingAgain = (removeAll SID_Movement_TryingAgain SIDS_Movement_list)"
definition "SIDS_Movement_no_AvoidingAgain = (removeAll SID_Movement_AvoidingAgain SIDS_Movement_list)"
definition "SIDS_Movement_no_GettingOut = (removeAll SID_Movement_GettingOut SIDS_Movement_list)"

(* Here we change enumtype to datatype as enumtype will take very long time to resolve 
this definition (I mean Isabelle keeps running poly and high CPU usage.) *)

datatype TIDS_Movement = NULLTRANSITION__Movement
	              | TID_Movement_t1
	              | TID_Movement_t2
	              | TID_Movement_t3
	              | TID_Movement_t4
	              | TID_Movement_t6
	              | TID_Movement_t7
	              | TID_Movement_t8
	              | TID_Movement_t9
	              | TID_Movement_t10
	              | TID_Movement_t11
	              | TID_Movement_t12
	              | TID_Movement_t14
	              | TID_Movement_t0
	              | TID_Movement_t15
	              | TID_Movement_t16
	              | TID_Movement_t17
	              | TID_Movement_t18
	              | TID_Movement_t19
	              | TID_Movement_t20
	              | TID_Movement_t21
	              | TID_Movement_t22
	              | TID_Movement_t13
	              | TID_Movement_t5


(*
typedef Movement = "{()}" by auto

type_synonym TIDS_Movement = "(Movement, 24) TrID"

abbreviation NULLTRANSITION__Movement :: "TIDS_Movement" where
"NULLTRANSITION__Movement \<equiv> MkTrid TYPE(Movement) 23"
abbreviation TID_Movement_t0 :: "TIDS_Movement" where
"TID_Movement_t0 \<equiv> MkTrid TYPE(Movement) 0"
abbreviation TID_Movement_t1 :: "TIDS_Movement" where
"TID_Movement_t1 \<equiv> MkTrid TYPE(Movement) 1"
abbreviation TID_Movement_t2 :: "TIDS_Movement" where
"TID_Movement_t2 \<equiv> MkTrid TYPE(Movement) 2"
abbreviation TID_Movement_t3 :: "TIDS_Movement" where
"TID_Movement_t3 \<equiv> MkTrid TYPE(Movement) 3"
abbreviation TID_Movement_t4 :: "TIDS_Movement" where
"TID_Movement_t4 \<equiv> MkTrid TYPE(Movement) 4"
abbreviation TID_Movement_t5 :: "TIDS_Movement" where
"TID_Movement_t5 \<equiv> MkTrid TYPE(Movement) 5"
abbreviation TID_Movement_t6 :: "TIDS_Movement" where
"TID_Movement_t6 \<equiv> MkTrid TYPE(Movement) 6"
abbreviation TID_Movement_t7 :: "TIDS_Movement" where
"TID_Movement_t7 \<equiv> MkTrid TYPE(Movement) 7"
abbreviation TID_Movement_t8 :: "TIDS_Movement" where
"TID_Movement_t8 \<equiv> MkTrid TYPE(Movement) 8"
abbreviation TID_Movement_t9 :: "TIDS_Movement" where
"TID_Movement_t9 \<equiv> MkTrid TYPE(Movement) 9"
abbreviation TID_Movement_t10 :: "TIDS_Movement" where
"TID_Movement_t10 \<equiv> MkTrid TYPE(Movement) 10"
abbreviation TID_Movement_t11 :: "TIDS_Movement" where
"TID_Movement_t11 \<equiv> MkTrid TYPE(Movement) 11"
abbreviation TID_Movement_t12 :: "TIDS_Movement" where
"TID_Movement_t12 \<equiv> MkTrid TYPE(Movement) 12"
abbreviation TID_Movement_t13 :: "TIDS_Movement" where
"TID_Movement_t13 \<equiv> MkTrid TYPE(Movement) 13"
abbreviation TID_Movement_t14 :: "TIDS_Movement" where
"TID_Movement_t14 \<equiv> MkTrid TYPE(Movement) 14"
abbreviation TID_Movement_t15 :: "TIDS_Movement" where
"TID_Movement_t15 \<equiv> MkTrid TYPE(Movement) 15"
abbreviation TID_Movement_t16 :: "TIDS_Movement" where
"TID_Movement_t16 \<equiv> MkTrid TYPE(Movement) 16"
abbreviation TID_Movement_t17 :: "TIDS_Movement" where
"TID_Movement_t17 \<equiv> MkTrid TYPE(Movement) 17"
abbreviation TID_Movement_t18 :: "TIDS_Movement" where
"TID_Movement_t18 \<equiv> MkTrid TYPE(Movement) 18"
abbreviation TID_Movement_t19 :: "TIDS_Movement" where
"TID_Movement_t19 \<equiv> MkTrid TYPE(Movement) 19"
abbreviation TID_Movement_t20 :: "TIDS_Movement" where
"TID_Movement_t20 \<equiv> MkTrid TYPE(Movement) 20"
abbreviation TID_Movement_t21 :: "TIDS_Movement" where
"TID_Movement_t21 \<equiv> MkTrid TYPE(Movement) 21"
abbreviation TID_Movement_t22 :: "TIDS_Movement" where
"TID_Movement_t22 \<equiv> MkTrid TYPE(Movement) 22"
*)
(*
definition "TIDS_Movement_list = enum_TIDS_Movement_inst.enum_TIDS_Movement"
*)
definition "TIDS_Movement_list = [NULLTRANSITION__Movement, TID_Movement_t0,
  TID_Movement_t1, TID_Movement_t2, TID_Movement_t3, TID_Movement_t4, TID_Movement_t5,
  TID_Movement_t6, TID_Movement_t7, TID_Movement_t8, TID_Movement_t9, TID_Movement_t10, 
  TID_Movement_t11, TID_Movement_t12, TID_Movement_t13, TID_Movement_t14, TID_Movement_t15, 
  TID_Movement_t16, TID_Movement_t17, TID_Movement_t18, TID_Movement_t19, TID_Movement_t20, 
  TID_Movement_t21, TID_Movement_t22]"

(*
definition "TIDS_Movement_list \<equiv> 
  map ((MkTrid TYPE(Movement)) \<circ> (\<lambda>i. (Abs_bit0' i)::(24))) (upt 0 (CARD(24)))"
*)
definition "TIDS_Movement_set = set TIDS_Movement_list"

text \<open> Identifiers of transitions that can interrupt a state, excluding transitions from junctions. \<close>
definition "ITIDS_Movement_list = [TID_Movement_t0,
  TID_Movement_t2, TID_Movement_t3,	TID_Movement_t4, TID_Movement_t5, TID_Movement_t6, 
  TID_Movement_t7, TID_Movement_t8,	TID_Movement_t9, TID_Movement_t10,	TID_Movement_t11,
  TID_Movement_t12,	TID_Movement_t13, TID_Movement_t14,	TID_Movement_t15, TID_Movement_t16,
  TID_Movement_t17,	TID_Movement_t18, TID_Movement_t19,	TID_Movement_t20, TID_Movement_t21,
  TID_Movement_t22  
]"

definition "ITIDS_Movement = set ITIDS_Movement_list"

chantype Chan_Movement =
(* flow channels *)
  internal_Movement :: TIDS_Movement
  enter_Movement :: "SIDS_Movement \<times> SIDS_Movement"
  entered_Movement :: "SIDS_Movement \<times> SIDS_Movement"
  exit_Movement :: "SIDS_Movement \<times> SIDS_Movement"
  exited_Movement :: "SIDS_Movement \<times> SIDS_Movement"
  terminate_Movement :: unit

(* Variables *)
  get_d0_Movement :: core_real
  set_d0_Movement :: core_real
  get_d1_Movement :: core_real
  set_d1_Movement :: core_real
  get_l_Movement :: "Location_Loc"
  set_l_Movement :: "Location_Loc"
  get_a_Movement :: "Chemical_Angle"
  set_a_Movement :: "Chemical_Angle"

(* event channels *)
  obstacle__Movement :: "TIDS_Movement \<times> InOut \<times> Location_Loc"
  obstacle_Movement :: "InOut \<times> Location_Loc"
  odometer__Movement :: "TIDS_Movement \<times> InOut \<times> core_real"
  odometer_Movement :: "InOut \<times> core_real"
  resume__Movement :: "TIDS_Movement \<times> InOut"
  resume_Movement :: "InOut"
  turn__Movement :: "TIDS_Movement \<times> InOut \<times> Chemical_Angle"
  turn_Movement :: "InOut \<times> Chemical_Angle"
  stop__Movement :: "TIDS_Movement \<times> InOut"
  stop_Movement :: "InOut"
  flag__Movement :: "TIDS_Movement \<times> InOut"
  flag_Movement :: "InOut"

(* Call events for undefined operations *)
  changeDirectionCall_Movement :: "Location_Loc"
  randomeWalkCall_Movement :: unit
  moveCall_Movement :: "core_real \<times> Chemical_Angle"
  shortRandomWalkCall_Movement :: unit

subsubsection \<open> Operation Calls \<close>
definition CALL__changeDirection_Movement :: "integer \<Rightarrow> Location_Loc \<Rightarrow> (Chan_Movement, unit) itree" where
"CALL__changeDirection_Movement idd l = do {outp changeDirectionCall_Movement l}"

definition CALL__randomWalk_Movement :: "integer \<Rightarrow> (Chan_Movement, unit) itree" where
"CALL__randomWalk_Movement idd = do {outp randomeWalkCall_Movement ()}"

definition CALL__move_Movement :: "integer \<Rightarrow> core_real \<Rightarrow> Chemical_Angle \<Rightarrow> (Chan_Movement, unit) itree" where
"CALL__move_Movement idd lv a = do {outp moveCall_Movement (lv, a)}"

definition CALL__shortRandomWalk_Movement :: "integer \<Rightarrow> (Chan_Movement, unit) itree" where
"CALL__shortRandomWalk_Movement idd = do {outp shortRandomWalkCall_Movement ()}"

subsubsection \<open> Sets of events \<close>

abbreviation "int_int_tids_Movement \<equiv> 
  removeAll NULLTRANSITION__Movement (removeAll (TID_Movement_t1) TIDS_Movement_list)"
(*[TID_Movement_t0,
  TID_Movement_t2, TID_Movement_t3, TID_Movement_t4, TID_Movement_t5,
  TID_Movement_t6, TID_Movement_t7, TID_Movement_t8, TID_Movement_t9, TID_Movement_t10, 
  TID_Movement_t11, TID_Movement_t12, TID_Movement_t13, TID_Movement_t14, TID_Movement_t15, 
  TID_Movement_t16, TID_Movement_t17, TID_Movement_t18, TID_Movement_t19, TID_Movement_t20, 
  TID_Movement_t21, TID_Movement_t22]*)

definition int_int_Movement where
"int_int_Movement = set (
  (enumchans3 [obstacle__Movement_C] int_int_tids_Movement InOut_list Location_Loc_list) @
  (enumchans3 [odometer__Movement_C] int_int_tids_Movement InOut_list rc.core_real_list) @
  (enumchans2 [resume__Movement_C, stop__Movement_C, flag__Movement_C] 
    int_int_tids_Movement InOut_list) @
  (enumchans3 [turn__Movement_C] int_int_tids_Movement InOut_list Chemical_Angle_list) @
  (enumchan1 internal_Movement_C int_int_tids_Movement)
)"

abbreviation "enter_exit_channels_Movement \<equiv>
  [enter_Movement_C, entered_Movement_C, exit_Movement_C, exited_Movement_C]"

definition internal_events_Movement where
"internal_events_Movement = set (
  enumchans2 enter_exit_channels_Movement SIDS_Movement_list SIDS_Movement_list
)"


definition Movement_d0_events where
"Movement_d0_events = 
    set (enumchans1 [get_d0_Movement_C, set_d0_Movement_C] rc.core_real_list)
"

definition Movement_d1_events where
"Movement_d1_events = 
    set (enumchans1 [get_d1_Movement_C, set_d1_Movement_C] rc.core_real_list)
"

definition Movement_l_events where
"Movement_l_events = 
    set (enumchans1 [get_l_Movement_C, set_l_Movement_C] Location_Loc_list)
"

definition Movement_a_events where
"Movement_a_events = 
    set (enumchans1 [get_a_Movement_C, set_a_Movement_C] Chemical_Angle_list)
"

definition Movement_MachineInternalEvents where
"Movement_MachineInternalEvents = 
  set (enumchan1 internal_Movement_C TIDS_Movement_list)
"

subsubsection \<open> State Machine Memory \<close>
text \<open> Memory cell processes \<close>

(* for the local variable x *)
definition Movement_Memory_opt_d0 where
"Movement_Memory_opt_d0 = 
  mem_of_lvar get_d0_Movement set_d0_Movement (rc.core_real_set)"

definition Movement_Memory_opt_d1 where
"Movement_Memory_opt_d1 = 
  mem_of_lvar get_d1_Movement set_d1_Movement (rc.core_real_set)"

definition Movement_Memory_opt_a where
"Movement_Memory_opt_a = mem_of_lvar get_a_Movement set_a_Movement Chemical_Angle_set"

definition Movement_Memory_opt_l where
"Movement_Memory_opt_l = mem_of_lvar get_l_Movement set_l_Movement (Location_Loc_set)"

text \<open> Memory transition processes \<close>
definition Movement_MemoryTransitions_opt_0 where
"Movement_MemoryTransitions_opt_0 = 
  loop (\<lambda> id::integer. 
    ( 
    do {outp resume__Movement (TID_Movement_t0, din) ; Ret (id)} \<box> 
    do {a \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t3, din, x). 
              x \<leftarrow> (Chemical_Angle_list)]) ; Ret (id)} \<box> 
    do {outp stop__Movement (TID_Movement_t16, din) ; Ret (id)} \<box>
    do {outp stop__Movement (TID_Movement_t17, din) ; Ret (id)} \<box> 
    do {a \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t14, din, x). 
              x \<leftarrow> (Chemical_Angle_list)]) ; Ret (id)} \<box> 
    do {outp resume__Movement (TID_Movement_t22, din) ; Ret (id)} \<box> 
    do {outp stop__Movement (TID_Movement_t18, din) ; Ret (id)} \<box>
    do {outp resume__Movement (TID_Movement_t20, din) ; Ret (id)} \<box>
    do {outp internal_Movement TID_Movement_t1 ; Ret (id)} \<box>
    do {l \<leftarrow> inp_in obstacle__Movement (set [(TID_Movement_t6, din, l). 
              l \<leftarrow> (Location_Loc_list)]) ; Ret (id)} \<box>
    do {outp resume__Movement (TID_Movement_t21, din) ; Ret (id)} \<box>
    do {outp stop__Movement (TID_Movement_t15, din) ; Ret (id)} \<box>
    do {outp internal_Movement TID_Movement_t5 ; Ret (id)} \<box>
    do {outp stop__Movement (TID_Movement_t4, din) ; Ret (id)} \<box>
    do {outp resume__Movement (TID_Movement_t10, din) ; Ret (id)} \<box>
    do {a \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t7, din, x). 
              x \<leftarrow> (Chemical_Angle_list)]) ; Ret (id)} \<box> 
    do {outp stop__Movement (TID_Movement_t9, din) ; Ret (id)} \<box>
    do {outp resume__Movement (TID_Movement_t19, din) ; Ret (id)} \<box>
    do {l \<leftarrow> inp_in obstacle__Movement (set [(TID_Movement_t11, din, l). 
              l \<leftarrow> (Location_Loc_list)]) ; Ret (id)} \<box>
    do {a \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t8, din, x). 
              x \<leftarrow> (Chemical_Angle_list)]) ; Ret (id)} \<box> 
    do {a \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t2, din, x). 
              x \<leftarrow> (Chemical_Angle_list)]) ; Ret (id)}
    )
)
"

definition Movement_MemoryTransitions_opt_1 where
"Movement_MemoryTransitions_opt_1 = 
  loop (\<lambda> id::integer.
    do {d1 \<leftarrow> inp_in get_d1_Movement rc.core_real_set ; 
        d0 \<leftarrow> inp_in get_d0_Movement rc.core_real_set ;
        (
          do {guard (True); outp internal_Movement TID_Movement_t12 ; Ret (id)} \<box>
          do {guard (True); outp internal_Movement TID_Movement_t13 ; Ret (id)} \<box>
          do {inp_in set_d1_Movement rc.core_real_set; Ret (id)} \<box>
          do {inp_in set_d0_Movement rc.core_real_set; Ret (id)}
        )
    }
  )
"

subsubsection \<open> States \<close>
paragraph \<open> Initial \<close>
definition I_Movement_i1 where
"I_Movement_i1 = (\<lambda> (id::integer) . 
  do {outp internal_Movement TID_Movement_t1 ; 
      outp enter_Movement (SID_Movement, SID_Movement_Waiting);
      outp entered_Movement (SID_Movement, SID_Movement_Waiting)
  })
"

paragraph \<open> Waiting \<close>
definition CS_Movement_Waiting_sync where
"CS_Movement_Waiting_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_Waiting] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_Waiting])
)"

definition Movement_Waiting_triggers where
"Movement_Waiting_triggers = set (
  (enumchans3 [obstacle__Movement_C] [TID_Movement_t6, TID_Movement_t11] InOut_list Location_Loc_list) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t22, TID_Movement_t20, TID_Movement_t21, TID_Movement_t10, 
    TID_Movement_t19] InOut_list) @
  (enumchans2 [stop__Movement_C] 
    [TID_Movement_t16, TID_Movement_t17, TID_Movement_t18, TID_Movement_t15, TID_Movement_t4, 
    TID_Movement_t9] InOut_list) @
  (enumchans3 [turn__Movement_C] [TID_Movement_t3, TID_Movement_t14, TID_Movement_t7, 
    TID_Movement_t8, TID_Movement_t2] InOut_list Chemical_Angle_list) @
  (enumchan1 internal_Movement_C [TID_Movement_t12, TID_Movement_t5, TID_Movement_t13])
)
"

definition tids_Movement_Waiting where
" tids_Movement_Waiting = 
    (filter 
        (\<lambda> s. s \<notin> (set [NULLTRANSITION__Movement,TID_Movement_t0,TID_Movement_t3,TID_Movement_t12,
          TID_Movement_t16,TID_Movement_t17,TID_Movement_t14,TID_Movement_t22,TID_Movement_t18,
          TID_Movement_t20,TID_Movement_t6,TID_Movement_t21,TID_Movement_t15,TID_Movement_t5,
          TID_Movement_t13,TID_Movement_t4,TID_Movement_t10,TID_Movement_t7,TID_Movement_t19,
          TID_Movement_t9,TID_Movement_t11,TID_Movement_t8,TID_Movement_t2])) 
        ITIDS_Movement_list)"

abbreviation Other_SIDs_to_Waiting_Movement where
"Other_SIDs_to_Waiting_Movement \<equiv>
  set [(s, SID_Movement_Waiting) . s \<leftarrow> (SIDS_Movement_no_Waiting)]"

definition exit_event_Movement1 :: 
  "integer \<Rightarrow> (TIDS_Movement \<Longrightarrow>\<^sub>\<triangle> Chan_Movement) \<Rightarrow> SIDS_Movement
   \<Rightarrow> TIDS_Movement list \<Rightarrow> SIDS_Movement rel 
   \<Rightarrow> (Chan_Movement, bool \<times> integer \<times> SIDS_Movement) itree" where
"exit_event_Movement1 idd ch sid tids other_sids = 
  do {inp_in ch (set tids);
      y \<leftarrow> inp_in exit_Movement other_sids;
      outp exited_Movement (fst y, sid);
      Ret(False, idd, sid)
}"

definition exit_event_Movement2 :: 
  "integer \<Rightarrow> (TIDS_Movement \<times> InOut \<Longrightarrow>\<^sub>\<triangle> Chan_Movement) \<Rightarrow> SIDS_Movement
   \<Rightarrow> TIDS_Movement list \<Rightarrow> SIDS_Movement rel 
   \<Rightarrow> (Chan_Movement, bool \<times> integer \<times> SIDS_Movement) itree" where
"exit_event_Movement2 idd ch sid tids other_sids = 
  do {r \<leftarrow> inp_in ch (set [(t, d). t \<leftarrow> (tids), d \<leftarrow> InOut_list]);
      y \<leftarrow> inp_in exit_Movement other_sids;
      outp exited_Movement (fst y, sid);
      Ret(False, idd, sid)
  }
"

definition exit_event_Movement3 :: 
  "integer \<Rightarrow> (TIDS_Movement \<times> InOut \<times> 'a \<Longrightarrow>\<^sub>\<triangle> Chan_Movement) \<Rightarrow> SIDS_Movement
   \<Rightarrow> TIDS_Movement list \<Rightarrow> 'a list \<Rightarrow> SIDS_Movement rel
   \<Rightarrow> (Chan_Movement, bool \<times> integer \<times> SIDS_Movement) itree" where
"exit_event_Movement3 idd ch sid tids alist other_sids = 
  do {r \<leftarrow> inp_in ch (set [(t, d, a). t \<leftarrow> (tids), d \<leftarrow> InOut_list, a \<leftarrow> alist]);
      y \<leftarrow> inp_in exit_Movement other_sids;
      outp exited_Movement (fst y, sid);
      Ret(False, idd, sid)
  }
"
definition exit_events_Movement ::  "integer \<Rightarrow> SIDS_Movement \<Rightarrow> TIDS_Movement list
    \<Rightarrow> SIDS_Movement rel \<Rightarrow> (Chan_Movement, bool \<times> integer \<times> SIDS_Movement) itree" where
"exit_events_Movement idd sid tids other_sids =
    (exit_event_Movement1 idd internal_Movement sid tids other_sids \<box>
     exit_event_Movement3 idd obstacle__Movement sid tids Location_Loc_list other_sids \<box>
     exit_event_Movement3 idd odometer__Movement sid tids rc.core_real_list other_sids \<box>
     exit_event_Movement2 idd resume__Movement sid tids other_sids \<box>
     exit_event_Movement3 idd turn__Movement sid tids Chemical_Angle_list other_sids \<box>
     exit_event_Movement2 idd stop__Movement sid tids other_sids \<box>
     exit_event_Movement2 idd flag__Movement sid tids other_sids
    )"

(*
definition exit_events_Movement ::  "integer \<Rightarrow> SIDS_Movement \<Rightarrow> TIDS_Movement list
    \<Rightarrow> SIDS_Movement rel \<Rightarrow> (Chan_Movement, bool \<times> integer \<times> SIDS_Movement) itree" where
"exit_events_Movement idd sid tids other_sids =
    (do {inp_in internal_Movement (set tids);
        y \<leftarrow> inp_in exit_Movement other_sids;
          outp exited_Movement (fst y, sid);
          Ret(False, idd, sid)
        } \<box>
    do {r \<leftarrow> inp_in obstacle__Movement (set [(t, d, l). 
            t \<leftarrow> (tids), d \<leftarrow> InOut_list,
            l \<leftarrow> (Location_Loc_list)]) ;
          y \<leftarrow> inp_in exit_Movement other_sids;
            outp exited_Movement (fst y, sid);
            Ret(False, idd, sid)
        } \<box>
    do {r \<leftarrow> inp_in odometer__Movement (set [(t, d, l). 
            t \<leftarrow> (tids), d \<leftarrow> InOut_list,
            l \<leftarrow> rc.core_real_list]) ;
          y \<leftarrow> inp_in exit_Movement other_sids;
            outp exited_Movement (fst y, sid);
            Ret(False, idd, sid)
        } \<box>
    do {t \<leftarrow> inp_in resume__Movement (set [(t, d). 
            t \<leftarrow> (tids), d \<leftarrow> InOut_list]) ;
          y \<leftarrow> inp_in exit_Movement other_sids;
            outp exited_Movement (fst y, sid);
            Ret(False, idd, sid)
        } \<box>
    do {t \<leftarrow> inp_in turn__Movement (set [(t, d, a). 
            t \<leftarrow> (tids), d \<leftarrow> InOut_list,
            a \<leftarrow> Chemical_Angle_list]) ;
          y \<leftarrow> inp_in exit_Movement other_sids;
            outp exited_Movement (fst y, sid);
            Ret(False, idd, sid)
        } \<box>
    do {t \<leftarrow> inp_in stop__Movement (set [(t, d). 
            t \<leftarrow> (tids), d \<leftarrow> InOut_list]) ;
          y \<leftarrow> inp_in exit_Movement other_sids;
            outp exited_Movement (fst y, sid);
            Ret(False, idd, sid)
        } \<box>
    do {t \<leftarrow> inp_in flag__Movement (set [(t, d). 
            t \<leftarrow> (tids), d \<leftarrow> InOut_list]) ;
          y \<leftarrow> inp_in exit_Movement other_sids;
            outp exited_Movement (fst y, sid);
            Ret(False, idd, sid)
        }
    )"
*)

definition State_Movement_Waiting where 
"State_Movement_Waiting = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_Waiting_Movement ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_Movement_Waiting_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_Movement (snd (snd s), SID_Movement_Waiting);
              (do {guard(True); CALL__randomWalk_Movement(id) ; stop} \<triangle>
                (
                \<comment> \<open> T_Movement_t2 \<close>
                do {t \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t2, din, a). 
                                a \<leftarrow> (Chemical_Angle_list)]) ;
                      outp set_a_Movement (snd (snd t)) ; 
                      outp exit_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      outp exited_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      outp enter_Movement (SID_Movement_Waiting, SID_Movement_Going);
                      outp entered_Movement (SID_Movement_Waiting, SID_Movement_Going);
                      Ret(False, fst (snd s), SID_Movement_Waiting)
                    } \<box>
                \<comment> \<open> T_Movement_t0 \<close>
                do {outp resume__Movement (TID_Movement_t0, din) ;
                      outp exit_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      outp exited_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      outp enter_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      Ret(True, fst (snd s), SID_Movement_Waiting)
                    } \<box>
                \<comment> \<open> T_Movement_t15 \<close>
                do {outp resume__Movement (TID_Movement_t15, din) ;
                      outp exit_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      outp exited_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      outp enter_Movement (SID_Movement_Waiting, SID_Movement_Found);
                      outp entered_Movement (SID_Movement_Waiting, SID_Movement_Found);
                      Ret(False, fst (snd s), SID_Movement_Waiting)
                    } \<box>
                (exit_events_Movement (fst (snd s)) SID_Movement_Waiting 
                   tids_Movement_Waiting Other_SIDs_to_Waiting_Movement)
                )
              )
            })
            \<comment> \<open> The previous state: a triple \<close> 
            (ret)
        ) ;
        Ret (id)
  }
)
"

definition State_Movement_Waiting_R where
"State_Movement_Waiting_R (idd::integer) = 
   (discard_state (State_Movement_Waiting idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_Movement - Movement_Waiting_triggers) \<^esub> 
   skip
"

paragraph \<open> Going \<close>
definition CS_Movement_Going_sync where
"CS_Movement_Going_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_Going] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_Going])
)"

definition Movement_Going_triggers where
"Movement_Going_triggers = set (
  (enumchan1 internal_Movement_C [TID_Movement_t12, TID_Movement_t5, TID_Movement_t13]) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t22, TID_Movement_t20, TID_Movement_t21, TID_Movement_t10,
     TID_Movement_t19] InOut_list) @
  (enumchans3 [turn__Movement_C] [TID_Movement_t3, TID_Movement_t14, TID_Movement_t7, TID_Movement_t8,
    TID_Movement_t2] InOut_list Chemical_Angle_list) @
  (enumchans2 [stop__Movement_C] 
    [TID_Movement_t16, TID_Movement_t17, TID_Movement_t18, TID_Movement_t15, TID_Movement_t4, 
    TID_Movement_t9] InOut_list) @
  (enumchans3 [obstacle__Movement_C] [TID_Movement_t6, TID_Movement_t11] InOut_list Location_Loc_list)
)
"

definition tids_Movement_Going where
" tids_Movement_Going = 
    (filter 
        (\<lambda> s. s \<notin> (set [NULLTRANSITION__Movement,TID_Movement_t0,TID_Movement_t3,TID_Movement_t12,
          TID_Movement_t16,TID_Movement_t17,TID_Movement_t14,TID_Movement_t22,TID_Movement_t18,
          TID_Movement_t20,TID_Movement_t6,TID_Movement_t21,TID_Movement_t15,TID_Movement_t5,
          TID_Movement_t13,TID_Movement_t4,TID_Movement_t10,TID_Movement_t7,TID_Movement_t19,
          TID_Movement_t9,TID_Movement_t11,TID_Movement_t8,TID_Movement_t2])) 
        ITIDS_Movement_list)"

abbreviation Other_SIDs_to_Going_Movement where
"Other_SIDs_to_Going_Movement \<equiv>
  set [(s, SID_Movement_Going) . s \<leftarrow> (SIDS_Movement_no_Going)]"

definition State_Movement_Going where 
"State_Movement_Going = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_Going_Movement ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_Movement_Going_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              a \<leftarrow> inp_in get_a_Movement (set Chemical_Angle_list);
              guard(True); CALL__move_Movement id  const_Movement_lv  a;
              outp entered_Movement (snd (snd s), SID_Movement_Going);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_Movement_t3 \<close>
                do {t \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t2, din, a). 
                                a \<leftarrow> (Chemical_Angle_list)]) ;
                      outp set_a_Movement (snd (snd t)) ; 
                      outp exit_Movement (SID_Movement_Going, SID_Movement_Going);
                      outp exited_Movement (SID_Movement_Going, SID_Movement_Going);
                      outp enter_Movement (SID_Movement_Going, SID_Movement_Going);
                      Ret(True, fst (snd s), SID_Movement_Going)
                    } \<box>
                \<comment> \<open> T_Movement_t4 \<close>
                do {outp stop__Movement (TID_Movement_t4, din) ;
                      outp exit_Movement (SID_Movement_Going, SID_Movement_Going);
                      outp exited_Movement (SID_Movement_Going, SID_Movement_Going);
                      outp enter_Movement (SID_Movement_Going, SID_Movement_Found);
                      outp entered_Movement (SID_Movement_Going, SID_Movement_Found);
                      Ret(False, fst (snd s), SID_Movement_Going)
                    } \<box>
                \<comment> \<open> T_Movement_t6 \<close>
                do {r \<leftarrow> inp_in obstacle__Movement (set [(TID_Movement_t6, din, a). 
                        a \<leftarrow> Location_Loc_list]);
                      outp set_l_Movement (snd (snd r)) ; 
                      outp exit_Movement (SID_Movement_Going, SID_Movement_Going);
                      outp exited_Movement (SID_Movement_Going, SID_Movement_Going);
                      outp enter_Movement (SID_Movement_Going, SID_Movement_Avoiding);
                      outp entered_Movement (SID_Movement_Going, SID_Movement_Avoiding);
                      Ret(False, fst (snd s), SID_Movement_Going)
                    } \<box>
                (exit_events_Movement (fst (snd s)) SID_Movement_Going 
                   tids_Movement_Going Other_SIDs_to_Going_Movement)
                )
              )
            })
            \<comment> \<open> The previous state: a triple \<close> 
            (ret)
        ) ;
        Ret (id)
  }
)
"

definition State_Movement_Going_R where
"State_Movement_Going_R (idd::integer) = 
   (discard_state (State_Movement_Going idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_Movement - Movement_Going_triggers) \<^esub> 
   skip
"

paragraph \<open> Found \<close>
definition CS_Movement_Found_sync where
"CS_Movement_Found_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_Found] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_Found])
)"

definition Movement_Found_triggers where
"Movement_Found_triggers = set (
  (enumchan1 internal_Movement_C [TID_Movement_t5]))
"

definition tids_Movement_Found where
" tids_Movement_Found = 
    (filter 
        (\<lambda> s. s \<notin> (set [NULLTRANSITION__Movement,TID_Movement_t0,TID_Movement_t3,TID_Movement_t12,
          TID_Movement_t16,TID_Movement_t17,TID_Movement_t14,TID_Movement_t22,TID_Movement_t18,
          TID_Movement_t20,TID_Movement_t6,TID_Movement_t21,TID_Movement_t15,TID_Movement_t5,
          TID_Movement_t13,TID_Movement_t4,TID_Movement_t10,TID_Movement_t7,TID_Movement_t19,
          TID_Movement_t9,TID_Movement_t11,TID_Movement_t8,TID_Movement_t2])) 
        ITIDS_Movement_list)"

abbreviation Other_SIDs_to_Found_Movement where
"Other_SIDs_to_Found_Movement \<equiv>
  set [(s, SID_Movement_Found) . s \<leftarrow> (SIDS_Movement_no_Found)]"

definition State_Movement_Found where 
"State_Movement_Found = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_Found_Movement ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_Movement_Found_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              guard(True); CALL__move_Movement id  0  Chemical_Angle_Front;
              guard(True); outp flag_Movement dout;
              outp entered_Movement (snd (snd s), SID_Movement_Found);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_Movement_t5 \<close>
                do {
                      outp internal_Movement TID_Movement_t5 ; 
                      outp exit_Movement (SID_Movement_Found, SID_Movement_Found);
                      outp exited_Movement (SID_Movement_Found, SID_Movement_Found);
                      outp enter_Movement (SID_Movement_Found, SID_Movement_j1);
                      outp entered_Movement (SID_Movement_Found, SID_Movement_j1);
                      Ret(False, fst (snd s), SID_Movement_Found)
                    } \<box>
                (exit_events_Movement (fst (snd s)) SID_Movement_Found 
                   tids_Movement_Found Other_SIDs_to_Found_Movement)
                )
              )
            })
            \<comment> \<open> The previous state: a triple \<close> 
            (ret)
        ) ;
        Ret (id)
  }
)
"

definition State_Movement_Found_R where
"State_Movement_Found_R (idd::integer) = 
   (discard_state (State_Movement_Found idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_Movement - Movement_Found_triggers) \<^esub> 
   skip
"
paragraph \<open> j1 \<close>
definition CS_Movement_j1_sync where
"CS_Movement_j1_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_j1] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_j1])
)"

definition Movement_j1_triggers where
"Movement_j1_triggers = set ([])
"

definition tids_Movement_j1 where
" tids_Movement_j1 = 
    (filter 
        (\<lambda> s. s \<notin> (set [NULLTRANSITION__Movement,TID_Movement_t0,TID_Movement_t3,TID_Movement_t12,
          TID_Movement_t16,TID_Movement_t17,TID_Movement_t14,TID_Movement_t22,TID_Movement_t18,
          TID_Movement_t20,TID_Movement_t6,TID_Movement_t21,TID_Movement_t15,TID_Movement_t5,
          TID_Movement_t13,TID_Movement_t4,TID_Movement_t10,TID_Movement_t7,TID_Movement_t19,
          TID_Movement_t9,TID_Movement_t11,TID_Movement_t8,TID_Movement_t2])) 
        ITIDS_Movement_list)"

abbreviation Other_SIDs_to_j1_Movement where
"Other_SIDs_to_j1_Movement \<equiv>
  set [(s, SID_Movement_j1) . s \<leftarrow> (SIDS_Movement_no_j1)]"

definition State_Movement_j1 where 
"State_Movement_j1 = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_j1_Movement ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_Movement_j1_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_Movement (snd (snd s), SID_Movement_j1);
              outp terminate_Movement ();
              Ret (False, id, SID_Movement_j1)
            })
            \<comment> \<open> The previous state: a triple \<close> 
            (ret)
        ) ;
        Ret (id)
  }
)
"

definition State_Movement_j1_R where
"State_Movement_j1_R (idd::integer) = 
   (discard_state (State_Movement_j1 idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_Movement - Movement_j1_triggers) \<^esub> 
   skip
"

paragraph \<open> Avoiding \<close>
definition CS_Movement_Avoiding_sync where
"CS_Movement_Avoiding_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_Avoiding] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_Avoiding])
)"

definition Movement_Avoiding_triggers where
"Movement_Avoiding_triggers = set (
    (enumchan1 internal_Movement_C [TID_Movement_t12, TID_Movement_t5, TID_Movement_t13]) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t22, TID_Movement_t20, TID_Movement_t21, TID_Movement_t10,
     TID_Movement_t19] InOut_list) @
  (enumchans3 [turn__Movement_C] [TID_Movement_t3, TID_Movement_t14, TID_Movement_t7, TID_Movement_t8,
    TID_Movement_t2] InOut_list Chemical_Angle_list) @
  (enumchans2 [stop__Movement_C] 
    [TID_Movement_t16, TID_Movement_t17, TID_Movement_t18, TID_Movement_t15, TID_Movement_t4, 
    TID_Movement_t9] InOut_list) @
  (enumchans3 [obstacle__Movement_C] [TID_Movement_t6, TID_Movement_t11] InOut_list Location_Loc_list)
)
"

definition tids_Movement_Avoiding where
" tids_Movement_Avoiding = 
    (filter 
        (\<lambda> s. s \<notin> (set [NULLTRANSITION__Movement,TID_Movement_t0,TID_Movement_t3,TID_Movement_t12,
          TID_Movement_t16,TID_Movement_t17,TID_Movement_t14,TID_Movement_t22,TID_Movement_t18,
          TID_Movement_t20,TID_Movement_t6,TID_Movement_t21,TID_Movement_t15,TID_Movement_t5,
          TID_Movement_t13,TID_Movement_t4,TID_Movement_t10,TID_Movement_t7,TID_Movement_t19,
          TID_Movement_t9,TID_Movement_t11,TID_Movement_t8,TID_Movement_t2])) 
        ITIDS_Movement_list)"

abbreviation Other_SIDs_to_Avoiding_Movement where
"Other_SIDs_to_Avoiding_Movement \<equiv>
  set [(s, SID_Movement_Avoiding) . s \<leftarrow> (SIDS_Movement_no_Avoiding)]"

definition State_Movement_Avoiding where 
"State_Movement_Avoiding = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_Avoiding_Movement ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_Movement_Avoiding_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              guard(True); r \<leftarrow> inp_in odometer_Movement (set 
                  [(d, l). d \<leftarrow> InOut_list, l \<leftarrow> rc.core_real_list]);  
              outp set_d0_Movement (snd r);
              l \<leftarrow> inp_in get_l_Movement Location_Loc_set;
              guard(True); CALL__changeDirection_Movement id l;
              outp entered_Movement (snd (snd s), SID_Movement_Avoiding);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_Movement_t7 \<close>
                do {r \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t7, din, a). 
                            a \<leftarrow> (Chemical_Angle_list)]);
                      outp set_a_Movement (snd (snd r)); 
                      outp exit_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                      outp exited_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                      outp enter_Movement (SID_Movement_Avoiding, SID_Movement_TryingAgain);
                      outp entered_Movement (SID_Movement_Avoiding, SID_Movement_TryingAgain);
                      Ret(False, fst (snd s), SID_Movement_Avoiding)
                    } \<box>
                \<comment> \<open> T_Movement_t18 \<close>
                do {outp stop__Movement (TID_Movement_t18, din);
                    outp exit_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                    outp exited_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                    outp enter_Movement (SID_Movement_Avoiding, SID_Movement_Found);
                    outp entered_Movement (SID_Movement_Avoiding, SID_Movement_Found);
                    Ret(False, fst (snd s), SID_Movement_Avoiding)
                  } \<box>
                \<comment> \<open> T_Movement_t19 \<close>
                do {outp resume__Movement (TID_Movement_t19, din);
                    outp exit_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                    outp exited_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                    outp enter_Movement (SID_Movement_Avoiding, SID_Movement_Waiting);
                    outp entered_Movement (SID_Movement_Avoiding, SID_Movement_Waiting);
                    Ret(False, fst (snd s), SID_Movement_Avoiding)
                  } \<box>
                \<comment> \<open> T_Movement_t21 \<close>
                do {outp resume__Movement (TID_Movement_t21, din);
                    outp exit_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                    outp exited_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                    outp enter_Movement (SID_Movement_Avoiding, SID_Movement_Going);
                    outp entered_Movement (SID_Movement_Avoiding, SID_Movement_Going);
                    Ret(False, fst (snd s), SID_Movement_Avoiding)
                  } \<box>
                (exit_events_Movement (fst (snd s)) SID_Movement_Avoiding 
                   tids_Movement_Avoiding Other_SIDs_to_Avoiding_Movement)
                )
              )
            })
            \<comment> \<open> The previous state: a triple \<close> 
            (ret)
        ) ;
        Ret (id)
  }
)
"

definition State_Movement_Avoiding_R where
"State_Movement_Avoiding_R (idd::integer) = 
   (discard_state (State_Movement_Avoiding idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_Movement - Movement_Avoiding_triggers) \<^esub> 
   skip
"

paragraph \<open> TryingAgain \<close>
definition CS_Movement_TryingAgain_sync where
"CS_Movement_TryingAgain_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_TryingAgain] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_TryingAgain])
)"

definition Movement_TryingAgain_triggers where
"Movement_TryingAgain_triggers = set (
    (enumchan1 internal_Movement_C [TID_Movement_t12, TID_Movement_t5, TID_Movement_t13]) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t22, TID_Movement_t20, TID_Movement_t21, TID_Movement_t10,
     TID_Movement_t19] InOut_list) @
  (enumchans3 [turn__Movement_C] [TID_Movement_t3, TID_Movement_t14, TID_Movement_t7, TID_Movement_t8,
    TID_Movement_t2] InOut_list Chemical_Angle_list) @
  (enumchans2 [stop__Movement_C] 
    [TID_Movement_t16, TID_Movement_t17, TID_Movement_t18, TID_Movement_t15, TID_Movement_t4, 
    TID_Movement_t9] InOut_list) @
  (enumchans3 [obstacle__Movement_C] [TID_Movement_t6, TID_Movement_t11] InOut_list Location_Loc_list)
)
"

definition tids_Movement_TryingAgain where
" tids_Movement_TryingAgain = 
    (filter 
        (\<lambda> s. s \<notin> (set [NULLTRANSITION__Movement,TID_Movement_t0,TID_Movement_t3,TID_Movement_t12,
          TID_Movement_t16,TID_Movement_t17,TID_Movement_t14,TID_Movement_t22,TID_Movement_t18,
          TID_Movement_t20,TID_Movement_t6,TID_Movement_t21,TID_Movement_t15,TID_Movement_t5,
          TID_Movement_t13,TID_Movement_t4,TID_Movement_t10,TID_Movement_t7,TID_Movement_t19,
          TID_Movement_t9,TID_Movement_t11,TID_Movement_t8,TID_Movement_t2])) 
        ITIDS_Movement_list)"

abbreviation Other_SIDs_to_TryingAgain_Movement where
"Other_SIDs_to_TryingAgain_Movement \<equiv>
  set [(s, SID_Movement_TryingAgain) . s \<leftarrow> (SIDS_Movement_no_TryingAgain)]"

definition State_Movement_TryingAgain where 
"State_Movement_TryingAgain = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_TryingAgain_Movement ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_Movement_TryingAgain_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {a \<leftarrow> inp_in get_a_Movement Chemical_Angle_set;
              guard(True); CALL__move_Movement id const_Movement_lv a; 
              outp entered_Movement (snd (snd s), SID_Movement_TryingAgain);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_Movement_t8 \<close>
                do {r \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t7, din, a). 
                            a \<leftarrow> (Chemical_Angle_list)]);
                      outp set_a_Movement (snd (snd r)); 
                      outp exit_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                      outp exited_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                      outp enter_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                      Ret(True, fst (snd s), SID_Movement_TryingAgain)
                    } \<box>
                \<comment> \<open> T_Movement_t9 \<close>
                do {outp stop__Movement (TID_Movement_t9, din);
                    outp exit_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                    outp exited_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                    outp enter_Movement (SID_Movement_TryingAgain, SID_Movement_Found);
                    outp entered_Movement (SID_Movement_TryingAgain, SID_Movement_Found);
                    Ret(False, fst (snd s), SID_Movement_TryingAgain)
                  } \<box>
                \<comment> \<open> T_Movement_t10 \<close>
                do {outp resume__Movement (TID_Movement_t10, din);
                    outp exit_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                    outp exited_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                    outp enter_Movement (SID_Movement_TryingAgain, SID_Movement_Waiting);
                    outp entered_Movement (SID_Movement_TryingAgain, SID_Movement_Waiting);
                    Ret(False, fst (snd s), SID_Movement_TryingAgain)
                  } \<box>
                \<comment> \<open> T_Movement_t11 \<close>
                do {r \<leftarrow> inp_in obstacle__Movement (set [(TID_Movement_t11, din, l). 
                        l \<leftarrow> Location_Loc_list]);
                      outp set_l_Movement (snd (snd r)) ; 
                    outp exit_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                    outp exited_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                    guard(True); r \<leftarrow> inp_in odometer_Movement (set 
                          [(d, l). d \<leftarrow> InOut_list, l \<leftarrow> rc.core_real_list]);
                    outp set_d1_Movement (snd r);
                    outp enter_Movement (SID_Movement_TryingAgain, SID_Movement_AvoidingAgain);
                    outp entered_Movement (SID_Movement_TryingAgain, SID_Movement_AvoidingAgain);
                    Ret(False, fst (snd s), SID_Movement_TryingAgain)
                  } \<box>
                (exit_events_Movement (fst (snd s)) SID_Movement_TryingAgain 
                   tids_Movement_TryingAgain Other_SIDs_to_TryingAgain_Movement)
                )
              )
            })
            \<comment> \<open> The previous state: a triple \<close> 
            (ret)
        ) ;
        Ret (id)
  }
)
"

definition State_Movement_TryingAgain_R where
"State_Movement_TryingAgain_R (idd::integer) = 
   (discard_state (State_Movement_TryingAgain idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_Movement - Movement_TryingAgain_triggers) \<^esub> 
   skip
"

paragraph \<open> AvoidingAgain \<close>
definition CS_Movement_AvoidingAgain_sync where
"CS_Movement_AvoidingAgain_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_AvoidingAgain] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_AvoidingAgain])
)"

definition Movement_AvoidingAgain_triggers where
"Movement_AvoidingAgain_triggers = set (
    (enumchan1 internal_Movement_C [TID_Movement_t12, TID_Movement_t5, TID_Movement_t13]) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t22, TID_Movement_t20, TID_Movement_t21, TID_Movement_t10,
     TID_Movement_t19] InOut_list) @
  (enumchans3 [turn__Movement_C] [TID_Movement_t3, TID_Movement_t14, TID_Movement_t7, TID_Movement_t8,
    TID_Movement_t2] InOut_list Chemical_Angle_list) @
  (enumchans2 [stop__Movement_C] 
    [TID_Movement_t16, TID_Movement_t17, TID_Movement_t18, TID_Movement_t15, TID_Movement_t4, 
    TID_Movement_t9] InOut_list) @
  (enumchans3 [obstacle__Movement_C] [TID_Movement_t6, TID_Movement_t11] InOut_list Location_Loc_list)
)
"

definition tids_Movement_AvoidingAgain where
" tids_Movement_AvoidingAgain = 
    (filter 
        (\<lambda> s. s \<notin> (set [NULLTRANSITION__Movement,TID_Movement_t0,TID_Movement_t3,TID_Movement_t12,
          TID_Movement_t16,TID_Movement_t17,TID_Movement_t14,TID_Movement_t22,TID_Movement_t18,
          TID_Movement_t20,TID_Movement_t6,TID_Movement_t21,TID_Movement_t15,TID_Movement_t5,
          TID_Movement_t13,TID_Movement_t4,TID_Movement_t10,TID_Movement_t7,TID_Movement_t19,
          TID_Movement_t9,TID_Movement_t11,TID_Movement_t8,TID_Movement_t2])) 
        ITIDS_Movement_list)"

abbreviation Other_SIDs_to_AvoidingAgain_Movement where
"Other_SIDs_to_AvoidingAgain_Movement \<equiv>
  set [(s, SID_Movement_AvoidingAgain) . s \<leftarrow> (SIDS_Movement_no_AvoidingAgain)]"

definition State_Movement_AvoidingAgain where 
"State_Movement_AvoidingAgain = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_AvoidingAgain_Movement ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_Movement_AvoidingAgain_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_Movement (snd (snd s), SID_Movement_AvoidingAgain);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_Movement_t12 \<close>
                do {outp internal_Movement TID_Movement_t12;
                      outp exit_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                      outp exited_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                      outp enter_Movement (SID_Movement_AvoidingAgain, SID_Movement_Avoiding);
                      outp entered_Movement (SID_Movement_AvoidingAgain, SID_Movement_Avoiding);
                      Ret(False, fst (snd s), SID_Movement_AvoidingAgain)
                    } \<box>
                \<comment> \<open> T_Movement_t17 \<close>
                do {outp stop__Movement (TID_Movement_t17, din);
                    outp exit_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                    outp exited_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                    outp enter_Movement (SID_Movement_AvoidingAgain, SID_Movement_Found);
                    outp entered_Movement (SID_Movement_AvoidingAgain, SID_Movement_Found);
                    Ret(False, fst (snd s), SID_Movement_AvoidingAgain)
                  } \<box>
                \<comment> \<open> T_Movement_t22 \<close>
                do {outp resume__Movement (TID_Movement_t22, din);
                    outp exit_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                    outp exited_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                    outp enter_Movement (SID_Movement_AvoidingAgain, SID_Movement_Waiting);
                    outp entered_Movement (SID_Movement_AvoidingAgain, SID_Movement_Waiting);
                    Ret(False, fst (snd s), SID_Movement_AvoidingAgain)
                  } \<box>
                \<comment> \<open> T_Movement_t13 \<close>
                do {outp internal_Movement TID_Movement_t13;
                      outp exit_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                      outp exited_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                      outp enter_Movement (SID_Movement_AvoidingAgain, SID_Movement_GettingOut);
                      outp entered_Movement (SID_Movement_AvoidingAgain, SID_Movement_GettingOut);
                      Ret(False, fst (snd s), SID_Movement_AvoidingAgain)
                    } \<box>
                (exit_events_Movement (fst (snd s)) SID_Movement_AvoidingAgain 
                   tids_Movement_AvoidingAgain Other_SIDs_to_AvoidingAgain_Movement)
                )
              )
            })
            \<comment> \<open> The previous state: a triple \<close> 
            (ret)
        ) ;
        Ret (id)
  }
)
"

definition State_Movement_AvoidingAgain_R where
"State_Movement_AvoidingAgain_R (idd::integer) = 
   (discard_state (State_Movement_AvoidingAgain idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_Movement - Movement_AvoidingAgain_triggers) \<^esub> 
   skip
"

paragraph \<open> GettingOut \<close>
definition CS_Movement_GettingOut_sync where
"CS_Movement_GettingOut_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_GettingOut] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_GettingOut])
)"

definition Movement_GettingOut_triggers where
"Movement_GettingOut_triggers = set (
    (enumchan1 internal_Movement_C [TID_Movement_t12, TID_Movement_t5, TID_Movement_t13]) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t22, TID_Movement_t20, TID_Movement_t21, TID_Movement_t10,
     TID_Movement_t19] InOut_list) @
  (enumchans3 [turn__Movement_C] [TID_Movement_t3, TID_Movement_t14, TID_Movement_t7, TID_Movement_t8,
    TID_Movement_t2] InOut_list Chemical_Angle_list) @
  (enumchans2 [stop__Movement_C] 
    [TID_Movement_t16, TID_Movement_t17, TID_Movement_t18, TID_Movement_t15, TID_Movement_t4, 
    TID_Movement_t9] InOut_list) @
  (enumchans3 [obstacle__Movement_C] [TID_Movement_t6, TID_Movement_t11] InOut_list Location_Loc_list)
)
"

definition tids_Movement_GettingOut where
" tids_Movement_GettingOut = 
    (filter 
        (\<lambda> s. s \<notin> (set [NULLTRANSITION__Movement,TID_Movement_t0,TID_Movement_t3,TID_Movement_t12,
          TID_Movement_t16,TID_Movement_t17,TID_Movement_t14,TID_Movement_t22,TID_Movement_t18,
          TID_Movement_t20,TID_Movement_t6,TID_Movement_t21,TID_Movement_t15,TID_Movement_t5,
          TID_Movement_t13,TID_Movement_t4,TID_Movement_t10,TID_Movement_t7,TID_Movement_t19,
          TID_Movement_t9,TID_Movement_t11,TID_Movement_t8,TID_Movement_t2])) 
        ITIDS_Movement_list)"

abbreviation Other_SIDs_to_GettingOut_Movement where
"Other_SIDs_to_GettingOut_Movement \<equiv>
  set [(s, SID_Movement_GettingOut) . s \<leftarrow> (SIDS_Movement_no_GettingOut)]"

definition State_Movement_GettingOut where 
"State_Movement_GettingOut = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_GettingOut_Movement ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_Movement_GettingOut_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              guard(True); CALL__shortRandomWalk_Movement id; 
              outp entered_Movement (snd (snd s), SID_Movement_GettingOut);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_Movement_t14 \<close>
                do {r \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t14, din, a). 
                            a \<leftarrow> (Chemical_Angle_list)]);
                      outp set_a_Movement (snd (snd r)); 
                      outp exit_Movement (SID_Movement_GettingOut, SID_Movement_GettingOut);
                      outp exited_Movement (SID_Movement_GettingOut, SID_Movement_GettingOut);
                      outp enter_Movement (SID_Movement_GettingOut, SID_Movement_Going);
                      outp entered_Movement (SID_Movement_GettingOut, SID_Movement_Going);
                      Ret(False, fst (snd s), SID_Movement_GettingOut)
                    } \<box>
                \<comment> \<open> T_Movement_t16 \<close>
                do {outp stop__Movement (TID_Movement_t16, din);
                    outp exit_Movement (SID_Movement_GettingOut, SID_Movement_GettingOut);
                    outp exited_Movement (SID_Movement_GettingOut, SID_Movement_GettingOut);
                    outp enter_Movement (SID_Movement_GettingOut, SID_Movement_Found);
                    outp entered_Movement (SID_Movement_GettingOut, SID_Movement_Found);
                    Ret(False, fst (snd s), SID_Movement_GettingOut)
                  } \<box>
                \<comment> \<open> T_Movement_t20 \<close>
                do {outp resume__Movement (TID_Movement_t20, din);
                    outp exit_Movement (SID_Movement_GettingOut, SID_Movement_GettingOut);
                    outp exited_Movement (SID_Movement_GettingOut, SID_Movement_GettingOut);
                    outp enter_Movement (SID_Movement_GettingOut, SID_Movement_Waiting);
                    outp entered_Movement (SID_Movement_GettingOut, SID_Movement_Waiting);
                    Ret(False, fst (snd s), SID_Movement_GettingOut)
                  } \<box>
                (exit_events_Movement (fst (snd s)) SID_Movement_GettingOut 
                   tids_Movement_GettingOut Other_SIDs_to_GettingOut_Movement)
                )
              )
            })
            \<comment> \<open> The previous state: a triple \<close> 
            (ret)
        ) ;
        Ret (id)
  }
)
"

definition State_Movement_GettingOut_R where
"State_Movement_GettingOut_R (idd::integer) = 
   (discard_state (State_Movement_GettingOut idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_Movement - Movement_GettingOut_triggers) \<^esub> 
   skip
"

subsubsection \<open> State machine \<close>
definition flow_events_Movement_stm_to_nodes where
"flow_events_Movement_stm_to_nodes = (
 let nodes = [SID_Movement_Waiting,SID_Movement_Going,SID_Movement_Found,SID_Movement_j1,
    SID_Movement_Avoiding,SID_Movement_TryingAgain,SID_Movement_AvoidingAgain,
    SID_Movement_GettingOut]
 in set (
      enumchans2 [enter_Movement_C, entered_Movement_C,exit_Movement_C,exited_Movement_C] 
          (filter (\<lambda> s. s \<notin> set nodes) SIDS_Movement_list) nodes
  )
)"

definition STM_Movement_1 where
"STM_Movement_1 (idd::integer) =
  (State_Movement_AvoidingAgain_R(idd)  
    \<parallel>\<^bsub> CS_Movement_AvoidingAgain_sync \<inter> CS_Movement_GettingOut_sync \<^esub> 
  State_Movement_GettingOut_R(idd))
"

definition STM_Movement_2 where
"STM_Movement_2 (idd::integer) =
  (State_Movement_TryingAgain_R(idd)  
    \<parallel>\<^bsub> CS_Movement_TryingAgain_sync \<inter> 
      (CS_Movement_AvoidingAgain_sync \<union> CS_Movement_GettingOut_sync) \<^esub> 
  STM_Movement_1(idd))
"

definition STM_Movement_3 where
"STM_Movement_3 (idd::integer) =
  (State_Movement_Avoiding_R(idd)  
    \<parallel>\<^bsub> CS_Movement_Avoiding_sync \<inter> 
      (CS_Movement_TryingAgain_sync \<union> 
        (CS_Movement_AvoidingAgain_sync \<union> CS_Movement_GettingOut_sync)) \<^esub> 
  STM_Movement_2(idd))
"

definition STM_Movement_4 where
"STM_Movement_4 (idd::integer) =
  (State_Movement_j1_R(idd)  
    \<parallel>\<^bsub> CS_Movement_j1_sync \<inter>
      (CS_Movement_Avoiding_sync \<union>
        (CS_Movement_TryingAgain_sync \<union> 
          (CS_Movement_AvoidingAgain_sync \<union> CS_Movement_GettingOut_sync))) \<^esub> 
  STM_Movement_3(idd))
"

definition STM_Movement_5 where
"STM_Movement_5 (idd::integer) =
  (State_Movement_Found_R(idd)  
    \<parallel>\<^bsub> CS_Movement_Found_sync \<inter>
      (CS_Movement_j1_sync \<union>
        (CS_Movement_Avoiding_sync \<union>
          (CS_Movement_TryingAgain_sync \<union> 
            (CS_Movement_AvoidingAgain_sync \<union> CS_Movement_GettingOut_sync)))) \<^esub> 
  STM_Movement_4(idd))
"

definition STM_Movement_6 where
"STM_Movement_6 (idd::integer) =
  (State_Movement_Going_R(idd)  
    \<parallel>\<^bsub> CS_Movement_Going_sync \<inter>
      (CS_Movement_Found_sync \<union>
        (CS_Movement_j1_sync \<union>
          (CS_Movement_Avoiding_sync \<union>
            (CS_Movement_TryingAgain_sync \<union> 
              (CS_Movement_AvoidingAgain_sync \<union> CS_Movement_GettingOut_sync))))) \<^esub> 
  STM_Movement_5(idd))
"

definition STM_Movement_7 where
"STM_Movement_7 (idd::integer) =
  (State_Movement_Waiting_R(idd)  
    \<parallel>\<^bsub> CS_Movement_Waiting_sync \<inter>
      (CS_Movement_Going_sync \<union>
        (CS_Movement_Found_sync \<union>
          (CS_Movement_j1_sync \<union>
            (CS_Movement_Avoiding_sync \<union>
              (CS_Movement_TryingAgain_sync \<union> 
                (CS_Movement_AvoidingAgain_sync \<union> CS_Movement_GettingOut_sync)))))) \<^esub> 
  STM_Movement_6(idd))
"

definition STM_Movement where
"STM_Movement (idd::integer) = 
   (I_Movement_i1(idd))
    \<parallel>\<^bsub> flow_events_Movement_stm_to_nodes \<^esub> 
   STM_Movement_7(idd)
"

definition Movement_opt_0_internal_set where
"Movement_opt_0_internal_set = 
  set ((enumchans1 [internal_Movement_C] [TID_Movement_t1, TID_Movement_t5]) @ 
      (enumchans2 [stop__Movement_C] 
          [TID_Movement_t18, TID_Movement_t17, TID_Movement_t16, TID_Movement_t9, TID_Movement_t15,
          TID_Movement_t4] InOut_list) @
       (enumchans3 [turn__Movement_C] 
          [TID_Movement_t3, TID_Movement_t2, TID_Movement_t14, TID_Movement_t7, TID_Movement_t8] 
          InOut_list Chemical_Angle_list) @
       (enumchans2 [resume__Movement_C] 
          [TID_Movement_t21, TID_Movement_t10, TID_Movement_t22, TID_Movement_t20, TID_Movement_t0,
          TID_Movement_t19] InOut_list) @
       (enumchans3 [obstacle__Movement_C] [TID_Movement_t6, TID_Movement_t11] 
          InOut_list Location_Loc_list)
)"

definition Movement_opt_1_internal_set where
"Movement_opt_1_internal_set = 
  set ((enumchans1 [internal_Movement_C] [TID_Movement_t12, TID_Movement_t13]) @
       (enumchans1 [set_d0_Movement_C, set_d1_Movement_C] rc.core_real_list)
)"

definition MemorySTM_opt_Movement where
"MemorySTM_opt_Movement (idd::integer) = 
  (par_hide
    (discard_state (Movement_Memory_opt_d1 (0)))
    Movement_d1_events 
    (par_hide
      (discard_state (Movement_Memory_opt_d0 (0)))
      Movement_d0_events
      (hide 
        (
          (hide
            (
              (par_hide
                (discard_state (Movement_Memory_opt_l (Location_Loc_left)))
                Movement_l_events
                (par_hide 
                  (discard_state (Movement_Memory_opt_a Chemical_Angle_Left)) 
                  Movement_a_events 
                  (STM_Movement idd)
                )
              )
              \<parallel>\<^bsub> Movement_opt_0_internal_set \<^esub>
              (discard_state (Movement_MemoryTransitions_opt_0 idd))
            )
            (set [internal_Movement_C TID_Movement_t5, internal_Movement_C TID_Movement_t1])
          )
          \<parallel>\<^bsub> Movement_opt_1_internal_set \<^esub> 
          (discard_state (Movement_MemoryTransitions_opt_1 idd))
        )
        (set (enumchans1 [internal_Movement_C] [TID_Movement_t12, TID_Movement_t13]))
      )
    )
  )
"

definition rename_Movement_events where
"rename_Movement_events = 
  concat (
    (enumchan2 (forget_first2 obstacle__Movement_C obstacle_Movement_C TIDS_Movement_list) 
            InOut_list Location_Loc_list) @
    (enumchan2 (forget_first2 odometer__Movement_C odometer_Movement_C TIDS_Movement_list) 
            InOut_list rc.core_real_list) @
    (enumchan1 (forget_first resume__Movement_C resume_Movement_C TIDS_Movement_list) 
            InOut_list) @
    (enumchan2 (forget_first2 turn__Movement_C turn_Movement_C TIDS_Movement_list) 
            InOut_list Chemical_Angle_list) @
    (enumchan1 (forget_first stop__Movement_C stop_Movement_C TIDS_Movement_list) 
            InOut_list) @
    (enumchan1 (forget_first flag__Movement_C flag_Movement_C TIDS_Movement_list) 
            InOut_list)
  )
"

definition rename_Movement_events_others where
"rename_Movement_events_others = 
  (enumchanp1 terminate_Movement_C [()]) @
  (enumchansp1 [get_l_Movement_C, set_l_Movement_C] Location_Loc_list) @
  (enumchansp1 [get_a_Movement_C, set_a_Movement_C] Chemical_Angle_list) @
  (enumchansp1 [get_d0_Movement_C, set_d0_Movement_C] rc.core_real_list) @
  (enumchansp1 [get_d1_Movement_C, set_d1_Movement_C] rc.core_real_list) @
  (enumchansp2 [obstacle_Movement_C] InOut_list Location_Loc_list) @
  (enumchansp2 [odometer_Movement_C] InOut_list rc.core_real_list) @
  (enumchansp2 [turn_Movement_C] InOut_list Chemical_Angle_list) @
  (enumchansp1 [resume_Movement_C, stop_Movement_C, flag_Movement_C] InOut_list) @
  (enumchansp2 [enter_Movement_C, entered_Movement_C, exit_Movement_C, exited_Movement_C] 
    SIDS_Movement_list SIDS_Movement_list) @
  (enumchansp1 [internal_Movement_C] TIDS_Movement_list) @
  (enumchansp1 [changeDirectionCall_Movement_C] Location_Loc_list) @
  (enumchansp1 [randomeWalkCall_Movement_C, shortRandomWalkCall_Movement_C] [()]) @
  (enumchansp2 [moveCall_Movement_C] rc.core_real_list Chemical_Angle_list)
"

definition rename_MemorySTM_opt_Movement where
"rename_MemorySTM_opt_Movement idd = 
  rename (set (rename_Movement_events @ rename_Movement_events_others)) 
    (MemorySTM_opt_Movement idd)
"

definition AUX_opt_Movement where
"AUX_opt_Movement (idd::integer) = 
  (hide 
    ( 
      (rename_MemorySTM_opt_Movement idd) \<lbrakk> set [terminate_Movement_C ()] \<Zrres> skip
    )
    Movement_MachineInternalEvents
  )
"

definition D__Movement where
"D__Movement (idd::integer) = 
  hide (AUX_opt_Movement idd) internal_events_Movement
"

subsection \<open> MicroController \<close>
chantype Chan_MicroCtrl =
  terminate_MicroController :: unit
  obstacle_MicroController :: "InOut \<times> Location_Loc"
  resume_MicroController :: "InOut"
  turn_MicroController :: "InOut \<times> Chemical_Angle"
  odometer_MicroController :: "InOut \<times> core_real"
  stop_MicroController :: "InOut"
  flag_MicroController :: "InOut"
(* *)
  randomeWalkCall_MicroController :: unit
  moveCall_MicroController :: "core_real \<times> Chemical_Angle"
  shortRandomWalkCall_MicroController :: unit

subsubsection \<open> Memory \<close>
definition Memory_MicroController where
"Memory_MicroController (idd::integer) = skip"

subsubsection \<open> Controller \<close>

definition rename_MicroController_Movement_events where
"rename_MicroController_Movement_events = 
  (enumchanp2_1 (terminate_Movement_C,terminate_MicroController_C) [()]) @
  (enumchansp2_1 [(resume_Movement_C, resume_MicroController_C)] InOut_list) @
  (enumchansp2_2 [(turn_Movement_C, turn_MicroController_C)] InOut_list Chemical_Angle_list) @
  (enumchansp2_2 [(obstacle_Movement_C, obstacle_MicroController_C)] InOut_list Location_Loc_list) @
  (enumchansp2_2 [(odometer_Movement_C, odometer_MicroController_C)] InOut_list rc.core_real_list) @
  (enumchansp2_1 [(stop_Movement_C, stop_MicroController_C)] InOut_list) @
  (enumchansp2_1 [(flag_Movement_C, flag_MicroController_C)] InOut_list)
"

definition rename_D__Movement where
  "rename_D__Movement idd = rename (set rename_MicroController_Movement_events) (D__Movement idd)"

definition D__MicroController where
"D__MicroController (idd::integer) = 
  (par_hide
    (rename_D__Movement idd)
    {}
    (discard_state (Memory_MicroController idd))
  )  \<lbrakk> set [terminate_MicroController_C ()] \<Zrres> skip
"
*)

export_code
  Movement_Memory_opt_d0
  Movement_MemoryTransitions_opt_0
  Movement_MemoryTransitions_opt_1
  I_Movement_i1
(*
  State_Movement_Waiting
  State_Movement_Waiting_R
  State_Movement_Analysis_R
  State_Movement_GasDetected_R
  State_Movement_j1_R
  State_Movement_Reading_R
  MemorySTM_opt_Movement
  AUX_opt_Movement
  D__Movement
*)
in Haskell 
  (* module_name Movement *)
  file_prefix RoboChart_ChemicalDetector 
  (string_classes) 




subsection \<open> Module \<close>
chantype Chan_mod0 =
(* terminates of MicroController are mapped to it *)
  terminate_mod0 :: unit 
(* variable channels: set_x and get_x of Movement and stm1 are mapped to these channels *)
  set_x_mod0 :: core_int
  get_x_mod0 :: core_int
(* shared variable channels *)
  set_EXT_x_mod0_MicroController :: core_int
(* e1 of Movement is mapped to it *)
  e1_mod0 :: "InOut \<times> core_int"
(* e2 of stm1 is mapped to it *)
  e2_mod0 :: "InOut"

definition Memory_mod0 where
"Memory_mod0 = loop (\<lambda> id::integer.
  ( do {x \<leftarrow> inp_in set_x_mod0 rc.core_int_set; 
        outp set_EXT_x_mod0_MicroController x; Ret (id)}
  )
)"

(*
definition rename_mod0_MicroController_events where
"rename_mod0_MicroController_events = 
  [(terminate_MicroController_C (), terminate_mod0_C ())] @
  [(set_x_MicroController_C n, set_x_mod0_C n). n \<leftarrow> rc.core_int_list] @
  [(get_x_MicroController_C n, get_x_mod0_C n). n \<leftarrow> rc.core_int_list] @
  [(e1_MicroController_C (d, n), e1_mod0_C (d, n)). d \<leftarrow> InOut_list, n \<leftarrow> rc.core_int_list] @
  [(e2_MicroController_C (d), e2_mod0_C (d)). d \<leftarrow> InOut_list] @
  [(set_EXT_x_MicroController_C n, set_EXT_x_mod0_MicroController_C n). n \<leftarrow> rc.core_int_list]
"
*)
definition rename_mod0_MicroController_events where
"rename_mod0_MicroController_events = 
  (enumchanp2_1 (terminate_MicroController_C,terminate_mod0_C) [()]) @
  (enumchansp2_1 [(set_x_MicroController_C, set_x_mod0_C), (get_x_MicroController_C, get_x_mod0_C), 
      (set_EXT_x_MicroController_C, set_EXT_x_mod0_MicroController_C)] rc.core_int_list) @
  (enumchanp2_1 (e2_MicroController_C, e2_mod0_C) InOut_list) @
  (enumchanp2_2 (e1_MicroController_C, e1_mod0_C) InOut_list rc.core_int_list)
"

definition rename_D__MicroController where
"rename_D__MicroController idd = rename (set rename_mod0_MicroController_events) (D__MicroController idd)"

definition "mod0_set_x_events = set (
  enumchan1 set_x_mod0_C  rc.core_int_list
)"

definition "mod0_get_x_events = set (
  enumchan1 get_x_mod0_C  rc.core_int_list
)"

definition "mod0_set_EXT_x_events = set (
  enumchan1 set_EXT_x_mod0_MicroController_C  rc.core_int_list
)"

definition D__ctr_mem where
"D__ctr_mem (idd::integer) = (
              (rename_D__MicroController idd) 
              \<parallel>\<^bsub> (mod0_set_x_events \<union> mod0_set_EXT_x_events) \<^esub> 
              (discard_state (Memory_mod0 idd))
            )"

definition D__mod0 where
"D__mod0 (idd::integer) = 
  (hide
    (
      (skip \<parallel>\<^bsub> {} \<^esub> 
        (
          hide 
            (
              (rename_D__MicroController idd) 
              \<parallel>\<^bsub> (mod0_set_x_events \<union> mod0_set_EXT_x_events) \<^esub> 
              (discard_state (Memory_mod0 idd))
            )
            ((mod0_set_x_events \<union> mod0_get_x_events) \<union> mod0_set_EXT_x_events)
        )
      )  \<lbrakk> set [terminate_mod0_C ()] \<Zrres> skip
    )
    (set [terminate_mod0_C ()])
  )
"

subsection \<open> Export code \<close>
export_code
  Movement_Memory_opt_x
  Movement_Memory_opt_l
  Movement_MemoryTransitions_opt_0
  Movement_MemoryTransitions_opt_1
  I_Movement_i0
  State_Movement_s0
  State_Movement_s0_R
  STM_Movement
  MemorySTM_opt_Movement 
  rename_MemorySTM_opt_Movement
  D__Movement 
  stm1_Memory_opt_x
  stm1_MemoryTransitions_opt_0
  I_stm1_i0
  State_stm1_s0
  State_stm1_s0_R
  STM_stm1
  MemorySTM_opt_stm1
  D__stm1
  rename_D__Movement
  rename_D__stm1
  D__MicroController
  rename_D__MicroController
  D__ctr_mem
  D__mod0
  in Haskell 
  (* module_name RoboChart_basic *)
  file_prefix RoboChart_basic 
  (string_classes) 

generate_file \<open>code/RoboChart_basic/Simulate.hs\<close> = 
\<open>module Simulate (simulate) where
import qualified Interaction_Trees;
import qualified Partial_Fun;

isPrefixOf              :: (Eq a) => [a] -> [a] -> Bool;
isPrefixOf [] _         =  True;
isPrefixOf _  []        =  False;
isPrefixOf (x:xs) (y:ys)=  x == y && isPrefixOf xs ys;

removeSubstr :: String -> String -> String;
removeSubstr w "" = "";
removeSubstr w s@(c:cs) = (if w `isPrefixOf` s then Prelude.drop (Prelude.length w) s else c : removeSubstr w cs);

simulate_cnt :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Prelude.Int -> Interaction_Trees.Itree e s -> Prelude.IO ();
simulate_cnt n (Interaction_Trees.Ret x) = Prelude.putStrLn ("Terminated: " ++ Prelude.show x);
simulate_cnt n (Interaction_Trees.Sil p) =
  do { if (n == 0) then Prelude.putStrLn "Internal Activity..." else return ();
       if (n >= 2000) then do { Prelude.putStr "Many steps (> 2000); Continue? [Y/N]"; q <- Prelude.getLine;
                              if (q == "Y") then simulate_cnt 0 p else Prelude.putStrLn "Ended early.";
                            }
                    else simulate_cnt (n + 1) p
     };
simulate_cnt n (Interaction_Trees.Vis (Partial_Fun.Pfun_of_alist [])) = Prelude.putStrLn "Deadlocked.";
simulate_cnt n t@(Interaction_Trees.Vis (Partial_Fun.Pfun_of_alist m)) =
  do { Prelude.putStrLn ("Events:" ++ Prelude.concat (map (\(n, e) -> " (" ++ Prelude.show n ++ ") " ++ removeSubstr "_C" e ++ ";") (zip [1..] (map (Prelude.show . fst) m))));
       e <- Prelude.getLine;
       case (Prelude.reads e) of
         []       -> if (Prelude.length m == 1)
                       then simulate_cnt 0 (snd (m !! (0)))
                       else do { Prelude.putStrLn "No parse"; simulate_cnt n t }
         [(v, _)] -> if (v > Prelude.length m)
                       then do { Prelude.putStrLn "Rejected"; simulate_cnt n t }
                       else simulate_cnt 0 (snd (m !! (v - 1)))
     };

simulate :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Interaction_Trees.Itree e s -> Prelude.IO ();
simulate = simulate_cnt 0;
\<close>

export_generated_files \<open>code/RoboChart_basic/Simulate.hs\<close>

end
