section \<open> Simulation of a very basic RoboChart model \<close>
text \<open> This theory aims for simulation of a trivial RoboChart model based on its CSP
 semantics. We use the @{term "rename"} operator for renaming.
\<close>
theory RoboChart_ChemicalDetector_autonomous
  imports "RoboChart_ChemicalDetector_autonomous_general"
    "RoboChart_ChemicalDetector_autonomous_maincontroller"
    "RoboChart_ChemicalDetector_autonomous_microcontroller"
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
definition "SIDS_Movement_no_GasDetected = (removeAll SID_Movement_Found SIDS_Movement_list)"
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
definition "TIDS_Movement_list = enum_TIDS_Movement_inst.enum_TIDS_Movement"
*)
definition "TIDS_Movement_list = [NULLTRANSITION__Movement, TID_Movement_t0,
  TID_Movement_t1, TID_Movement_t2, TID_Movement_t3, TID_Movement_t4, TID_Movement_t5,
  TID_Movement_t6, TID_Movement_t7, TID_Movement_t8, TID_Movement_t9, TID_Movement_t10, 
  TID_Movement_t11, TID_Movement_t12, TID_Movement_t13, TID_Movement_t14, TID_Movement_t15, 
  TID_Movement_t16, TID_Movement_t17, TID_Movement_t18, TID_Movement_t19, TID_Movement_t20, 
  TID_Movement_t21, TID_Movement_t22]"

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
  moveCall :: "core_real \<times> Chemical_Angle"
  shortRandomWalkCall :: unit

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
  (enumchans3 [obstacle__Movement_C] int_int_tids_Movement [din, dout] Location_Loc_list) @
  (enumchans3 [odometer__Movement_C] int_int_tids_Movement [din, dout] rc.core_real_list) @
  (enumchans2 [resume__Movement_C, stop__Movement_C, flag__Movement_C] 
    int_int_tids_Movement [din, dout]) @
  (enumchans3 [turn__Movement_C] int_int_tids_Movement [din, dout] Chemical_Angle_list) @
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
  (enumchans3 [obstacle__Movement_C] [TID_Movement_t6, TID_Movement_t11] [din, dout] Location_Loc_list) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t22, TID_Movement_t20, TID_Movement_t21, TID_Movement_t10, 
    TID_Movement_t19] [din, dout]) @
  (enumchans2 [stop__Movement_C] 
    [TID_Movement_t16, TID_Movement_t17, TID_Movement_t18, TID_Movement_t15, TID_Movement_t4, 
    TID_Movement_t9] [din, dout]) @
  (enumchans3 [turn__Movement_C] [TID_Movement_t3, TID_Movement_t14, TID_Movement_t7, 
    TID_Movement_t8, TID_Movement_t2] [din, dout] Chemical_Angle_list) @
  (enumchan1 internal_Movement_C [TID_Movement_t12, TID_Movement_t5, TID_Movement_t13])
)
"

(* empty list *)
definition tids_Movement_Waiting where
" tids_Movement_Waiting = 
    (filter 
        (\<lambda> s. s \<notin> (set ITIDS_Movement_list)) 
        ITIDS_Movement_list)"

abbreviation Other_SIDs_to_Waiting_Movement where
"Other_SIDs_to_Waiting_Movement \<equiv>
  set [(s, SID_Movement_Waiting) . s \<leftarrow> (SIDS_Movement_no_Waiting)]"

definition 
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
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_Movement_t2 \<close>
                do {t \<leftarrow> inp_in gas__Movement (set [(TID_Movement_t2, din, gs). 
                                gs \<leftarrow> (lseq_gassensor_enum)]) ;
                      outp set_gs_Movement (snd (snd t)) ; 
                      outp exit_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      outp exited_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      outp enter_Movement (SID_Movement_Waiting, SID_Movement_Analysis);
                      outp entered_Movement (SID_Movement_Waiting, SID_Movement_Analysis);
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

paragraph \<open> Analysis \<close>
definition CS_Movement_Analysis_sync where
"CS_Movement_Analysis_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_Analysis] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_Analysis])
)"

definition Movement_Analysis_triggers where
"Movement_Analysis_triggers = set (
  (enumchan1 internal_Movement_C 
    [TID_Movement_t3, TID_Movement_t4,
     TID_Movement_t8, TID_Movement_t9a]) @
  (enumchans3 [gas__Movement_C] 
    [TID_Movement_t0, TID_Movement_t2] 
    [din, dout] 
    (lseq_gassensor_enum))
)
"

definition tids_Movement_Analysis where
" tids_Movement_Analysis = 
    (filter 
        (\<lambda> s. s \<notin> {NULLTRANSITION__Movement, TID_Movement_t9a,
          TID_Movement_t8, TID_Movement_t4, TID_Movement_t3, 
          TID_Movement_t2, TID_Movement_t0}) 
        ITIDS_Movement_list)"

abbreviation Other_SIDs_to_Analysis_Movement where
"Other_SIDs_to_Analysis_Movement \<equiv> 
  set [(s, SID_Movement_Analysis) . s \<leftarrow> (SIDS_Movement_no_Analysis)]"

definition State_Movement_Analysis where 
"State_Movement_Analysis = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_Analysis_Movement ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_Movement_Analysis_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              gs \<leftarrow> inp_in get_gs_Movement (set (lseq_gassensor_enum));
              outp set_st_Movement (Chemical_analysis gs);
              outp entered_Movement (snd (snd s), SID_Movement_Analysis);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_Movement_t3 \<close>
                do {outp internal_Movement TID_Movement_t3 ;
                    outp exit_Movement (SID_Movement_Analysis, SID_Movement_Analysis);
                    outp exited_Movement (SID_Movement_Analysis, SID_Movement_Analysis);
                    outp resume_Movement dout;
                    outp enter_Movement (SID_Movement_Analysis, SID_Movement_Waiting);
                    outp entered_Movement (SID_Movement_Analysis, SID_Movement_Waiting);
                    Ret(False, fst (snd s), SID_Movement_Analysis)
                    } \<box>
                \<comment> \<open> T_Movement_t4 \<close>
                do {outp internal_Movement TID_Movement_t4 ;
                    outp exit_Movement (SID_Movement_Analysis, SID_Movement_Analysis);
                    outp exited_Movement (SID_Movement_Analysis, SID_Movement_Analysis);
                    outp enter_Movement (SID_Movement_Analysis, SID_Movement_GasDetected);
                    outp entered_Movement (SID_Movement_Analysis, SID_Movement_GasDetected);
                    Ret(False, fst (snd s), SID_Movement_Analysis)
                    } \<box>
                (exit_events_Movement (fst (snd s)) SID_Movement_Analysis 
                   tids_Movement_Analysis Other_SIDs_to_Analysis_Movement)
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

definition State_Movement_Analysis_R where
"State_Movement_Analysis_R (idd::integer) = 
   (discard_state (State_Movement_Analysis idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_Movement - Movement_Analysis_triggers) \<^esub> 
   skip
"

paragraph \<open> GasDetected \<close>
definition CS_Movement_GasDetected_sync where
"CS_Movement_GasDetected_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_GasDetected] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_GasDetected])
)"

definition Movement_GasDetected_triggers where
"Movement_GasDetected_triggers = set (
  (enumchan1 internal_Movement_C 
    [TID_Movement_t3, TID_Movement_t4,
     TID_Movement_t8, TID_Movement_t9a]) @
  (enumchans3 [gas__Movement_C] 
    [TID_Movement_t0, TID_Movement_t2] 
    [din, dout] 
    (lseq_gassensor_enum))
)
"

definition tids_Movement_GasDetected where
" tids_Movement_GasDetected = 
    (filter 
        (\<lambda> s. s \<notin> {NULLTRANSITION__Movement, TID_Movement_t9a,
          TID_Movement_t8, TID_Movement_t4, TID_Movement_t3, 
          TID_Movement_t2, TID_Movement_t0}) 
        ITIDS_Movement_list)"

abbreviation Other_SIDs_to_GasDetected_Movement where
"Other_SIDs_to_GasDetected_Movement \<equiv>
  set [(s, SID_Movement_GasDetected) . s \<leftarrow> (SIDS_Movement_no_GasDetected)]"

definition State_Movement_GasDetected where 
"State_Movement_GasDetected = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_GasDetected_Movement ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_Movement_GasDetected_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              gs \<leftarrow> inp_in get_gs_Movement (set (lseq_gassensor_enum));
              guard (pre_Chemical_intensity(gs));
              outp set_i_Movement (Chemical_intensity gs);
              outp entered_Movement (snd (snd s), SID_Movement_GasDetected);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_Movement_t8 \<close>
                do {outp internal_Movement TID_Movement_t8 ;
                    outp exit_Movement (SID_Movement_GasDetected, SID_Movement_GasDetected);
                    outp exited_Movement (SID_Movement_GasDetected, SID_Movement_GasDetected);
                    outp stop_Movement dout;
                    outp enter_Movement (SID_Movement_GasDetected, SID_Movement_j1);
                    outp entered_Movement (SID_Movement_GasDetected, SID_Movement_j1);
                    Ret(False, fst (snd s), SID_Movement_GasDetected)
                    } \<box>
                 \<comment> \<open> T_Movement_t9a \<close>
                do {outp internal_Movement TID_Movement_t9a ;
                    outp exit_Movement (SID_Movement_GasDetected, SID_Movement_GasDetected);
                    outp exited_Movement (SID_Movement_GasDetected, SID_Movement_GasDetected);
                    gs \<leftarrow> inp_in get_gs_Movement (set (lseq_gassensor_enum));
                    guard (pre_Chemical_location(gs));
                    outp set_a_Movement (Chemical_location gs);
                    a \<leftarrow> inp_in get_a_Movement Chemical_Angle_set;
                    outp turn_Movement (dout, a);
                    outp enter_Movement (SID_Movement_GasDetected, SID_Movement_Reading);
                    outp entered_Movement (SID_Movement_GasDetected, SID_Movement_Reading);
                    Ret(False, fst (snd s), SID_Movement_GasDetected)
                    } \<box>
                (exit_events_Movement (fst (snd s)) SID_Movement_GasDetected 
                   tids_Movement_GasDetected Other_SIDs_to_GasDetected_Movement)
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

definition State_Movement_GasDetected_R where
"State_Movement_GasDetected_R (idd::integer) = 
   (discard_state (State_Movement_GasDetected idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_Movement - Movement_GasDetected_triggers) \<^esub> 
   skip
"

paragraph \<open> Final \<close>
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
        (\<lambda> s. s \<notin> {NULLTRANSITION__Movement, TID_Movement_t9a,
          TID_Movement_t8, TID_Movement_t4, TID_Movement_t3, 
          TID_Movement_t2, TID_Movement_t0}) 
        ITIDS_Movement_list)"

abbreviation Other_SIDs_to_j1_Movement where
"Other_SIDs_to_j1_Movement \<equiv>
  set [(s, SID_Movement_j1) . s \<leftarrow> (SIDS_Movement_no_j1)]"

definition State_Movement_j1 where 
"State_Movement_j1 = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_j1_Movement ; 
        outp terminate_Movement ();
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

paragraph \<open> Reading \<close>
definition CS_Movement_Reading_sync where
"CS_Movement_Reading_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_Reading] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_Reading])
)"

definition Movement_Reading_triggers where
"Movement_Reading_triggers = set (
  (enumchan1 internal_Movement_C 
    [TID_Movement_t3, TID_Movement_t4,
     TID_Movement_t8, TID_Movement_t9a]) @
  (enumchans3 [gas__Movement_C] 
    [TID_Movement_t0, TID_Movement_t2] 
    [din, dout] 
    (lseq_gassensor_enum))
)
"

definition tids_Movement_Reading where
" tids_Movement_Reading = 
    (filter 
        (\<lambda> s. s \<notin> {NULLTRANSITION__Movement, TID_Movement_t9a,
          TID_Movement_t8, TID_Movement_t4, TID_Movement_t3, 
          TID_Movement_t2, TID_Movement_t0}) 
        ITIDS_Movement_list)"

abbreviation Other_SIDs_to_Reading_Movement where
"Other_SIDs_to_Reading_Movement \<equiv>
  set [(s, SID_Movement_Reading) . s \<leftarrow> (SIDS_Movement_no_Reading)]"

definition State_Movement_Reading where 
"State_Movement_Reading = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_Reading_Movement ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_Movement_Reading_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_Movement (snd (snd s), SID_Movement_Reading);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_Movement_t0 \<close>
                do {gs \<leftarrow> inp_in gas__Movement (set [(TID_Movement_t0, din, x). 
                        x \<leftarrow> (lseq_gassensor_enum)]) ;
                    outp set_gs_Movement (snd (snd gs));
                    outp exit_Movement (SID_Movement_Reading, SID_Movement_Reading);
                    outp exited_Movement (SID_Movement_Reading, SID_Movement_Reading);
                    outp enter_Movement (SID_Movement_Reading, SID_Movement_Analysis);
                    outp entered_Movement (SID_Movement_Reading, SID_Movement_Analysis);
                    Ret(False, fst (snd s), SID_Movement_Reading)
                    } \<box>
                (exit_events_Movement (fst (snd s)) SID_Movement_Reading 
                   tids_Movement_Reading Other_SIDs_to_Reading_Movement)
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

definition State_Movement_Reading_R where
"State_Movement_Reading_R (idd::integer) = 
   (discard_state (State_Movement_Reading idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_Movement - Movement_Reading_triggers) \<^esub> 
   skip
"

subsubsection \<open> State machine \<close>
definition flow_events_Movement_stm_to_nodes where
"flow_events_Movement_stm_to_nodes = (
 let nodes = [SID_Movement_Waiting,SID_Movement_Analysis,SID_Movement_GasDetected,
              SID_Movement_j1,SID_Movement_Reading]
 in set (
      enumchans2 [enter_Movement_C, entered_Movement_C,exit_Movement_C,exited_Movement_C] 
          (filter (\<lambda> s. s \<notin> set nodes) SIDS_Movement_list) nodes
  )
)"

definition STM_Movement where
"STM_Movement (idd::integer) = 
   (I_Movement_i1(idd))
    \<parallel>\<^bsub> flow_events_Movement_stm_to_nodes \<^esub> 
   (State_Movement_Waiting_R(idd)
      \<parallel>\<^bsub> CS_Movement_Analysis_sync \<inter> (CS_Movement_Analysis_sync \<union> 
          (CS_Movement_GasDetected_sync \<union> (CS_Movement_j1_sync \<union> CS_Movement_Reading_sync))) \<^esub>
      (State_Movement_Analysis_R(idd)
        \<parallel>\<^bsub> CS_Movement_Analysis_sync \<inter> (CS_Movement_GasDetected_sync \<union> 
            (CS_Movement_j1_sync \<union> CS_Movement_Reading_sync)) \<^esub> 
        ( State_Movement_GasDetected_R(idd)
          \<parallel>\<^bsub> CS_Movement_GasDetected_sync \<inter> (CS_Movement_j1_sync \<union> CS_Movement_Reading_sync) \<^esub> 
          (State_Movement_j1_R(idd)  
            \<parallel>\<^bsub> CS_Movement_j1_sync \<inter> CS_Movement_Reading_sync \<^esub> 
          State_Movement_Reading_R(idd))
        )
      )
   )
"

definition Movement_opt_0_internal_set where
"Movement_opt_0_internal_set = 
  set (([internal_Movement_C TID_Movement_t1]) @ 
       (enumchans3 [gas__Movement_C] 
          [TID_Movement_t0, TID_Movement_t2] 
          [din, dout] 
          (lseq_gassensor_enum))
)"

definition Movement_opt_1_internal_set where
"Movement_opt_1_internal_set = 
  set ((enumchans1 [internal_Movement_C] [TID_Movement_t4, TID_Movement_t3]) @
       (enumchans1 [set_st_Movement_C] Chemical_Status_list)
)"

definition Movement_opt_2_internal_set where
"Movement_opt_2_internal_set = 
  set ((enumchans1 [internal_Movement_C] [TID_Movement_t8, TID_Movement_t9a])
)"

definition MemorySTM_opt_Movement where
"MemorySTM_opt_Movement (idd::integer) = 
  (par_hide
    (discard_state (Movement_Memory_opt_i (Chemical_IntensityC (0::2))))
    Movement_i_events
    (par_hide 
      (par_hide
        (discard_state (Movement_Memory_opt_st (Chemical_Status_noGas)))
        Movement_st_events
        (hide 
          (
            (hide
              (
                (par_hide
                  (discard_state (Movement_Memory_opt_gs (bmake TYPE(2) [])))
                  Movement_gs_events
                  (par_hide 
                    (discard_state (Movement_Memory_opt_a Chemical_Angle_Left)) 
                    Movement_a_events 
                    (STM_Movement idd)
                  )
                )
                \<parallel>\<^bsub> Movement_opt_0_internal_set \<^esub>
                (discard_state (Movement_MemoryTransitions_opt_0 idd))
              )
              ({internal_Movement_C TID_Movement_t1})
            )
            \<parallel>\<^bsub> Movement_opt_1_internal_set \<^esub> 
            (discard_state (Movement_MemoryTransitions_opt_1 idd))
          )
          (set (enumchans1 [internal_Movement_C] [TID_Movement_t4, TID_Movement_t3]))
        )
      )
      Movement_opt_2_internal_set
      (discard_state (Movement_MemoryTransitions_opt_2 idd))
    )
  )   
"

definition rename_Movement_events where
"rename_Movement_events = 
  concat (
    (enumchan2 (forget_first2 gas__Movement_C gas_Movement_C TIDS_Movement_list) 
            InOut_list lseq_gassensor_enum) @
    (enumchan2 (forget_first2 turn__Movement_C turn_Movement_C TIDS_Movement_list) 
            InOut_list Chemical_Angle_list) @
    (enumchan1 (forget_first resume__Movement_C resume_Movement_C TIDS_Movement_list) 
            InOut_list) @
    (enumchan1 (forget_first stop__Movement_C stop_Movement_C TIDS_Movement_list) 
            InOut_list)
  )
"

term "\<lbrace>resume__Movement (t, x) \<mapsto> resume_Movement x | x. x \<in> InOut_set\<rbrace>"
term "\<lbrace>terminate_Movement () \<mapsto> terminate_Movement () | _. True\<rbrace>"

definition rename_Movement_events_others where
"rename_Movement_events_others = 
  (enumchanp1 terminate_Movement_C [()]) @
  (enumchansp1 [get_i_Movement_C, set_i_Movement_C] Chemical_Intensity2_list) @
  (enumchansp1 [get_a_Movement_C, set_a_Movement_C] Chemical_Angle_list) @
  (enumchansp1 [get_st_Movement_C, set_st_Movement_C] Chemical_Status_list) @
  (enumchansp1 [get_gs_Movement_C, set_gs_Movement_C] lseq_gassensor_enum) @
  (enumchansp2 [gas_Movement_C] InOut_list lseq_gassensor_enum) @
  (enumchansp2 [turn_Movement_C] InOut_list Chemical_Angle_list) @
  (enumchansp1 [resume_Movement_C, stop_Movement_C] InOut_list) @
  (enumchansp2 [enter_Movement_C, entered_Movement_C, exit_Movement_C, exited_Movement_C] 
    SIDS_Movement_list SIDS_Movement_list) @
  (enumchansp1 [internal_Movement_C] TIDS_Movement_list)
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

subsection \<open> MainController \<close>
chantype Chan_MainCtrl =
  terminate_MainCtrl :: unit
  gas_MainCtrl :: "InOut \<times> 2 Chemical_GasSensor[2]blist"
  resume_MainCtrl :: "InOut"
  turn_MainCtrl :: "InOut \<times> Chemical_Angle"
  stop_MainCtrl :: "InOut"

subsubsection \<open> Memory \<close>
definition Memory_MainCtrl where
"Memory_MainCtrl (idd::integer) = skip"

subsubsection \<open> Controller \<close>

definition rename_MainCtrl_Movement_events where
"rename_MainCtrl_Movement_events = 
  (enumchanp2_1 (terminate_Movement_C,terminate_MainCtrl_C) [()]) @
  (enumchansp2_2 [(gas_Movement_C, gas_MainCtrl_C)] InOut_list lseq_gassensor_enum) @
  (enumchansp2_1 [(resume_Movement_C, resume_MainCtrl_C)] InOut_list) @
  (enumchansp2_2 [(turn_Movement_C, turn_MainCtrl_C)] InOut_list Chemical_Angle_list) @
  (enumchansp2_1 [(stop_Movement_C, stop_MainCtrl_C)] InOut_list)
"

definition rename_D__Movement where
  "rename_D__Movement idd = rename (set rename_MainCtrl_Movement_events) (D__Movement idd)"

definition D__MainCtrl where
"D__MainCtrl (idd::integer) = 
  (par_hide
    (rename_D__Movement idd)
    {}
    (discard_state (Memory_MainCtrl idd))
  )  \<lbrakk> set [terminate_MainCtrl_C ()] \<Zrres> skip
"

export_code
  Movement_Memory_opt_gs
  Movement_MemoryTransitions_opt_0
  Movement_MemoryTransitions_opt_1
  Movement_MemoryTransitions_opt_2
  I_Movement_i1
  State_Movement_Waiting
  State_Movement_Waiting_R
  State_Movement_Analysis_R
  State_Movement_GasDetected_R
  State_Movement_j1_R
  State_Movement_Reading_R
  MemorySTM_opt_Movement
  AUX_opt_Movement
  D__Movement
in Haskell 
  (* module_name Movement *)
  file_prefix RoboChart_ChemicalDetector 
  (string_classes) 




subsection \<open> Module \<close>
chantype Chan_mod0 =
(* terminates of MainCtrl are mapped to it *)
  terminate_mod0 :: unit 
(* variable channels: set_x and get_x of Movement and stm1 are mapped to these channels *)
  set_x_mod0 :: core_int
  get_x_mod0 :: core_int
(* shared variable channels *)
  set_EXT_x_mod0_MainCtrl :: core_int
(* e1 of Movement is mapped to it *)
  e1_mod0 :: "InOut \<times> core_int"
(* e2 of stm1 is mapped to it *)
  e2_mod0 :: "InOut"

definition Memory_mod0 where
"Memory_mod0 = loop (\<lambda> id::integer.
  ( do {x \<leftarrow> inp_in set_x_mod0 rc.core_int_set; 
        outp set_EXT_x_mod0_MainCtrl x; Ret (id)}
  )
)"

(*
definition rename_mod0_MainCtrl_events where
"rename_mod0_MainCtrl_events = 
  [(terminate_MainCtrl_C (), terminate_mod0_C ())] @
  [(set_x_MainCtrl_C n, set_x_mod0_C n). n \<leftarrow> rc.core_int_list] @
  [(get_x_MainCtrl_C n, get_x_mod0_C n). n \<leftarrow> rc.core_int_list] @
  [(e1_MainCtrl_C (d, n), e1_mod0_C (d, n)). d \<leftarrow> InOut_list, n \<leftarrow> rc.core_int_list] @
  [(e2_MainCtrl_C (d), e2_mod0_C (d)). d \<leftarrow> InOut_list] @
  [(set_EXT_x_MainCtrl_C n, set_EXT_x_mod0_MainCtrl_C n). n \<leftarrow> rc.core_int_list]
"
*)
definition rename_mod0_MainCtrl_events where
"rename_mod0_MainCtrl_events = 
  (enumchanp2_1 (terminate_MainCtrl_C,terminate_mod0_C) [()]) @
  (enumchansp2_1 [(set_x_MainCtrl_C, set_x_mod0_C), (get_x_MainCtrl_C, get_x_mod0_C), 
      (set_EXT_x_MainCtrl_C, set_EXT_x_mod0_MainCtrl_C)] rc.core_int_list) @
  (enumchanp2_1 (e2_MainCtrl_C, e2_mod0_C) InOut_list) @
  (enumchanp2_2 (e1_MainCtrl_C, e1_mod0_C) InOut_list rc.core_int_list)
"

definition rename_D__MainCtrl where
"rename_D__MainCtrl idd = rename (set rename_mod0_MainCtrl_events) (D__MainCtrl idd)"

definition "mod0_set_x_events = set (
  enumchan1 set_x_mod0_C  rc.core_int_list
)"

definition "mod0_get_x_events = set (
  enumchan1 get_x_mod0_C  rc.core_int_list
)"

definition "mod0_set_EXT_x_events = set (
  enumchan1 set_EXT_x_mod0_MainCtrl_C  rc.core_int_list
)"

definition D__ctr_mem where
"D__ctr_mem (idd::integer) = (
              (rename_D__MainCtrl idd) 
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
              (rename_D__MainCtrl idd) 
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
  D__MainCtrl
  rename_D__MainCtrl
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
