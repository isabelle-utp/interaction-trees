section \<open> MicroController \label{sec:chem_microcontroller}\<close>

theory RoboChart_ChemicalDetector_autonomous_microcontroller
  imports "RoboChart_ChemicalDetector_autonomous_general"
begin

subsection \<open> Overview\label{ssec:chem_movement_overview}\<close>
text \<open> The @{text Movement} state machine in the @{text MicroController} differs from 
@{text GasAnalysis} in that it requires an operation @{text changeDirection}, which is provided by 
@{text MicroController} and defined in the package @{text Location}. The operation is defined using 
a standard state machine.

We also note that the machine @{text Movement} encoded in this theory differs from the original 
version 3.0\footnote{
@{url "https://robostar.cs.york.ac.uk/case_studies/autonomous-chemical-detector/autonomous-chemical-detector.html#version3"}
}
 in that the transition @{text t21} from @{text Avoiding} to @{text Going} with a trigger 
@{text resume} should not be here and so removed in this theory. \<close>

subsection \<open> Movement general definitions\label{ssec:chem_movement_general}\<close>
subsubsection \<open> Constants \<close>
text \<open>The values of these constants are from @{verbatim "instantiation.csp"}. \<close>
abbreviation const_Movement_lv :: "core_real" where
"const_Movement_lv \<equiv> 1"

abbreviation const_Movement_evadeTime :: "core_nat" where
"const_Movement_evadeTime \<equiv> 0"

abbreviation const_Movement_stuckPeriod :: "core_nat" where
"const_Movement_stuckPeriod \<equiv> 0"

abbreviation const_Movement_stuckDist :: "core_real" where
"const_Movement_stuckDist \<equiv> 0"

abbreviation const_Movement_outPeriod :: "core_nat" where
"const_Movement_outPeriod \<equiv> 0"

text \<open>The definition @{term const_Location_changeDirection_lv} corresponds to the constant 
@{text lv} in the definition of the operation @{text changeDirection} in the package @{text Location}.
\<close>
abbreviation const_Location_changeDirection_lv :: "core_real" where
"const_Location_changeDirection_lv \<equiv> 0"

subsubsection \<open> Types \<close>
paragraph \<open> changeOperation \<close>text\<open>\mbox{}\<close>

datatype SIDS_changeDirection = SID_changeDirection
	              | SID_changeDirection_From
	              | SID_changeDirection_j0

(* definition "SIDS_changeDirection_list = enum_SIDS_changeDirection_inst.enum_SIDS_changeDirection"*)
abbreviation "SIDS_changeDirection_list \<equiv> [
  SID_changeDirection, SID_changeDirection_From, SID_changeDirection_j0]"
abbreviation "SIDS_changeDirection_set \<equiv> set SIDS_changeDirection_list"
abbreviation "SIDS_changeDirection_nodes \<equiv> (removeAll SID_changeDirection SIDS_changeDirection_list)"
abbreviation "SIDS_changeDirection_no_From \<equiv> (removeAll SID_changeDirection_From SIDS_changeDirection_list)"
abbreviation "SIDS_changeDirection_no_j0 \<equiv> (removeAll SID_changeDirection_j0 SIDS_changeDirection_list)"

datatype TIDS_changeDirection = NULLTRANSITION__changeDirection
	              | TID_changeDirection_t1
	              | TID_changeDirection_t2
	              | TID_changeDirection_t3
	              | TID_changeDirection_t4

abbreviation "TIDS_changeDirection_list \<equiv> [NULLTRANSITION__changeDirection,
  TID_changeDirection_t1, TID_changeDirection_t2, TID_changeDirection_t3, 
  TID_changeDirection_t4]"
abbreviation "TIDS_changeDirection_set \<equiv> set TIDS_changeDirection_list"

text \<open> Identifiers of transitions that can interrupt a state, excluding transitions from junctions. \<close>
abbreviation "ITIDS_changeDirection_list \<equiv> [
  TID_changeDirection_t1, TID_changeDirection_t3,	TID_changeDirection_t4
]"
abbreviation "ITIDS_changeDirection \<equiv> set ITIDS_changeDirection_list"

paragraph \<open> Movement \<close>text\<open>\mbox{}\<close>
datatype SIDS_Movement = SID_Movement
	              | SID_Movement_Waiting
	              | SID_Movement_Going
	              | SID_Movement_Found
	              | SID_Movement_j1
	              | SID_Movement_Avoiding
	              | SID_Movement_TryingAgain
	              | SID_Movement_AvoidingAgain
	              | SID_Movement_GettingOut

(* definition "SIDS_Movement_list = enum_SIDS_Movement_inst.enum_SIDS_Movement"*)
abbreviation "SIDS_Movement_list \<equiv> [SID_Movement, SID_Movement_Waiting, SID_Movement_Going, 
  SID_Movement_Found, SID_Movement_j1, SID_Movement_Avoiding, SID_Movement_TryingAgain,
  SID_Movement_AvoidingAgain, SID_Movement_GettingOut]"
abbreviation "SIDS_Movement_set \<equiv> set SIDS_Movement_list"
abbreviation "SIDS_Movement_nodes \<equiv> (removeAll SID_Movement SIDS_Movement_list)"
abbreviation "SIDS_Movement_no_Waiting \<equiv> (removeAll SID_Movement_Waiting SIDS_Movement_list)"
abbreviation "SIDS_Movement_no_Going \<equiv> (removeAll SID_Movement_Going SIDS_Movement_list)"
abbreviation "SIDS_Movement_no_Found \<equiv> (removeAll SID_Movement_Found SIDS_Movement_list)"
abbreviation "SIDS_Movement_no_Avoiding \<equiv> (removeAll SID_Movement_Avoiding SIDS_Movement_list)"
abbreviation "SIDS_Movement_no_j1 \<equiv> (removeAll SID_Movement_j1 SIDS_Movement_list)"
abbreviation "SIDS_Movement_no_TryingAgain \<equiv> (removeAll SID_Movement_TryingAgain SIDS_Movement_list)"
abbreviation "SIDS_Movement_no_AvoidingAgain \<equiv> (removeAll SID_Movement_AvoidingAgain SIDS_Movement_list)"
abbreviation "SIDS_Movement_no_GettingOut \<equiv> (removeAll SID_Movement_GettingOut SIDS_Movement_list)"

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

(* An example to use TrID to construct a more abstract data type.
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
abbreviation "TIDS_Movement_list \<equiv> [NULLTRANSITION__Movement, TID_Movement_t0,
  TID_Movement_t1, TID_Movement_t2, TID_Movement_t3, TID_Movement_t4, TID_Movement_t5,
  TID_Movement_t6, TID_Movement_t7, TID_Movement_t8, TID_Movement_t9, TID_Movement_t10, 
  TID_Movement_t11, TID_Movement_t12, TID_Movement_t13, TID_Movement_t14, TID_Movement_t15, 
  TID_Movement_t16, TID_Movement_t17, TID_Movement_t18, TID_Movement_t19, TID_Movement_t20, 
  TID_Movement_t21, TID_Movement_t22]"

(*
definition "TIDS_Movement_list \<equiv> 
  map ((MkTrid TYPE(Movement)) \<circ> (\<lambda>i. (Abs_bit0' i)::(24))) (upt 0 (CARD(24)))"
*)
abbreviation "TIDS_Movement_set \<equiv> set TIDS_Movement_list"

text \<open> Identifiers of transitions that can interrupt a state, excluding transitions from junctions. \<close>
abbreviation "ITIDS_Movement_list \<equiv> [TID_Movement_t0,
  TID_Movement_t2, TID_Movement_t3,	TID_Movement_t4, TID_Movement_t5, TID_Movement_t6, 
  TID_Movement_t7, TID_Movement_t8,	TID_Movement_t9, TID_Movement_t10,	TID_Movement_t11,
  TID_Movement_t12,	TID_Movement_t13, TID_Movement_t14,	TID_Movement_t15, TID_Movement_t16,
  TID_Movement_t17,	TID_Movement_t18, TID_Movement_t19,	TID_Movement_t20, TID_Movement_t21,
  TID_Movement_t22  
]"

abbreviation "ITIDS_Movement \<equiv> set ITIDS_Movement_list"

text \<open>Because this state machine requires three undefined operations @{text randomWalk}, 
@{text move}, and @{text shortRandomWalk}, provided by the platform through the interface 
@{text Operations}, its channel type @{term Chan_Movement} contains three 
extra channels @{text randomWalkCall_Movement}, @{text moveCall_Movement}, and 
@{text shortRandomWalkCall_Movement} to record calls of these operations. 

Additionally, the state machine also requires state machine defined operation 
@{text changeDirection}. The usual channels, such as @{text internal}, @{text terminate}, 
flow channels, variables, and events, in the channel type for a state machine are also present for 
this operation @{text changeDirection}. But these channels are not inside a separate channel type 
for @{text changeDirection}. Instead, they are also merged into this channel type @{text Chan_Movement}. 

The reason why these channels are still in this channel type is because in the CSP semantics 
the memory processes and the states processes of this operation are merged into @{text Movement}.
In order to compose them with the processes for @{text Movement}, @{text Movement} and 
@{text changeDirection} shall have the same channel type. So we build a big channel type to contain 
channels for both of them. \<close>
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
  (* changeDirectionCall_Movement :: "Location_Loc" *)
  randomWalkCall_Movement :: unit
  moveCall_Movement :: "core_real \<times> Chemical_Angle"
  shortRandomWalkCall_Movement :: unit

\<comment> \<open>Channels for @{text changeOperation}\<close>
(* flow channels *)
  internal_changeDirection :: TIDS_changeDirection
  enter_changeDirection :: "SIDS_changeDirection \<times> SIDS_changeDirection"
  entered_changeDirection :: "SIDS_changeDirection \<times> SIDS_changeDirection"
  exit_changeDirection :: "SIDS_changeDirection \<times> SIDS_changeDirection"
  exited_changeDirection :: "SIDS_changeDirection \<times> SIDS_changeDirection"
  terminate_changeDirection :: unit
\<comment> \<open>The operation itself does not have a local variable named @{text l}. In the CSP semantics, we 
treat the parameter @{text l} as a local variable. Its value is set when the operation is called 
outside, and got inside the process for the operation. So its value will not be set inside the 
operation. \<close>
  get_l_changeDirection :: "Location_Loc"
  set_l_changeDirection :: "Location_Loc"
(* timeout *)
  stuck_timeout__Movement :: "TIDS_Movement \<times> InOut"
  stuck_timeout_Movement :: "InOut"

(* Call events for undefined operations. In the operation, use the channel (moveCall_Movement) 
  from Movement *)
  (* 
  randomWalkCall_changeDirection :: unit
  moveCall_changeDirection :: "core_real \<times> Chemical_Angle"
  shortRandomWalkCall_changeDirection :: unit
  *)

text \<open>We also note that in @{term Chan_Movement} there is no operation call event for the call to the 
@{text move} operation in @{text changeOperation}. Instead, @{text changeOperation} will use the 
@{term moveCall_Movement} for that call. This is due to the fact that the required operations in 
@{text changeOperation} (as an operation called in @{text Movement}) must also be required in 
@{text Movement}. This is enforced by a well-formedness condition of RoboChart. So the channel for 
the call to the required @{text move} operation in @{text changeOperation} has already provided by 
@{text Movement}: @{term moveCall_Movement}. 

In @{term Chan_Movement}, we also add another event channel @{term stuck_timeout__Movement} to deal 
with a problem raised by the ignorance of time expressions in the guard of the transition from 
@{text AvoidingAgain} to @{text GettingOut}. This problem will be explained later.
\<close>

subsubsection \<open> Operation Calls \<close>
(*
definition CALL__changeDirection_Movement :: "integer \<Rightarrow> Location_Loc \<Rightarrow> (Chan_Movement, unit) itree" where
"CALL__changeDirection_Movement idd l = do {outp changeDirectionCall_Movement l}"
*)
text \<open>Calls to the platform provided operations @{text randomWalk}, @{text move}, and 
@{text shortRandomWalk} are wrapped in the functions: @{term CALL__randomWalk_Movement},
@{term CALL__move_Movement}, and @{term CALL__shortRandomWalk_Movement} below. Each function outputs 
the operation parameters on its corresponding channel event.\<close>
definition CALL__randomWalk_Movement :: "integer \<Rightarrow> (Chan_Movement, unit) itree" where
"CALL__randomWalk_Movement idd = do {outp randomWalkCall_Movement ()}"

definition CALL__move_Movement :: "integer \<Rightarrow> core_real \<Rightarrow> Chemical_Angle \<Rightarrow> (Chan_Movement, unit) itree" where
"CALL__move_Movement idd lv a = do {outp moveCall_Movement (lv, a)}"

definition CALL__shortRandomWalk_Movement :: "integer \<Rightarrow> (Chan_Movement, unit) itree" where
"CALL__shortRandomWalk_Movement idd = do {outp shortRandomWalkCall_Movement ()}"

subsection \<open> The changeDirection operation\label{ssec:chem_changedirection_op}\<close>
text \<open>In this theory, the memory processes and the state machine process of @{text changeDirection} 
are not independent in its own module in CSP. Instead, they are part of those of @{text Movement}. \<close>

subsubsection \<open> Sets of events \<close>

abbreviation "int_int_tids_changeDirection \<equiv> 
  [TID_changeDirection_t1, TID_changeDirection_t3,	TID_changeDirection_t4]"

abbreviation int_int_changeDirection where
"int_int_changeDirection \<equiv> set (
  (enumchan1 internal_changeDirection_C int_int_tids_changeDirection)
)"

abbreviation "enter_exit_channels_changeDirection \<equiv>
  [enter_changeDirection_C, entered_changeDirection_C, exit_changeDirection_C, exited_changeDirection_C]"

abbreviation internal_events_changeDirection where
"internal_events_changeDirection \<equiv> set (
  enumchans2 enter_exit_channels_changeDirection SIDS_changeDirection_list SIDS_changeDirection_list
)"

abbreviation changeDirection_l_events where
"changeDirection_l_events \<equiv> 
    set (enumchans1 [get_l_changeDirection_C, set_l_changeDirection_C] Location_Loc_list)
"

abbreviation changeDirection_MachineInternalEvents where
"changeDirection_MachineInternalEvents \<equiv> 
  set (enumchan1 internal_changeDirection_C TIDS_changeDirection_list)
"

subsubsection \<open> State Machine Memory \<close>
text \<open> Memory cell processes and memory transition processes of this operation are part of the memory 
processes of @{text Movement}. \<close>

definition changeDirection_Memory_opt_l where
"changeDirection_Memory_opt_l = 
  mem_of_lvar get_l_changeDirection set_l_changeDirection (Location_Loc_set)"

subsubsection \<open> States \<close>
paragraph \<open> Initial \<close>text\<open>\mbox{}\<close>
definition I_changeDirection_i0 where
"I_changeDirection_i0 = (\<lambda> (id::integer) . 
  do {outp internal_changeDirection TID_changeDirection_t2 ; 
      outp enter_changeDirection (SID_changeDirection, SID_changeDirection_From);
      outp entered_changeDirection (SID_changeDirection, SID_changeDirection_From)
  })
"

paragraph \<open> From \<close>text\<open>\mbox{}\<close>
abbreviation CS_changeDirection_From_sync where
"CS_changeDirection_From_sync \<equiv>
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_changeDirection 
        [SID_changeDirection_From] SIDS_changeDirection_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_changeDirection 
        SIDS_changeDirection_nodes [SID_changeDirection_From])
)"

abbreviation changeDirection_From_triggers where
"changeDirection_From_triggers \<equiv> set (
  (enumchan1 internal_changeDirection_C 
    [TID_changeDirection_t1, TID_changeDirection_t3, TID_changeDirection_t4])
)
"

definition tids_changeDirection_From where
" tids_changeDirection_From = 
    (filter 
        (\<lambda> s. s \<notin> (set [NULLTRANSITION__changeDirection,TID_changeDirection_t1,
                        TID_changeDirection_t3, TID_changeDirection_t4])) 
        ITIDS_changeDirection_list)"

abbreviation Other_SIDs_to_From_changeDirection where
"Other_SIDs_to_From_changeDirection \<equiv>
  set [(s, SID_changeDirection_From) . s \<leftarrow> (SIDS_changeDirection_no_From)]"

definition exit_event_changeDirection1 :: 
  "integer \<Rightarrow> (TIDS_changeDirection \<Longrightarrow>\<^sub>\<triangle> Chan_Movement) \<Rightarrow> SIDS_changeDirection
   \<Rightarrow> TIDS_changeDirection list \<Rightarrow> SIDS_changeDirection rel 
   \<Rightarrow> (Chan_Movement, bool \<times> integer \<times> SIDS_changeDirection) itree" where
"exit_event_changeDirection1 idd ch sid tids other_sids = 
  do {inp_in ch (set tids);
      y \<leftarrow> inp_in exit_changeDirection other_sids;
      outp exited_changeDirection (fst y, sid);
      Ret(False, idd, sid)
}"

definition exit_events_changeDirection ::  "integer \<Rightarrow> SIDS_changeDirection 
    \<Rightarrow> TIDS_changeDirection list  \<Rightarrow> SIDS_changeDirection rel 
    \<Rightarrow> (Chan_Movement, bool \<times> integer \<times> SIDS_changeDirection) itree" where
"exit_events_changeDirection idd sid tids other_sids =
    (exit_event_changeDirection1 idd internal_changeDirection sid tids other_sids
    )"

definition State_changeDirection_From where 
"State_changeDirection_From = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_changeDirection Other_SIDs_to_From_changeDirection ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open>  @{verbatim State_changeDirection_From_execute} \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_changeDirection (snd (snd s), SID_changeDirection_From);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open>  @{verbatim T_changeDirection_t1} \<close>
              do {outp internal_changeDirection TID_changeDirection_t1 ;
                  outp exit_changeDirection (SID_changeDirection_From, SID_changeDirection_From);
                  outp exited_changeDirection (SID_changeDirection_From, SID_changeDirection_From);
                  guard(True); CALL__move_Movement id const_Location_changeDirection_lv 
                    Chemical_Angle_Right;
                  outp enter_changeDirection (SID_changeDirection_From, SID_changeDirection_j0);
                  outp entered_changeDirection (SID_changeDirection_From, SID_changeDirection_j0);
                  Ret(False, fst (snd s), SID_changeDirection_From)
              } \<box>
              \<comment> \<open>  @{verbatim T_changeDirection_t3} \<close>
              do {outp internal_changeDirection TID_changeDirection_t3 ;
                  outp exit_changeDirection (SID_changeDirection_From, SID_changeDirection_From);
                  outp exited_changeDirection (SID_changeDirection_From, SID_changeDirection_From);
                  guard(True); CALL__move_Movement id const_Location_changeDirection_lv 
                    Chemical_Angle_Left;
                  outp enter_changeDirection (SID_changeDirection_From, SID_changeDirection_j0);
                  outp entered_changeDirection (SID_changeDirection_From, SID_changeDirection_j0);
                  Ret(False, fst (snd s), SID_changeDirection_From)
              } \<box>
              \<comment> \<open>  @{verbatim T_changeDirection_t4} \<close>
              do {outp internal_changeDirection TID_changeDirection_t4 ;
                  outp exit_changeDirection (SID_changeDirection_From, SID_changeDirection_From);
                  outp exited_changeDirection (SID_changeDirection_From, SID_changeDirection_From);
                  guard(True); CALL__move_Movement id const_Location_changeDirection_lv 
                    Chemical_Angle_Back;
                  outp enter_changeDirection (SID_changeDirection_From, SID_changeDirection_j0);
                  outp entered_changeDirection (SID_changeDirection_From, SID_changeDirection_j0);
                  Ret(False, fst (snd s), SID_changeDirection_From)
              } \<box>
                (exit_events_changeDirection (fst (snd s)) SID_changeDirection_From 
                   tids_changeDirection_From Other_SIDs_to_From_changeDirection)
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

definition State_changeDirection_From_R where
"State_changeDirection_From_R (idd::integer) = 
   (discard_state (State_changeDirection_From idd))
    \<parallel>\<^bsub> (int_int_changeDirection - changeDirection_From_triggers) \<^esub> 
   skip
"

paragraph \<open> Final (j0) \<close>text\<open>\mbox{}\<close>
abbreviation CS_changeDirection_j0_sync where
"CS_changeDirection_j0_sync \<equiv>
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_changeDirection [SID_changeDirection_j0] SIDS_changeDirection_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_changeDirection SIDS_changeDirection_nodes [SID_changeDirection_j0])
)"

abbreviation changeDirection_j0_triggers where
"changeDirection_j0_triggers \<equiv> set ([])
"

abbreviation Other_SIDs_to_j0_changeDirection where
"Other_SIDs_to_j0_changeDirection \<equiv>
  set [(s, SID_changeDirection_j0) . s \<leftarrow> (SIDS_changeDirection_no_j0)]"

definition State_changeDirection_j0 where 
"State_changeDirection_j0 = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_changeDirection Other_SIDs_to_j0_changeDirection ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open>  @{verbatim State_changeDirection_j0_execute} \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_changeDirection (snd (snd s), SID_changeDirection_j0);
              outp terminate_changeDirection ();
              Ret(False, id, SID_changeDirection_j0)
            })
            \<comment> \<open> The previous state: a triple \<close> 
            (ret)
        ) ;
        Ret (id)
  }
)
"

definition State_changeDirection_j0_R where
"State_changeDirection_j0_R (idd::integer) = 
   (discard_state (State_changeDirection_j0 idd))
    \<parallel>\<^bsub> (int_int_changeDirection - changeDirection_j0_triggers) \<^esub> 
   skip
"

subsubsection \<open> State machine \<close>
abbreviation flow_events_changeDirection_stm_to_nodes where
"flow_events_changeDirection_stm_to_nodes \<equiv> (
 let nodes = [SID_changeDirection_From, SID_changeDirection_j0]
 in set (
      enumchans2 [enter_changeDirection_C, entered_changeDirection_C,
          exit_changeDirection_C,exited_changeDirection_C] 
          (filter (\<lambda> s. s \<notin> set nodes) SIDS_changeDirection_list) nodes
  )
)"

definition STM_changeDirection_1 where
"STM_changeDirection_1 (idd::integer) =
  (State_changeDirection_From_R(idd)  
    \<parallel>\<^bsub> CS_changeDirection_From_sync \<inter> CS_changeDirection_j0_sync \<^esub> 
  State_changeDirection_j0_R(idd))
"

definition STM_changeDirection where
"STM_changeDirection (idd::integer) = 
   (I_changeDirection_i0(idd))
    \<parallel>\<^bsub> flow_events_changeDirection_stm_to_nodes \<^esub> 
   STM_changeDirection_1(idd)
"

(*
definition STM_core_changeDirection where
"STM_core_changeDirection (idd::integer) l = 
   do {outp set_l_changeDirection l; STM_changeDirection idd}
"

definition changeDirection_opt_0_internal_set where
"changeDirection_opt_0_internal_set = 
  set ((enumchans1 [internal_changeDirection_C] 
    [TID_changeDirection_t2]))"

definition changeDirection_opt_1_internal_list where
"changeDirection_opt_1_internal_list = 
   ((enumchans1 [internal_changeDirection_C] 
    [TID_changeDirection_t1, TID_changeDirection_t3, TID_changeDirection_t4]))"

definition changeDirection_opt_1_internal_set where
"changeDirection_opt_1_internal_set = 
  set (changeDirection_opt_1_internal_list @ 
  enumchan1 set_l_changeDirection_C Location_Loc_list)"

definition MemorySTM_opt_changeDirection where
"MemorySTM_opt_changeDirection (idd::integer) l = 
    (par_hide
      (discard_state (changeDirection_Memory_opt_l (Location_Loc_left)))
      changeDirection_l_events
      (hide 
        (
          (hide
            (
              (STM_core_changeDirection idd l)
              \<parallel>\<^bsub> changeDirection_opt_0_internal_set \<^esub>
              (discard_state (changeDirection_MemoryTransitions_opt_0 idd))
            )
            changeDirection_opt_0_internal_set
          )
          \<parallel>\<^bsub> set changeDirection_opt_1_internal_list \<^esub> 
          (discard_state (changeDirection_MemoryTransitions_opt_1 idd))
        )
        changeDirection_opt_1_internal_set
      )
    )
"

definition AUX_opt_changeDirection where
"AUX_opt_changeDirection (idd::integer) l = 
  (hide 
    ( 
      (MemorySTM_opt_changeDirection idd l) \<lbrakk> set [terminate_changeDirection_C ()] \<Zrres> skip
    )
    changeDirection_MachineInternalEvents
  )
"

text \<open> Here @{text "terminate"} is also treated as internal in an operation, which is different from 
that of a state machine definition. \<close>

definition D__changeDirection where
"D__changeDirection (idd::integer) l = 
  hide (hide (AUX_opt_changeDirection idd l) internal_events_changeDirection) 
  (set [terminate_changeDirection_C ()])
"

subsubsection \<open> State machine inside MicroController \<close>
*)
(*text \<open> This is the version inside the MicroController.csp. In this version, the memory of local 
variables is with the state machine Movement, instead of inside this operation.
\<close>*)
(* This process will deadlock because there are three internal events enabled and hidden. 
See the definition of hide. *)

(*
definition AUX_changeDirection where
"AUX_changeDirection (idd::integer) = 
  (hide 
    ( 
      (STM_changeDirection idd) \<lbrakk> set [terminate_changeDirection_C ()] \<Zrres> skip
    )
    changeDirection_MachineInternalEvents
  )
"
*)

text \<open> The reference of @{term AUX_changeDirection} is @{verbatim AUX_changeDirection} inside 
@{verbatim MicroController.csp}. This definition of this process is different from that of 
@{text Movement} in that it will not hide the @{text internal__changeDirection} channel events 
(@{term changeDirection_MachineInternalEvents}). If this channel is hidden here, then it cannot be 
used to synchronise with @{text internal__changeDirection} in the memory of @{text changeDirection} 
because its memory is part of the memory of @{text Movement}.
These events, therefore, are hidden later in @{term AUX_opt_Movement}.
\<close>
definition AUX_changeDirection where
"AUX_changeDirection (idd::integer) = 
    ( 
      (STM_changeDirection idd) \<lbrakk> set [terminate_changeDirection_C ()] \<Zrres> skip
    )
"

text \<open>Similarly, @{term D__changeDirection} does not hide @{term internal_events_changeDirection}. \<close>
definition D__changeDirection where
"D__changeDirection (idd::integer) = 
  ((AUX_changeDirection idd) \<setminus> internal_events_changeDirection)
    \<setminus> (set [terminate_changeDirection_C ()])
"

subsection \<open> Movement state machine\label{ssec:chem_movement}\<close>
subsubsection \<open> Operation Calls \<close>
text \<open>The function @{term CALL__changeDirection_Movement} below corresponds to the call of @{text 
changeDirection} in @{text Movement}. The call parameter is recorded in @{text l} and set to the 
memory cell for @{text l} in the operation through channel @{term set_l_changeDirection}. Afterwards, 
the process of the operation is called. \<close>
definition CALL__changeDirection_Movement 
  :: "integer \<Rightarrow> Location_Loc \<Rightarrow> (Chan_Movement, unit) itree" where
"CALL__changeDirection_Movement idd l = do {outp set_l_changeDirection l; D__changeDirection idd}"

subsubsection \<open> Sets of events \<close>

abbreviation "int_int_tids_Movement \<equiv> 
  removeAll NULLTRANSITION__Movement (removeAll (TID_Movement_t1) TIDS_Movement_list)"
(*[TID_Movement_t0,
  TID_Movement_t2, TID_Movement_t3, TID_Movement_t4, TID_Movement_t5,
  TID_Movement_t6, TID_Movement_t7, TID_Movement_t8, TID_Movement_t9, TID_Movement_t10, 
  TID_Movement_t11, TID_Movement_t12, TID_Movement_t13, TID_Movement_t14, TID_Movement_t15, 
  TID_Movement_t16, TID_Movement_t17, TID_Movement_t18, TID_Movement_t19, TID_Movement_t20, 
  TID_Movement_t21, TID_Movement_t22]*)

abbreviation int_int_Movement where
"int_int_Movement \<equiv> set (
  (enumchans3 [obstacle__Movement_C] int_int_tids_Movement InOut_list Location_Loc_list) @
  (enumchans3 [odometer__Movement_C] int_int_tids_Movement InOut_list rc.core_real_list) @
  (enumchans2 [resume__Movement_C, stop__Movement_C, flag__Movement_C] 
    int_int_tids_Movement InOut_list) @
  (enumchans3 [turn__Movement_C] int_int_tids_Movement InOut_list Chemical_Angle_list) @
  (enumchan1 internal_Movement_C int_int_tids_Movement)
)"

abbreviation "enter_exit_channels_Movement \<equiv>
  [enter_Movement_C, entered_Movement_C, exit_Movement_C, exited_Movement_C]"

abbreviation internal_events_Movement where
"internal_events_Movement \<equiv> set (
  enumchans2 enter_exit_channels_Movement SIDS_Movement_list SIDS_Movement_list
)"


abbreviation Movement_d0_events where
"Movement_d0_events \<equiv> 
    set (enumchans1 [get_d0_Movement_C, set_d0_Movement_C] rc.core_real_list)
"

abbreviation Movement_d1_events where
"Movement_d1_events \<equiv> 
    set (enumchans1 [get_d1_Movement_C, set_d1_Movement_C] rc.core_real_list)
"

abbreviation Movement_l_events where
"Movement_l_events \<equiv> 
    set (enumchans1 [get_l_Movement_C, set_l_Movement_C] Location_Loc_list)
"

abbreviation Movement_a_events where
"Movement_a_events \<equiv> 
    set (enumchans1 [get_a_Movement_C, set_a_Movement_C] Chemical_Angle_list)
"

abbreviation Movement_MachineInternalEvents where
"Movement_MachineInternalEvents \<equiv>
  set (enumchan1 internal_Movement_C TIDS_Movement_list)
"

subsubsection \<open> State Machine Memory \<close>
text \<open> Memory cell processes for local variables @{text d0}, @{text d1}, @{text a}, and @{text l} are 
defined below. \<close>
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

text \<open> Memory transition processes are given below. \<close>
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
    \<comment> \<open>@{text \<open>do {outp internal_Movement (TID_Movement_t21) ; Ret (id)} \<box> \<close>} \<close>
    do {outp stop__Movement (TID_Movement_t15, din) ; Ret (id)} \<box>
    do {outp internal_Movement TID_Movement_t5 ; Ret (id)} \<box>
    \<comment> \<open>This is for the default transition @{text t2} in @{text changeDirection}.\<close>
    do {outp internal_changeDirection TID_changeDirection_t2 ; Ret (id)} \<box>
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

(*
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
*)

text \<open> This memory transition process @{term changeDirection_MemoryTransitions_opt_1} is for 
the three transitions from @{text From} to @{text Final} of @{text changeOperation}. \<close>
definition changeDirection_MemoryTransitions_opt_1 where
"changeDirection_MemoryTransitions_opt_1 =
  loop (\<lambda> id::integer.
    do {l \<leftarrow> inp_in get_l_changeDirection Location_Loc_set ;
        (
          do {guard (l=Location_Loc_left); outp internal_changeDirection TID_changeDirection_t1 ;
            Ret (id)} \<box>
          do {guard (l=Location_Loc_front); outp internal_changeDirection TID_changeDirection_t4 ;
            Ret (id)} \<box>
          do {guard (l=Location_Loc_right); outp internal_changeDirection TID_changeDirection_t3 ;
            Ret (id)} \<box>
          do {inp_in set_l_changeDirection Location_Loc_set ; Ret (id)}
        )
    }
  )
"

definition Movement_MemoryTransitions_opt_2 where
"Movement_MemoryTransitions_opt_2 = 
  loop (\<lambda> id::integer.
    do {d1 \<leftarrow> inp_in get_d1_Movement rc.core_real_set ; 
        d0 \<leftarrow> inp_in get_d0_Movement rc.core_real_set ;
        ( \<comment> \<open>In the CSP semantics, the guards of transitions @{text t12} and @{text t13} are both true; 
          We manually discard time primitives, but keep the non-time expression 
          @{text \<open>(d1-d0\<le>stuckDist)\<close>} for @{text t13}, and 
          @{text \<open>(d1-d0>stuckDist)\<close>} for @{text t12}. \<close>
          do {guard ((rc.Minus d1 d0 rc.core_real_set) > const_Movement_stuckDist); 
              outp internal_Movement TID_Movement_t12 ; Ret (id)} \<box>
          \<comment> \<open> \<close>
          do {guard ((rc.Minus d1 d0 rc.core_real_set) \<le> const_Movement_stuckDist); 
              outp stuck_timeout__Movement (TID_Movement_t13, din) ; Ret (id)} \<box>
          do {inp_in set_d1_Movement rc.core_real_set; Ret (id)} \<box>
          do {inp_in set_d0_Movement rc.core_real_set; Ret (id)}
        )
    }
  )
"

subsubsection \<open> States \<close>
paragraph \<open> Initial \<close>text\<open>\mbox{}\<close>
definition I_Movement_i1 where
"I_Movement_i1 = (\<lambda> (id::integer) . 
  do {outp internal_Movement TID_Movement_t1 ; 
      outp enter_Movement (SID_Movement, SID_Movement_Waiting);
      outp entered_Movement (SID_Movement, SID_Movement_Waiting)
  })
"

paragraph \<open> Waiting \<close>text\<open>\mbox{}\<close>
abbreviation CS_Movement_Waiting_sync where
"CS_Movement_Waiting_sync \<equiv> 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_Waiting] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_Waiting])
)"

abbreviation Movement_Waiting_triggers where
"Movement_Waiting_triggers \<equiv> set (
  (enumchans3 [obstacle__Movement_C] [TID_Movement_t6, TID_Movement_t11] InOut_list Location_Loc_list) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t22, TID_Movement_t20, TID_Movement_t10, 
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
        \<comment> \<open> @{verbatim State_Movement_Waiting_execute} \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_Movement (snd (snd s), SID_Movement_Waiting);
              (do {guard(True); CALL__randomWalk_Movement(id) ; stop} \<triangle>
                (
                \<comment> \<open> @{verbatim T_Movement_t2} \<close>
                do {t \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t2, din, a). 
                                a \<leftarrow> (Chemical_Angle_list)]) ;
                      outp set_a_Movement (snd (snd t)) ; 
                      outp exit_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      outp exited_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      outp enter_Movement (SID_Movement_Waiting, SID_Movement_Going);
                      outp entered_Movement (SID_Movement_Waiting, SID_Movement_Going);
                      Ret(False, fst (snd s), SID_Movement_Waiting)
                    } \<box>
                \<comment> \<open> @{verbatim T_Movement_t0} \<close>
                do {outp resume__Movement (TID_Movement_t0, din) ;
                      outp exit_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      outp exited_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      outp enter_Movement (SID_Movement_Waiting, SID_Movement_Waiting);
                      Ret(True, fst (snd s), SID_Movement_Waiting)
                    } \<box>
                \<comment> \<open> @{verbatim T_Movement_t15} \<close>
                do {outp stop__Movement (TID_Movement_t15, din) ;
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
   (discard_state (State_Movement_Waiting idd))
    \<parallel>\<^bsub> (int_int_Movement - Movement_Waiting_triggers) \<^esub> 
   skip
"

paragraph \<open> Going \<close>text\<open>\mbox{}\<close>
abbreviation CS_Movement_Going_sync where
"CS_Movement_Going_sync \<equiv> 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_Going] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_Going])
)"

abbreviation Movement_Going_triggers where
"Movement_Going_triggers \<equiv> set (
  (enumchan1 internal_Movement_C [TID_Movement_t12, TID_Movement_t5, TID_Movement_t13]) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t22, TID_Movement_t20, TID_Movement_t10,
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
        \<comment> \<open> @{verbatim State_Movement_Going_execute} \<close>
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
                \<comment> \<open> @{verbatim T_Movement_t3} \<close>
                do {t \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t2, din, a). 
                                a \<leftarrow> (Chemical_Angle_list)]) ;
                      outp set_a_Movement (snd (snd t)) ; 
                      outp exit_Movement (SID_Movement_Going, SID_Movement_Going);
                      outp exited_Movement (SID_Movement_Going, SID_Movement_Going);
                      outp enter_Movement (SID_Movement_Going, SID_Movement_Going);
                      Ret(True, fst (snd s), SID_Movement_Going)
                    } \<box>
                \<comment> \<open> @{verbatim T_Movement_t4} \<close>
                do {outp stop__Movement (TID_Movement_t4, din) ;
                      outp exit_Movement (SID_Movement_Going, SID_Movement_Going);
                      outp exited_Movement (SID_Movement_Going, SID_Movement_Going);
                      outp enter_Movement (SID_Movement_Going, SID_Movement_Found);
                      outp entered_Movement (SID_Movement_Going, SID_Movement_Found);
                      Ret(False, fst (snd s), SID_Movement_Going)
                    } \<box>
                \<comment> \<open> @{verbatim T_Movement_t6} \<close>
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
   (discard_state (State_Movement_Going idd))
    \<parallel>\<^bsub> (int_int_Movement - Movement_Going_triggers) \<^esub> 
   skip
"

paragraph \<open> Found \<close>text\<open>\mbox{}\<close>
abbreviation CS_Movement_Found_sync where
"CS_Movement_Found_sync \<equiv> 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_Found] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_Found])
)"

abbreviation Movement_Found_triggers where
"Movement_Found_triggers \<equiv> set (
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
        \<comment> \<open> @{verbatim State_Movement_Found_execute} \<close>
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
                \<comment> \<open> @{verbatim T_Movement_t5} \<close>
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
   (discard_state (State_Movement_Found idd))
    \<parallel>\<^bsub> (int_int_Movement - Movement_Found_triggers) \<^esub> 
   skip
"
paragraph \<open> Final (j1) \<close>text\<open>\mbox{}\<close>
abbreviation CS_Movement_j1_sync where
"CS_Movement_j1_sync \<equiv>
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_j1] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_j1])
)"

abbreviation Movement_j1_triggers where
"Movement_j1_triggers \<equiv> set ([])
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
        \<comment> \<open> @{verbatim State_Movement_j1_execute} \<close>
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
   (discard_state (State_Movement_j1 idd))
    \<parallel>\<^bsub> (int_int_Movement - Movement_j1_triggers) \<^esub> 
   skip
"

paragraph \<open> Avoiding \<close>text\<open>\mbox{}\<close>
abbreviation CS_Movement_Avoiding_sync where
"CS_Movement_Avoiding_sync \<equiv> 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_Avoiding] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_Avoiding])
)"

abbreviation Movement_Avoiding_triggers where
"Movement_Avoiding_triggers \<equiv> set (
    (enumchan1 internal_Movement_C [TID_Movement_t12, TID_Movement_t5, TID_Movement_t13]) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t22, TID_Movement_t20, TID_Movement_t10,
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

text \<open>The entry action of the state @{text Avoiding} contains a call @{text "changeDirection(l)"} 
to the operation. This is implemented by calling @{term CALL__changeDirection_Movement}. \<close>
definition State_Movement_Avoiding where 
"State_Movement_Avoiding = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_Avoiding_Movement ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> @{verbatim State_Movement_Avoiding_execute} \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              guard(True); r \<leftarrow> inp_in odometer_Movement (set 
                  [(din, l). l \<leftarrow> rc.core_real_list]);  
              outp set_d0_Movement (snd r);
              l \<leftarrow> inp_in get_l_Movement Location_Loc_set;
              guard(True); CALL__changeDirection_Movement id l;
              outp entered_Movement (snd (snd s), SID_Movement_Avoiding);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> @{verbatim T_Movement_t7} \<close>
                do {r \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t7, din, a). 
                            a \<leftarrow> (Chemical_Angle_list)]);
                      outp set_a_Movement (snd (snd r)); 
                      outp exit_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                      outp exited_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                      outp enter_Movement (SID_Movement_Avoiding, SID_Movement_TryingAgain);
                      outp entered_Movement (SID_Movement_Avoiding, SID_Movement_TryingAgain);
                      Ret(False, fst (snd s), SID_Movement_Avoiding)
                    } \<box>
                \<comment> \<open> @{verbatim T_Movement_t18} \<close>
                do {outp stop__Movement (TID_Movement_t18, din);
                    outp exit_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                    outp exited_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                    outp enter_Movement (SID_Movement_Avoiding, SID_Movement_Found);
                    outp entered_Movement (SID_Movement_Avoiding, SID_Movement_Found);
                    Ret(False, fst (snd s), SID_Movement_Avoiding)
                  } \<box>
                \<comment> \<open> @{verbatim T_Movement_t19} \<close>
                do {outp resume__Movement (TID_Movement_t19, din);
                    outp exit_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                    outp exited_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                    outp enter_Movement (SID_Movement_Avoiding, SID_Movement_Waiting);
                    outp entered_Movement (SID_Movement_Avoiding, SID_Movement_Waiting);
                    Ret(False, fst (snd s), SID_Movement_Avoiding)
                  } \<box> 
                \<comment> \<open>We use the biased external choice to avoid deadlock, and give priority to 
                resume to Waiting state. However, the biased operator cannot work at this level
                because the @{text resume__Movement} events for t19 and t21 are different 
                thanks to the transition id.
                \<close>
                \<comment> \<open> @{verbatim T_Movement_t21} \<close>
                \<comment> \<open> @{text \<open>do {outp internal_Movement (TID_Movement_t21);
                    outp exit_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                    outp exited_Movement (SID_Movement_Avoiding, SID_Movement_Avoiding);
                    outp enter_Movement (SID_Movement_Avoiding, SID_Movement_Going);
                    outp entered_Movement (SID_Movement_Avoiding, SID_Movement_Going);
                    Ret(False, fst (snd s), SID_Movement_Avoiding)
                  } \<box> \<close>}\<close>
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
   (discard_state (State_Movement_Avoiding idd))
    \<parallel>\<^bsub> (int_int_Movement - Movement_Avoiding_triggers) \<^esub> 
   skip
"

paragraph \<open> TryingAgain \<close>text\<open>\mbox{}\<close>
abbreviation CS_Movement_TryingAgain_sync where
"CS_Movement_TryingAgain_sync \<equiv>
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_TryingAgain] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_TryingAgain])
)"

abbreviation Movement_TryingAgain_triggers where
"Movement_TryingAgain_triggers \<equiv> set (
    (enumchan1 internal_Movement_C [TID_Movement_t12, TID_Movement_t5, TID_Movement_t13]) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t22, TID_Movement_t20, TID_Movement_t10,
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
        \<comment> \<open> @{verbatim State_Movement_TryingAgain_execute} \<close>
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
                \<comment> \<open> @{verbatim T_Movement_t8} \<close>
                do {r \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t7, din, a). 
                            a \<leftarrow> (Chemical_Angle_list)]);
                      outp set_a_Movement (snd (snd r)); 
                      outp exit_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                      outp exited_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                      outp enter_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                      Ret(True, fst (snd s), SID_Movement_TryingAgain)
                    } \<box>
                \<comment> \<open> @{verbatim T_Movement_t9} \<close>
                do {outp stop__Movement (TID_Movement_t9, din);
                    outp exit_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                    outp exited_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                    outp enter_Movement (SID_Movement_TryingAgain, SID_Movement_Found);
                    outp entered_Movement (SID_Movement_TryingAgain, SID_Movement_Found);
                    Ret(False, fst (snd s), SID_Movement_TryingAgain)
                  } \<box>
                \<comment> \<open> @{verbatim T_Movement_t10} \<close>
                do {outp resume__Movement (TID_Movement_t10, din);
                    outp exit_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                    outp exited_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                    outp enter_Movement (SID_Movement_TryingAgain, SID_Movement_Waiting);
                    outp entered_Movement (SID_Movement_TryingAgain, SID_Movement_Waiting);
                    Ret(False, fst (snd s), SID_Movement_TryingAgain)
                  } \<box>
                \<comment> \<open> @{verbatim T_Movement_t11} \<close>
                do {r \<leftarrow> inp_in obstacle__Movement (set [(TID_Movement_t11, din, l). 
                        l \<leftarrow> Location_Loc_list]);
                      outp set_l_Movement (snd (snd r)) ; 
                    outp exit_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                    outp exited_Movement (SID_Movement_TryingAgain, SID_Movement_TryingAgain);
                    guard(True); r \<leftarrow> inp_in odometer_Movement (set 
                          [(din, l). l \<leftarrow> rc.core_real_list]);
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
   (discard_state (State_Movement_TryingAgain idd))
    \<parallel>\<^bsub> (int_int_Movement - Movement_TryingAgain_triggers) \<^esub> 
   skip
"

paragraph \<open> AvoidingAgain \<close>text\<open>\mbox{}\<close>
abbreviation CS_Movement_AvoidingAgain_sync where
"CS_Movement_AvoidingAgain_sync \<equiv> 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_AvoidingAgain] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_AvoidingAgain])
)"

abbreviation Movement_AvoidingAgain_triggers where
"Movement_AvoidingAgain_triggers \<equiv> set (
    (enumchan1 internal_Movement_C [TID_Movement_t12, TID_Movement_t5, TID_Movement_t13]) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t22, TID_Movement_t20, TID_Movement_t10,
     TID_Movement_t19] InOut_list) @
  (enumchans3 [turn__Movement_C] [TID_Movement_t3, TID_Movement_t14, TID_Movement_t7, TID_Movement_t8,
    TID_Movement_t2] InOut_list Chemical_Angle_list) @
  (enumchans2 [stop__Movement_C] 
    [TID_Movement_t16, TID_Movement_t17, TID_Movement_t18, TID_Movement_t15, TID_Movement_t4, 
    TID_Movement_t9] InOut_list) @
  (enumchans3 [obstacle__Movement_C] [TID_Movement_t6, TID_Movement_t11] InOut_list Location_Loc_list)
  \<comment> \<open> an extra timeout event\<close>  
  @ (enumchan2 stuck_timeout__Movement_C [TID_Movement_t13] InOut_list)
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

text \<open> At this state @{text AvoidingAgain}, there are four outgoing transitions: 
\begin{itemize}
  \item one with trigger resume, 
  \item one with trigger stop, and 
  \item another two @{text t12} and @{text t13} without triggers.
\end{itemize}
Eventually, this process will synchronise with @{term Movement_MemoryTransitions_opt_2} on 
@{text internal__.t12} and @{text internal__.t13} events, and hide the events in 
@{term MemorySTM_opt_Movement}.

Based on the maximal progress assumption, the transitions with trigger @{text resume} and 
@{text stop} cannot be available because the guards of @{text t12} and @{text t13} form a cover after 
time expressions are removed.
We, therefore, add an extra timeout event @{text stuck_timeout__Movement} to introduce time in an 
abstract way to avoid this issue.
\<close>
definition State_Movement_AvoidingAgain where 
"State_Movement_AvoidingAgain = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_Movement Other_SIDs_to_AvoidingAgain_Movement ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> @{verbatim State_Movement_AvoidingAgain_execute} \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_Movement (snd (snd s), SID_Movement_AvoidingAgain);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> @{verbatim T_Movement_t12} \<close>
                do {outp internal_Movement TID_Movement_t12;
                      outp exit_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                      outp exited_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                      outp enter_Movement (SID_Movement_AvoidingAgain, SID_Movement_Avoiding);
                      outp entered_Movement (SID_Movement_AvoidingAgain, SID_Movement_Avoiding);
                      Ret(False, fst (snd s), SID_Movement_AvoidingAgain)
                    } \<box>
                \<comment> \<open>@{verbatim T_Movement_t17} \<close>
                do {outp stop__Movement (TID_Movement_t17, din);
                    outp exit_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                    outp exited_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                    outp enter_Movement (SID_Movement_AvoidingAgain, SID_Movement_Found);
                    outp entered_Movement (SID_Movement_AvoidingAgain, SID_Movement_Found);
                    Ret(False, fst (snd s), SID_Movement_AvoidingAgain)
                  } \<box>
                \<comment> \<open>@{verbatim T_Movement_t22} \<close>
                do {outp resume__Movement (TID_Movement_t22, din);
                    outp exit_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                    outp exited_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                    outp enter_Movement (SID_Movement_AvoidingAgain, SID_Movement_Waiting);
                    outp entered_Movement (SID_Movement_AvoidingAgain, SID_Movement_Waiting);
                    Ret(False, fst (snd s), SID_Movement_AvoidingAgain)
                  } \<box>
                \<comment> \<open>@{verbatim T_Movement_t13} \<close>
                \<comment> \<open> @{text \<open>
                do {outp internal_Movement TID_Movement_t13;
                      outp exit_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                      outp exited_Movement (SID_Movement_AvoidingAgain, SID_Movement_AvoidingAgain);
                      outp enter_Movement (SID_Movement_AvoidingAgain, SID_Movement_GettingOut);
                      outp entered_Movement (SID_Movement_AvoidingAgain, SID_Movement_GettingOut);
                      Ret(False, fst (snd s), SID_Movement_AvoidingAgain)
                    } \<close> }\<close> 
                  do {outp stuck_timeout__Movement (TID_Movement_t13, din);
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
   (discard_state (State_Movement_AvoidingAgain idd))
    \<parallel>\<^bsub> (int_int_Movement - Movement_AvoidingAgain_triggers) \<^esub> 
   skip
"

paragraph \<open> GettingOut \<close>text\<open>\mbox{}\<close>
abbreviation CS_Movement_GettingOut_sync where
"CS_Movement_GettingOut_sync \<equiv>
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_Movement [SID_Movement_GettingOut] SIDS_Movement_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_Movement SIDS_Movement_nodes [SID_Movement_GettingOut])
)"

abbreviation Movement_GettingOut_triggers where
"Movement_GettingOut_triggers \<equiv> set (
    (enumchan1 internal_Movement_C [TID_Movement_t12, TID_Movement_t5, TID_Movement_t13]) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t22, TID_Movement_t20, TID_Movement_t10,
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
        \<comment> \<open> @{verbatim State_Movement_GettingOut_execute} \<close>
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
                \<comment> \<open> @{verbatim T_Movement_t14} \<close>
                do {r \<leftarrow> inp_in turn__Movement (set [(TID_Movement_t14, din, a). 
                            a \<leftarrow> (Chemical_Angle_list)]);
                      outp set_a_Movement (snd (snd r)); 
                      outp exit_Movement (SID_Movement_GettingOut, SID_Movement_GettingOut);
                      outp exited_Movement (SID_Movement_GettingOut, SID_Movement_GettingOut);
                      outp enter_Movement (SID_Movement_GettingOut, SID_Movement_Going);
                      outp entered_Movement (SID_Movement_GettingOut, SID_Movement_Going);
                      Ret(False, fst (snd s), SID_Movement_GettingOut)
                    } \<box>
                \<comment> \<open> @{verbatim T_Movement_t16} \<close>
                do {outp stop__Movement (TID_Movement_t16, din);
                    outp exit_Movement (SID_Movement_GettingOut, SID_Movement_GettingOut);
                    outp exited_Movement (SID_Movement_GettingOut, SID_Movement_GettingOut);
                    outp enter_Movement (SID_Movement_GettingOut, SID_Movement_Found);
                    outp entered_Movement (SID_Movement_GettingOut, SID_Movement_Found);
                    Ret(False, fst (snd s), SID_Movement_GettingOut)
                  } \<box>
                \<comment> \<open> @{verbatim T_Movement_t20} \<close>
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
   (discard_state (State_Movement_GettingOut idd))
    \<parallel>\<^bsub> (int_int_Movement - Movement_GettingOut_triggers) \<^esub> 
   skip
"

subsubsection \<open> State machine \<close>
abbreviation flow_events_Movement_stm_to_nodes where
"flow_events_Movement_stm_to_nodes \<equiv> (
 let nodes = [SID_Movement_Waiting,SID_Movement_Going,SID_Movement_Found,SID_Movement_j1,
    SID_Movement_Avoiding,SID_Movement_TryingAgain,SID_Movement_AvoidingAgain,
    SID_Movement_GettingOut]
 in set (
      enumchans2 [enter_Movement_C, entered_Movement_C,exit_Movement_C,exited_Movement_C] 
          (filter (\<lambda> s. s \<notin> set nodes) SIDS_Movement_list) nodes
  )
)"

text \<open>We define here seven functions from @{term STM_Movement_1} to @{term STM_Movement_7} which 
are to be used in the definition of @{term STM_Movement}. We can merge these definitions into 
@{term STM_Movement}. One benefit of these definitions is to facilitate debug of parallel composition 
of individual states, such as @{term STM_Movement_1} for composition of @{text AvoidingAgain} and 
@{text GettingOut}.
\<close>
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
              (CS_Movement_AvoidingAgain_sync \<union> 
                CS_Movement_GettingOut_sync))))) \<^esub> 
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
(*
definition STM_Movement' where
"STM_Movement' (idd::integer) = 
   (I_Movement_i1(idd))
    \<parallel>\<^bsub> flow_events_Movement_stm_to_nodes \<^esub> 
   ((State_Movement_Waiting_R(idd)  
    \<parallel>\<^bsub> CS_Movement_Waiting_sync \<inter>
      (CS_Movement_Going_sync \<union>
        (CS_Movement_Found_sync \<union>
          (CS_Movement_j1_sync \<union>
            (CS_Movement_Avoiding_sync \<union>
              (CS_Movement_TryingAgain_sync \<union> 
                (CS_Movement_AvoidingAgain_sync \<union> 
                  CS_Movement_GettingOut_sync)))))) \<^esub> 
      (State_Movement_Going_R(idd)  
        \<parallel>\<^bsub> CS_Movement_Going_sync \<inter>
          (CS_Movement_Found_sync \<union>
            (CS_Movement_j1_sync \<union>
              (CS_Movement_Avoiding_sync \<union>
                (CS_Movement_TryingAgain_sync \<union> 
                  (CS_Movement_AvoidingAgain_sync \<union> 
                    CS_Movement_GettingOut_sync))))) \<^esub> 
      (State_Movement_Found_R(idd)  
        \<parallel>\<^bsub> CS_Movement_Found_sync \<inter>
          (CS_Movement_j1_sync \<union>
            (CS_Movement_Avoiding_sync \<union>
              (CS_Movement_TryingAgain_sync \<union> 
                (CS_Movement_AvoidingAgain_sync \<union> 
                  CS_Movement_GettingOut_sync)))) \<^esub> 
      (State_Movement_j1_R(idd)  
        \<parallel>\<^bsub> CS_Movement_j1_sync \<inter>
          (CS_Movement_Avoiding_sync \<union>
            (CS_Movement_TryingAgain_sync \<union> 
              (CS_Movement_AvoidingAgain_sync \<union> 
                CS_Movement_GettingOut_sync))) \<^esub> 
      (State_Movement_Avoiding_R(idd)  
        \<parallel>\<^bsub> CS_Movement_Avoiding_sync \<inter> 
          (CS_Movement_TryingAgain_sync \<union> 
            (CS_Movement_AvoidingAgain_sync \<union> 
              CS_Movement_GettingOut_sync)) \<^esub> 
      (State_Movement_TryingAgain_R(idd)  
        \<parallel>\<^bsub> CS_Movement_TryingAgain_sync \<inter> 
          (CS_Movement_AvoidingAgain_sync \<union> 
            CS_Movement_GettingOut_sync) \<^esub> 
      (State_Movement_AvoidingAgain_R(idd)  
        \<parallel>\<^bsub> CS_Movement_AvoidingAgain_sync \<inter> 
          CS_Movement_GettingOut_sync \<^esub> 
       State_Movement_GettingOut_R(idd)))))))))
"
*)

abbreviation Movement_opt_0_internal_set where
"Movement_opt_0_internal_set \<equiv> 
  set ((enumchans1 [internal_Movement_C] [TID_Movement_t1, TID_Movement_t5]) @ 
      (enumchans2 [stop__Movement_C] 
          [TID_Movement_t18, TID_Movement_t17, TID_Movement_t16, TID_Movement_t9, TID_Movement_t15,
          TID_Movement_t4] InOut_list) @
       (enumchans3 [turn__Movement_C] 
          [TID_Movement_t3, TID_Movement_t2, TID_Movement_t14, TID_Movement_t7, TID_Movement_t8] 
          InOut_list Chemical_Angle_list) @
       (enumchans2 [resume__Movement_C] 
          [TID_Movement_t10, TID_Movement_t22, TID_Movement_t20, TID_Movement_t0,
          TID_Movement_t19] InOut_list) @
       (enumchans3 [obstacle__Movement_C] [TID_Movement_t6, TID_Movement_t11] 
          InOut_list Location_Loc_list) @
       (enumchans1 [internal_changeDirection_C] [TID_changeDirection_t2])
)"

abbreviation Movement_opt_2_internal_set where
"Movement_opt_2_internal_set \<equiv> 
  set ((enumchans1 [internal_Movement_C] [TID_Movement_t12, TID_Movement_t13]) @
       (enumchans1 [set_d0_Movement_C, set_d1_Movement_C] rc.core_real_list) 
    \<comment> \<open> timeout \<close>
    @ (enumchan2 stuck_timeout__Movement_C [TID_Movement_t13] InOut_list)
)"

abbreviation "changeDirection_opt_internal_set \<equiv> (enumchans1 [internal_changeDirection_C] 
          [TID_changeDirection_t3, TID_changeDirection_t4, TID_changeDirection_t1])"

abbreviation Movement_opt_1_internal_set where
"Movement_opt_1_internal_set \<equiv> 
  set (changeDirection_opt_internal_set @
       (enumchans1 [set_l_changeDirection_C] Location_Loc_list)
)"
(*
definition MemorySTM_opt_Movement' where
"MemorySTM_opt_Movement' (idd::integer) = 
(
   ( 
      (
        (
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
          ) \<setminus> (set [internal_Movement_C TID_Movement_t5, internal_Movement_C TID_Movement_t1,
               internal_changeDirection_C TID_changeDirection_t2])
        )
        \<parallel>\<^bsub> Movement_opt_2_internal_set \<^esub> 
        (discard_state (Movement_MemoryTransitions_opt_2 idd))
      ) \<setminus> (set (enumchans1 [internal_Movement_C] [TID_Movement_t12, TID_Movement_t13]))
   )
)"
*)
text \<open>The memory cell process and the memory transition process of @{text changeDirection} is also 
part of the memory of @{text Movement}, which is reflected in the definition of 
@{term MemorySTM_opt_Movement} below.
\<close>
definition MemorySTM_opt_Movement where
"MemorySTM_opt_Movement (idd::integer) = 
  (par_hide
    (discard_state (changeDirection_Memory_opt_l (Location_Loc_left)))
    changeDirection_l_events
    (
      (
        (par_hide
          (discard_state (Movement_Memory_opt_d1 (0)))
          Movement_d1_events 
          (par_hide
            (discard_state (Movement_Memory_opt_d0 (0)))
            Movement_d0_events
            ( 
              (
                (
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
                  ) \<setminus> (set [internal_Movement_C TID_Movement_t5, internal_Movement_C TID_Movement_t1,
                       internal_changeDirection_C TID_changeDirection_t2])
                )
                \<parallel>\<^bsub> Movement_opt_2_internal_set \<^esub> 
                (discard_state (Movement_MemoryTransitions_opt_2 idd))
              ) \<setminus> (set (enumchans1 [internal_Movement_C] [TID_Movement_t12, TID_Movement_t13]))
            )
          )
        )
        \<parallel>\<^bsub> Movement_opt_1_internal_set \<^esub>
        (discard_state (changeDirection_MemoryTransitions_opt_1 idd))
      ) \<setminus> (set changeDirection_opt_internal_set)
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
    @ (enumchan1 (forget_first stuck_timeout__Movement_C stuck_timeout_Movement_C TIDS_Movement_list) 
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
  (enumchansp1 [randomWalkCall_Movement_C, shortRandomWalkCall_Movement_C] [()]) @
  (enumchansp2 [moveCall_Movement_C] rc.core_real_list Chemical_Angle_list)
"

definition rename_MemorySTM_opt_Movement where
"rename_MemorySTM_opt_Movement idd = ( 
  (MemorySTM_opt_Movement idd) \<lbrace>(set (rename_Movement_events @ rename_Movement_events_others))\<rbrace>
)
" 

text \<open>The @{text internal_} channel of @{text changeDirection} is hidden in @{term AUX_opt_Movement}.
\<close>
definition AUX_opt_Movement where
"AUX_opt_Movement (idd::integer) = 
  ( 
    ( 
      (rename_MemorySTM_opt_Movement idd) \<lbrakk> set [terminate_Movement_C ()] \<Zrres> skip
    ) \<setminus> (Movement_MachineInternalEvents \<union> changeDirection_MachineInternalEvents)
  )                                                      
"

text \<open>This @{term AUX_opt_Movement_sim} below is defined to animate @{term AUX_opt_Movement}. This 
is not part of the semantics of the model, but just for animation. \<close>
definition "AUX_opt_Movement_sim = AUX_opt_Movement 0"
text \<open>Uncomment the line below to animate @{term AUX_opt_Movement}.\<close>
(* animate1 AUX_opt_Movement_sim *)

definition D__Movement where
"D__Movement (idd::integer) = 
  (AUX_opt_Movement idd) \<setminus> internal_events_Movement
"

text \<open>This @{term D_Movement_sim} below is defined to animate @{term D__Movement}. \<close>
definition "D_Movement_sim = D__Movement 0"
text \<open>Uncomment the line below to animate @{term D__Movement}.\<close>
(* animate1 D_Movement_sim *)

subsection \<open> MicroController \label{ssec:chem_microcontroller}\<close>
chantype Chan_MicroCtrl =
  terminate_MicroController :: unit
  obstacle_MicroController :: "InOut \<times> Location_Loc"
  resume_MicroController :: "InOut"
  turn_MicroController :: "InOut \<times> Chemical_Angle"
  odometer_MicroController :: "InOut \<times> core_real"
  stop_MicroController :: "InOut"
  flag_MicroController :: "InOut"
(* operation call events *)
  randomWalkCall_MicroController :: unit
  moveCall_MicroController :: "core_real \<times> Chemical_Angle"
  shortRandomWalkCall_MicroController :: unit
(* timeout *)
  stuck_timeout_MicroController :: "InOut"

subsubsection \<open> Memory \<close>
text \<open>This controller does not have a memory cell process or memory transition processes. \<close>
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
  (enumchansp2_1 [(flag_Movement_C, flag_MicroController_C)] InOut_list) @
  (enumchansp2_1 [(randomWalkCall_Movement_C, randomWalkCall_MicroController_C), 
      (shortRandomWalkCall_Movement_C, shortRandomWalkCall_MicroController_C)] [()]) @
  (enumchanp2_2 (moveCall_Movement_C, moveCall_MicroController_C) rc.core_int_list 
    Chemical_Angle_list)
  \<comment> \<open> timeout \<close>
  @ (enumchansp2_1 [(stuck_timeout_Movement_C, stuck_timeout_MicroController_C)] InOut_list)
"

definition rename_D__Movement where
  "rename_D__Movement idd = ((D__Movement idd) \<lbrace>(set rename_MicroController_Movement_events)\<rbrace>)"

definition D__MicroController where
"D__MicroController (idd::integer) = 
  (par_hide
    (rename_D__Movement idd)
    {}
    (discard_state (Memory_MicroController idd))
  )  \<lbrakk> set [terminate_MicroController_C ()] \<Zrres> skip
"

definition "D_MicroController_sim = D__MicroController 0"
animate1 D_MicroController_sim

subsubsection \<open> Export code \<close>
export_code
  Movement_Memory_opt_d0
  Movement_MemoryTransitions_opt_0
  changeDirection_MemoryTransitions_opt_1
  Movement_MemoryTransitions_opt_2
  I_Movement_i1
  State_Movement_AvoidingAgain_R
  State_Movement_Waiting_R
  State_Movement_TryingAgain_R
  State_Movement_Avoiding_R
  State_Movement_j1_R
  State_Movement_Found_R
  State_Movement_Going_R
  STM_Movement_1
  STM_Movement_2
  STM_Movement_3
  STM_Movement_4
  STM_Movement_5
  STM_Movement_6
  STM_Movement_7
  STM_Movement
  MemorySTM_opt_Movement(*
  MemorySTM_opt_Movement'*)
  changeDirection_MemoryTransitions_opt_1
  rename_MemorySTM_opt_Movement
  AUX_opt_Movement
  D__Movement
  D__MicroController
  I_changeDirection_i0
  STM_changeDirection_1
  STM_changeDirection 
  AUX_changeDirection
  D__changeDirection
in Haskell 
  (* module_name Movement *)
  file_prefix RoboChart_ChemicalDetector 
  (string_classes) 

generate_file \<open>code/RoboChart_ChemicalDetector/Simulate.hs\<close> = 
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

generate_file \<open>code/RoboChart_ChemicalDetector/Main.hs\<close> = 
\<open>import qualified Interaction_Trees;
import qualified Partial_Fun;
import qualified Simulate;
import qualified RoboChart_ChemicalDetector_autonomous_microcontroller;

main :: IO ()
main =
  do
    Simulate.simulate (RoboChart_ChemicalDetector_autonomous_microcontroller.d_MicroController 0);
\<close>

export_generated_files 
  \<open>code/RoboChart_ChemicalDetector/Simulate.hs\<close>
  \<open>code/RoboChart_ChemicalDetector/Main.hs\<close>

end
