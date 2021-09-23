section \<open> Simulation of a very basic RoboChart model \<close>
text \<open> This theory aims for simulation of a trivial RoboChart model (see 
Figure~\ref{fig:robochart_basic}) based on its CSP semantics. 
\begin{figure}
  \includegraphics[scale=0.50]{images/system.pdf}
  \caption{The RoboChart model of a trivial example}
  \label{fig:robochart_basic}
\end{figure}

This model contains one robotic
platform @{text rp0} and one controller @{text ctr0}. The controller is further composed of two 
state machines: @{text stm0} and @{text stm1}. A shared variable @{text x} is provided by @{text rp0} 
and required by the controller and its two state machines. The machine @{text stm0} additionally has 
a local variable @{text l}. The controller communicates with the platform through two input events:
@{text e1} and @{text e2}, which are further connected to @{text stm0} and @{text stm1}. The two 
state machines are also connected through an event: @{text e3} (from @{text stm0} to @{text stm1}).

We note this theory is not directly translated from the RoboChart model. Instead, it is translated 
from the standard CSP semantics (under @{verbatim "csp-gen/defs"}) of the model which is generated in 
RoboTool.
\<close>
theory RoboChart_basic
  imports "ITree_RoboChart.ITree_RoboChart"
begin

subsection \<open> General definitions \<close>
text \<open> Instantiation of @{term "min_int"}, @{term "max_int"}, @{term "max_nat"}, @{term "min_real"}, 
@{term "max_real"},, to -1, 1, 1, -1, and 1 separately.
\<close>
interpretation rc: robochart_confs "-1" "1" "1" "-1" "1".

subsection \<open> stm0 \<close>
text \<open> @{term "SIDS_stm0"} defines state identifiers for state machine @{text "stm0"}, which include 
the machine itself and the state @{text "s0"}.\<close>
datatype SIDS_stm0 = SID_stm0
                   | SID_stm0_s0

text \<open> @{term "SIDS_stm0_list"} defines a list of all possible values in @{term "SIDS_stm0"}.\<close>
definition "SIDS_stm0_list = [SID_stm0, SID_stm0_s0]"

text \<open> @{term "SIDS_stm0_set"} defines a set of all possible values in @{term "SIDS_stm0"}.\<close>
definition "SIDS_stm0_set = set SIDS_stm0_list"

definition "SIDS_stm0_without_s0 = (removeAll SID_stm0_s0 SIDS_stm0_list)"

text \<open> @{term "TIDS_stm0"} defines transition identifiers for state machine @{text "stm0"}.\<close>
datatype TIDS_stm0 = NULLTRANSITION_stm0
                   | TID_stm0_t0
                   | TID_stm0_t1
                   | TID_stm0_t2

definition "TIDS_stm0_list = [NULLTRANSITION_stm0, TID_stm0_t0, TID_stm0_t1, TID_stm0_t2]"
definition "TIDS_stm0_set = set TIDS_stm0_list"

text \<open> @{term "ITIDS_stm0_list"} gives a list of transition IDs that can interrupt a state. \<close>
definition "ITIDS_stm0_list = [TID_stm0_t1, TID_stm0_t2]"
definition "ITIDS_stm0_set = set ITIDS_stm0_list"  

text \<open> @{term "Chan_stm0"} is a channel type for the state machine, and it declares various channels 
including flow channels, variable channels, and event channels.
\<close>
chantype Chan_stm0 =
(* flow channels *)
  internal_stm0 :: TIDS_stm0
  enter_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  entered_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  exit_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  exited_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  terminate_stm0 :: unit
(* variable channels : the next 3 channels will be hidden *)
  get_l_stm0 :: core_int
  set_l_stm0 :: core_int
  get_x_stm0 :: core_int
(* this won't be hidden, and will be renamed to set_x_ctr0 *)
  set_x_stm0 :: core_int
(* shared variable channels, and will be renamed to set_EXT_x_ctr0_stm0 *)
  set_EXT_x_stm0 :: core_int
(* event channels *)
  (* will be renamed to e1_stm0 (may introduce nondeterminism) *)
  e1__stm0 :: "TIDS_stm0 \<times> InOut \<times> core_int"
  (* will be further renamed to e1_ctr0 *)
  e1_stm0 :: "InOut \<times> core_int"
  (* will be renamed to e3_ctr0.out *)
  e3__stm0 :: "TIDS_stm0 \<times> InOut \<times> core_int"
  e3_stm0 :: "InOut \<times> core_int"

text \<open> Here, we use the following 
conventions.
\begin{itemize}
  \item a channel type: @{term "Chan_stm0"},
  \item channels (declared in @{term "Chan_stm0"}): @{term "internal_stm0"}, @{term "e1_stm0"}, etc.
  \begin{itemize}
    \item an internal trigger channel: @{term "internal_stm0"};
    \item flow control channels: @{term "enter_stm0"}, @{term "entered_stm0"}, @{term "exit_stm0"}, 
      and @{term "exited_stm0"};
    \item a terminate channel: @{term "terminate_stm0"};
    \item local variable channels: @{term "get_l_stm0"}, and @{term "set_l_stm0"};
    \item shared variable channels: @{term "get_x_stm0"}, @{term "set_x_stm0"}, and 
      @{term "set_EXT_x_stm0"};
    \item Event channels: trigger event channels (@{term "e1__stm0"} and @{term "e3__stm0"}), 
      and event channels (@{term "e1_stm0"} and @{term "e3_stm0"}).
  \end{itemize}
  \item a channel event: an event starting with the name of a channel and carrying a value on the 
  channel, such as @{text "internal_stm0 TID_stm0_t1"};
  %\item the data type of a channel (@{term "e1_stm0"}): @{typeof "e1_stm0_C"};
  \item the type of a channel (@{term "e1_stm0"}): @{typeof "e1_stm0"}, a prism from the data type 
    of the channel to the channel type.
\end{itemize}
\<close>

subsubsection \<open> Sets of events \<close>
text \<open> @{term "int_int_stm0"} defines a set of internal channel events that can interrupt states. \<close>
definition int_int_stm0 where
"int_int_stm0 = 
  set ((enumchans3 [e1__stm0_C, e3__stm0_C] [TID_stm0_t1,TID_stm0_t2] [din, dout] rc.core_int_list) @
       (enumchan1 internal_stm0_C [TID_stm0_t1,TID_stm0_t2])
)"

text \<open> @{term "internal_events_stm0"} defines a set of internal flow control events. \<close>
definition internal_events_stm0 where
"internal_events_stm0 = 
  set (enumchans2 [enter_stm0_C, entered_stm0_C, exit_stm0_C, exited_stm0_C] SIDS_stm0_list 
  SIDS_stm0_list)"

(*
definition shared_variable_events_stm0 where
"shared_variable_events_stm0 = 
  set ([set_EXT_x_stm0_C (x). 
          x \<leftarrow> rc.core_int_list]
)"
*)

definition CS_stm0_s0_sync where
"CS_stm0_s0_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 [enter_stm0_C, entered_stm0_C, exit_stm0_C, exited_stm0_C] [SID_stm0_s0] [SID_stm0_s0])@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 [enter_stm0_C, entered_stm0_C, exit_stm0_C, exited_stm0_C] [SID_stm0_s0] [SID_stm0_s0])
)"

text \<open> @{term "stm0_s0_triggers"} defines a set of channel events that act as triggers of transitions
. \<close>
definition stm0_s0_triggers where
"stm0_s0_triggers = 
  set ((enumchan3 e1__stm0_C [TID_stm0_t1,TID_stm0_t2] [din, dout] rc.core_int_list) @
  (enumchan1 internal_stm0_C [TID_stm0_t2])
)
"

text \<open> @{term "stm0_l_events"} defines a set of variable channel events for @{text "l"}. \<close>
definition stm0_l_events where
"stm0_l_events = 
    set (enumchans1 [get_l_stm0_C, set_l_stm0_C] rc.core_int_list)
"

text \<open> @{term "stm0_x_events"} defines a set of variable channel events for @{text "x"}. \<close>
definition stm0_x_events where
"stm0_x_events = 
    set (
        (enumchans1 [get_x_stm0_C, set_x_stm0_C] rc.core_int_list) @
        (enumchan1 set_EXT_x_stm0_C rc.core_int_list)
    )
"

text \<open> @{term "stm0_MachineInternalEvents"} defines a set of @{text "internal_"} channel events. \<close>
definition stm0_MachineInternalEvents where
"stm0_MachineInternalEvents = 
  set (enumchan1 internal_stm0_C TIDS_stm0_list)
"

subsubsection \<open> State Machine Memory \<close>
paragraph \<open> Memory cell processes \<close>

text \<open> @{term "stm0_Memory_opt_x"} is a memory cell process for a shared variable @{term x}.\<close>
definition stm0_Memory_opt_x where
"stm0_Memory_opt_x = 
  mem_of_svar get_x_stm0 set_x_stm0 set_EXT_x_stm0 rc.core_int_set"

text \<open> @{term "stm0_Memory_opt_l"} is a memory cell process for a local variable @{term l}.\<close>
definition stm0_Memory_opt_l where
"stm0_Memory_opt_l = mem_of_lvar get_l_stm0 set_l_stm0 rc.core_int_set"

paragraph \<open> Memory transition processes \<close>
text \<open> @{term "stm0_MemoryTransitions_opt_0"} and @{term "stm0_MemoryTransitions_opt_1"} are memory 
processes for transitions, particularly the guards of transitions evaluated in the process.\<close>
definition stm0_MemoryTransitions_opt_0 where
"stm0_MemoryTransitions_opt_0 = 
  loop (\<lambda> id::integer. 
    (do {outp internal_stm0 TID_stm0_t0 ; Ret (id)} \<box> deadlock)
  )
"

definition stm0_MemoryTransitions_opt_1 where
"stm0_MemoryTransitions_opt_1 = 
  loop (\<lambda> id::integer.
    do {x \<leftarrow> inp_in get_x_stm0 rc.core_int_set ; 
      (
        do {inp_in e1__stm0 (set [(TID_stm0_t1, din, l). l \<leftarrow> rc.core_int_list, (x = 0)])
              ; Ret (id)} \<box>
        do {guard (x \<noteq> 0); outp internal_stm0 TID_stm0_t2 ; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_x_stm0 rc.core_int_set; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_EXT_x_stm0 rc.core_int_set; Ret (id)}
      )
    }
  )
"

subsubsection \<open> States \<close>
definition I_stm0_i0 where
"I_stm0_i0 = (\<lambda> (id::integer) . 
  do {outp internal_stm0 TID_stm0_t0 ; 
      outp set_x_stm0 0; 
      outp enter_stm0 (SID_stm0, SID_stm0_s0);
      outp entered_stm0 (SID_stm0, SID_stm0_s0)
  })
"

definition tids_stm0_s0 where
" tids_stm0_s0 = 
    (filter 
        (\<lambda> s. s \<notin> {NULLTRANSITION_stm0,TID_stm0_t1,TID_stm0_t2}) 
        ITIDS_stm0_list)"

(* We need an interrupt operator for during actions *) 
(* ::"integer \<Rightarrow> SIDS_stm0 \<Rightarrow> (Chan_stm0, SIDS_stm0) itree" *)
definition State_stm0_s0 where 
"State_stm0_s0 = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_stm0 (set 
          [(s, SID_stm0_s0) . s \<leftarrow> (removeAll SID_stm0_s0 SIDS_stm0_list)]) ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> @{text State_stm0_s0_execute} \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_stm0 (snd (snd s), SID_stm0_s0);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> @{text T_stm0_t1} \<close>
                do {t \<leftarrow> inp_in e1__stm0 (set [(TID_stm0_t1, din, l) . l \<leftarrow> rc.core_int_list]) ;
                      outp set_l_stm0 (snd (snd t)) ; 
                      outp exit_stm0 (SID_stm0_s0, SID_stm0_s0);
                      outp exited_stm0 (SID_stm0_s0, SID_stm0_s0);
                      l \<leftarrow> inp_in get_l_stm0 rc.core_int_set ; 
                        outp set_x_stm0 (l);
                        outp enter_stm0 (SID_stm0_s0, SID_stm0_s0);
                        Ret(True, fst (snd s), SID_stm0_s0)
                    } \<box>
                \<comment> \<open> @{text T_stm0_t2} \<close>
                do {outp internal_stm0 TID_stm0_t2;
                    outp exit_stm0 (SID_stm0_s0, SID_stm0_s0);
                    outp exited_stm0 (SID_stm0_s0, SID_stm0_s0);
                      x \<leftarrow> inp_in get_x_stm0 rc.core_int_set ; 
                        outp e3_stm0 (dout, x);
                        outp enter_stm0 (SID_stm0_s0, SID_stm0_s0);
                        Ret(True, fst (snd s), SID_stm0_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in internal_stm0 
                      (set tids_stm0_s0);
                    y \<leftarrow> inp_in exit_stm0 (set 
                      [(s, SID_stm0_s0) . s \<leftarrow> (removeAll SID_stm0_s0 SIDS_stm0_list)]);
                      outp exit_stm0 (fst y, SID_stm0_s0);
                      Ret (False, fst (snd s), SID_stm0_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in e1__stm0 (set [(s, d, l) . 
                        s \<leftarrow> tids_stm0_s0, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> rc.core_int_list]) ;
                    y \<leftarrow> inp_in exit_stm0 (set 
                        [(s, SID_stm0_s0) . s \<leftarrow> (removeAll SID_stm0_s0 SIDS_stm0_list)]);
                      outp exit_stm0 (fst y, SID_stm0_s0);
                      Ret (False, fst (snd s), SID_stm0_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in e3__stm0 (set [(s, d, l) . 
                        s \<leftarrow> tids_stm0_s0, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> rc.core_int_list]) ;
                    y \<leftarrow> inp_in exit_stm0 (set 
                        [(s, SID_stm0_s0) . s \<leftarrow> (removeAll SID_stm0_s0 SIDS_stm0_list)]);
                      outp exit_stm0 (fst y, SID_stm0_s0);
                      Ret (False, fst (snd s), SID_stm0_s0)
                    }
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

definition State_stm0_s0_R where
"State_stm0_s0_R (idd::integer) = 
   (discard_state (State_stm0_s0 idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_stm0 - stm0_s0_triggers) \<^esub> 
   skip
"

definition flow_event_stm0_not_s0 where 
"flow_event_stm0_not_s0 = set (
  enumchans2 [enter_stm0_C, entered_stm0_C,exit_stm0_C,exited_stm0_C] 
             SIDS_stm0_without_s0 [SID_stm0_s0]
)"

definition STM_stm0 where
"STM_stm0 (idd::integer) = 
   (I_stm0_i0(idd))
    \<parallel>\<^bsub> flow_event_stm0_not_s0 \<^esub> 
   State_stm0_s0_R(idd)
"

definition stm0_e1_x_internal_set where
"stm0_e1_x_internal_set = 
  set ((enumchan3 e1__stm0_C [TID_stm0_t1] [din, dout] rc.core_int_list) @ 
       [internal_stm0_C TID_stm0_t2] @
       (enumchan1 set_x_stm0_C rc.core_int_list)
)"

subsubsection \<open> State machine \<close>
definition MemorySTM_opt_stm0 where
"MemorySTM_opt_stm0 (idd::integer) = 
  (
    (
      (discard_state (stm0_Memory_opt_x 0))
      \<parallel>\<^bsub> stm0_x_events \<^esub>
      ( 
        (
          (par_hide
            (par_hide (discard_state (stm0_Memory_opt_l 0)) stm0_l_events (STM_stm0 idd))
            {internal_stm0_C TID_stm0_t0}
            (discard_state (stm0_MemoryTransitions_opt_0 idd))
          )
          \<parallel>\<^bsub> stm0_e1_x_internal_set \<^esub> 
          (discard_state (stm0_MemoryTransitions_opt_1 idd))
        ) \<setminus> {internal_stm0_C TID_stm0_t2}
      )
    ) \<setminus> (set [get_x_stm0_C n. n \<leftarrow> rc.core_int_list])
  )   
"

text \<open> This definition actually defines a non-injective mapping as shown below.
@{text
  "[
    (e1__stm0_C (TID_stm0_t0, din, 0), e1_stm0_C (din, 0)),
    (e1__stm0_C (TID_stm0_t1, din, 0), e1_stm0_C (din, 0)), 
    ...
  ]"
}
here multiple @{term "e1__stm0"} events are mapped to one @{term "e1_stm0"} event.
So we cannot rename a process with a non-injective mapping now.
\<close>
(*
definition rename_stm0_events where
"rename_stm0_events = 
  [(e1__stm0_C (tid, dir, n), e1_stm0_C (dir, n)) . 
          tid \<leftarrow> TIDS_stm0_list, 
          dir \<leftarrow> InOut_list, 
          n \<leftarrow> rc.core_int_list] @
  [(e3__stm0_C (tid, dir, n), e3_stm0_C (dir, n)) . 
          tid \<leftarrow> TIDS_stm0_list, 
          dir \<leftarrow> InOut_list, 
          n \<leftarrow> rc.core_int_list]
"*)

definition rename_stm0_events where
"rename_stm0_events = 
  concat ((enumchan2 (forget_first2 e1__stm0_C e1_stm0_C TIDS_stm0_list) InOut_list rc.core_int_list) @
          (enumchan2 (forget_first2 e3__stm0_C e3_stm0_C TIDS_stm0_list) InOut_list rc.core_int_list))
"

definition rename_stm0_events_others where
"rename_stm0_events_others = 
  (enumchanp1 terminate_stm0_C [()]) @
  (enumchansp1 [get_x_stm0_C, set_x_stm0_C, set_EXT_x_stm0_C] rc.core_int_list) @
  (enumchansp2 [e1_stm0_C, e3_stm0_C] InOut_list rc.core_int_list) @
  (enumchansp2 [enter_stm0_C, entered_stm0_C, exit_stm0_C, exited_stm0_C] SIDS_stm0_list SIDS_stm0_list)
"
(*
definition rename_stm0_events_others' where
"rename_stm0_events_others' = 
  [(terminate_stm0_C(), terminate_stm0_C () ) ] @
  [(get_x_stm0_C (n), get_x_stm0_C (n)) . 
          n \<leftarrow> rc.core_int_list] @
  [(set_x_stm0_C (n), set_x_stm0_C (n)) . 
          n \<leftarrow> rc.core_int_list] @
  [(set_EXT_x_stm0_C (n), set_EXT_x_stm0_C (n)) .
          n \<leftarrow> rc.core_int_list] @
  [(e1_stm0_C (dir, n), e1_stm0_C (dir, n)) . 
          dir \<leftarrow> InOut_list, 
          n \<leftarrow> rc.core_int_list] @
  [(e3_stm0_C (dir, n), e3_stm0_C (dir, n)) . 
          dir \<leftarrow> InOut_list, 
          n \<leftarrow> rc.core_int_list] @
  [(enter_stm0_C (sid1, sid2), enter_stm0_C (sid1, sid2)) . 
          sid1 \<leftarrow> SIDS_stm0_list, 
          sid2 \<leftarrow> SIDS_stm0_list] @
  [(entered_stm0_C (sid1, sid2), entered_stm0_C (sid1, sid2)) . 
          sid1 \<leftarrow> SIDS_stm0_list, 
          sid2 \<leftarrow> SIDS_stm0_list] @
  [(exit_stm0_C (sid1, sid2), exit_stm0_C (sid1, sid2)) . 
          sid1 \<leftarrow> SIDS_stm0_list, 
          sid2 \<leftarrow> SIDS_stm0_list] @
  [(exited_stm0_C (sid1, sid2), exited_stm0_C (sid1, sid2)) . 
          sid1 \<leftarrow> SIDS_stm0_list, 
          sid2 \<leftarrow> SIDS_stm0_list] 
"*)

definition rename_MemorySTM_opt_stm0 where
"rename_MemorySTM_opt_stm0 idd =
    ((MemorySTM_opt_stm0 idd) \<lbrakk>(set (rename_stm0_events @ rename_stm0_events_others))\<rbrakk>)
"

definition AUX_opt_stm0 where
"AUX_opt_stm0 (idd::integer) = 
  ( 
    ( 
      (rename_MemorySTM_opt_stm0 idd) \<lbrakk> set [terminate_stm0_C ()] \<Zrres> skip
    ) \<setminus> stm0_MachineInternalEvents
  )
"

definition D__stm0 where
"D__stm0 (idd::integer) = 
  (AUX_opt_stm0 idd) \<setminus> internal_events_stm0
"

subsection \<open> stm1 \<close>

datatype SIDS_stm1 = SID_stm1 | SID_stm1_s0

definition "SIDS_stm1_list = [SID_stm1, SID_stm1_s0]"
definition "SIDS_stm1_set = set SIDS_stm1_list"
definition "SIDS_stm1_without_s0 = (removeAll SID_stm1_s0 SIDS_stm1_list)"

datatype TIDS_stm1 = NULLTRANSITION_stm1
	              | TID_stm1_t0
	              | TID_stm1_t1
	              | TID_stm1_t2

definition "TIDS_stm1_list = [NULLTRANSITION_stm1, TID_stm1_t0, TID_stm1_t1, TID_stm1_t2]"
definition "TIDS_stm1_set = set TIDS_stm1_list"

definition "ITIDS_stm1_list = [TID_stm1_t1, TID_stm1_t2]"
definition "ITIDS_stm1 = set ITIDS_stm1_list"

chantype Chan_stm1 =
(* flow channels *)
  internal_stm1 :: TIDS_stm1
(*
  enteredV_stm1 :: SIDS_stm1
  enterV_stm1 :: SIDS_stm1 
  exitV_stm1  :: SIDS_stm1 
  exitedV_stm1 :: SIDS_stm1
*)
  enter_stm1 :: "SIDS_stm1 \<times> SIDS_stm1"
  entered_stm1 :: "SIDS_stm1 \<times> SIDS_stm1"
  exit_stm1 :: "SIDS_stm1 \<times> SIDS_stm1"
  exited_stm1 :: "SIDS_stm1 \<times> SIDS_stm1"
  terminate_stm1 :: unit
(* variable channels *)
  get_l_stm1 :: core_int
  set_l_stm1 :: core_int
  get_x_stm1 :: core_int
  set_x_stm1 :: core_int
(* shared variable channels *)
  set_EXT_x_stm1 :: core_int
(* event channels *)
  e2__stm1 :: "TIDS_stm1 \<times> InOut"
  e2_stm1 :: "InOut"
  e3__stm1 :: "TIDS_stm1 \<times> InOut \<times> core_int"
  e3_stm1 :: "InOut \<times> core_int"

subsubsection \<open> Sets of events \<close>
definition int_int_stm1 where
"int_int_stm1 = 
  set ((enumchan2 e2__stm1_C [TID_stm1_t1,TID_stm1_t2] [din, dout]) @
       (enumchan3 e3__stm1_C [TID_stm1_t1,TID_stm1_t2] [din, dout] rc.core_int_list) @
       (enumchan1 internal_stm1_C [TID_stm1_t1,TID_stm1_t2])
)"

definition internal_events_stm1 where
"internal_events_stm1 = 
  set (enumchans2 [enter_stm1_C, entered_stm1_C, exit_stm1_C, exited_stm1_C] SIDS_stm1_list SIDS_stm1_list)
"

(*
definition shared_variable_events_stm1 where
"shared_variable_events_stm1 = 
  set ([set_EXT_x_stm1_C (x). 
          x \<leftarrow> rc.core_int_list]
)"
*)

definition stm1_s0_triggers where
"stm1_s0_triggers = 
  set ((enumchan2 e2__stm1_C [TID_stm1_t2] [din, dout]) @
       (enumchan3 e3__stm1_C [TID_stm1_t1] [din, dout] rc.core_int_list)
)
"

definition stm1_x_events where
"stm1_x_events = 
  set (enumchans1 [get_x_stm1_C, set_x_stm1_C] rc.core_int_list)
"

definition stm1_MachineInternalEvents where
"stm1_MachineInternalEvents = 
  set (enumchan1 internal_stm1_C TIDS_stm1_list)"

subsubsection \<open> State Machine Memory \<close>
text \<open> Memory cell processes \<close>
(* for the shared variable x *)

definition stm1_Memory_opt_x where
"stm1_Memory_opt_x = 
  mem_of_svar get_x_stm1 set_x_stm1 set_EXT_x_stm1 rc.core_int_set"

text \<open> Memory transition processes \<close>
definition stm1_MemoryTransitions_opt_0 where
"stm1_MemoryTransitions_opt_0 = 
  loop (\<lambda> id::integer. 
    (do {outp internal_stm1 TID_stm1_t0 ; Ret (id)} \<box> 
     do {outp e2__stm1 (TID_stm1_t2, din) ; Ret (id)} \<box> 
     do {inp_in e3__stm1 (set [(TID_stm1_t1, din, x). x \<leftarrow> rc.core_int_list]) ; Ret (id)}
    )
  )
"

subsubsection \<open> States \<close>
definition I_stm1_i0 where
"I_stm1_i0 = (\<lambda> (id::integer) . 
  do {outp internal_stm1 TID_stm1_t0 ; 
      outp enter_stm1 (SID_stm1, SID_stm1_s0);
      outp entered_stm1 (SID_stm1, SID_stm1_s0)
  })
"


definition tids_stm1_s0 where
" tids_stm1_s0 = 
    (filter 
        (\<lambda> s. s \<notin> {NULLTRANSITION_stm1,TID_stm1_t1,TID_stm1_t2}) 
        ITIDS_stm1_list)"

(* We need an interrupt operator for during actions *) 
(* ::"integer \<Rightarrow> SIDS_stm0 \<Rightarrow> (Chan_stm0, SIDS_stm0) itree" *)
definition State_stm1_s0 where 
"State_stm1_s0 = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_stm1 (set 
          [(s, SID_stm1_s0) . s \<leftarrow> (removeAll SID_stm1_s0 SIDS_stm1_list)]) ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> @{text State_stm1_s0_execute} \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_stm1 (snd (snd s), SID_stm1_s0);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> @{text T_stm1_t1} \<close>
                do {t \<leftarrow> inp_in e3__stm1 (set [(TID_stm1_t1, din, l) . l \<leftarrow> rc.core_int_list]) ;
                      outp set_x_stm1 (snd (snd t)) ; 
                      outp exit_stm1 (SID_stm1_s0, SID_stm1_s0);
                      outp exited_stm1 (SID_stm1_s0, SID_stm1_s0);
                      x \<leftarrow> inp_in get_x_stm1 rc.core_int_set ; 
                        \<comment> \<open> @{text \<open>outp set_x_stm1 (x+1);\<close>} \<close>
                        outp set_x_stm1 (rc.Plus x 1 rc.core_int_set);
                        outp enter_stm1 (SID_stm1_s0, SID_stm1_s0);
                        Ret(True, fst (snd s), SID_stm1_s0)
                    } \<box>
                \<comment> \<open> @{text T_stm1_t2} \<close>
                do {outp e2__stm1 (TID_stm1_t2, din);
                    outp exit_stm1 (SID_stm1_s0, SID_stm1_s0);
                    outp exited_stm1 (SID_stm1_s0, SID_stm1_s0);
                    outp set_x_stm1 0;
                    outp enter_stm1 (SID_stm1_s0, SID_stm1_s0);
                    Ret(True, fst (snd s), SID_stm1_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in internal_stm1(set tids_stm1_s0);
                    y \<leftarrow> inp_in exit_stm1 (set 
                      [(s, SID_stm1_s0) . s \<leftarrow> (removeAll SID_stm1_s0 SIDS_stm1_list)]);
                      outp exit_stm1 (fst y, SID_stm1_s0);
                      Ret (False, fst (snd s), SID_stm1_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in e2__stm1 (set [(s, d) . 
                        s \<leftarrow> tids_stm1_s0, 
                        d \<leftarrow> InOut_list]) ;
                    y \<leftarrow> inp_in exit_stm1 (set 
                        [(s, SID_stm1_s0) . s \<leftarrow> (removeAll SID_stm1_s0 SIDS_stm1_list)]);
                      outp exit_stm1 (fst y, SID_stm1_s0);
                      Ret (False, fst (snd s), SID_stm1_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in e3__stm1 (set [(s, d, l) . 
                        s \<leftarrow> tids_stm1_s0, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> rc.core_int_list]) ;
                    y \<leftarrow> inp_in exit_stm1 (set 
                        [(s, SID_stm1_s0) . s \<leftarrow> (removeAll SID_stm1_s0 SIDS_stm1_list)]);
                      outp exit_stm1 (fst y, SID_stm1_s0);
                      Ret (False, fst (snd s), SID_stm1_s0)
                    }
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


definition State_stm1_s0_R where
"State_stm1_s0_R (idd::integer) = 
   (discard_state (State_stm1_s0 idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_stm1 - stm1_s0_triggers) \<^esub> 
   skip
"

definition flow_event_stm1_not_s0 where 
"flow_event_stm1_not_s0 = set (
  enumchans2 [enter_stm1_C, entered_stm1_C,exit_stm1_C,exited_stm1_C] 
             SIDS_stm1_without_s0 [SID_stm1_s0]
)"

definition STM_stm1 where
"STM_stm1 (idd::integer) = 
   (I_stm1_i0(idd))
    \<parallel>\<^bsub> flow_event_stm1_not_s0 \<^esub> 
   State_stm1_s0_R(idd)
"

definition stm1_e1_x_internal_set where
"stm1_e1_x_internal_set = 
   set ((enumchan3 e3__stm1_C [TID_stm1_t1] [din, dout] rc.core_int_list) @ 
       [internal_stm1_C TID_stm1_t0] @
       (enumchan2 e2__stm1_C [TID_stm1_t2] [din, dout])
)"

subsubsection \<open> State machine \<close>
definition MemorySTM_opt_stm1 where
"MemorySTM_opt_stm1 (idd::integer) = 
  (
    (
      (
        (
          (discard_state (stm1_Memory_opt_x 0))
          \<parallel>\<^bsub> stm1_x_events \<^esub>
          (STM_stm1 idd)
        ) \<setminus> (set [get_x_stm1_C n. n \<leftarrow> rc.core_int_list])
      )
      \<parallel>\<^bsub> stm1_e1_x_internal_set \<^esub>
      (discard_state (stm1_MemoryTransitions_opt_0 idd))
    ) \<setminus> {internal_stm1_C TID_stm1_t0}
  )
"
(*
definition rename_stm1_events where
"rename_stm1_events = 
  [(e2__stm1_C (tid, dir), e2_stm1_C (dir)) . 
          tid \<leftarrow> TIDS_stm1_list, 
          dir \<leftarrow> InOut_list] @
  [(e3__stm1_C (tid, dir, n), e3_stm1_C (dir, n)) . 
          tid \<leftarrow> TIDS_stm1_list, 
          dir \<leftarrow> InOut_list, 
          n \<leftarrow> rc.core_int_list]
"

definition rename_stm1_events_others where
"rename_stm1_events_others = 
  [(terminate_stm1_C(), terminate_stm1_C () ) ] @
  [(get_x_stm1_C (n), get_x_stm1_C (n)) . 
          n \<leftarrow> rc.core_int_list] @
  [(set_x_stm1_C (n), set_x_stm1_C (n)) . 
          n \<leftarrow> rc.core_int_list] @
  [(set_EXT_x_stm1_C (n), set_EXT_x_stm1_C (n)) .
          n \<leftarrow> rc.core_int_list] @
  [(e2_stm1_C (dir), e2_stm1_C (dir)) . 
          dir \<leftarrow> InOut_list] @
  [(e3_stm1_C (dir, n), e3_stm1_C (dir, n)) . 
          dir \<leftarrow> InOut_list, 
          n \<leftarrow> rc.core_int_list] @
  [(enter_stm1_C (sid1, sid2), enter_stm1_C (sid1, sid2)) . 
          sid1 \<leftarrow> SIDS_stm1_list, 
          sid2 \<leftarrow> SIDS_stm1_list] @
  [(entered_stm1_C (sid1, sid2), entered_stm1_C (sid1, sid2)) . 
          sid1 \<leftarrow> SIDS_stm1_list, 
          sid2 \<leftarrow> SIDS_stm1_list] @
  [(exit_stm1_C (sid1, sid2), exit_stm1_C (sid1, sid2)) . 
          sid1 \<leftarrow> SIDS_stm1_list, 
          sid2 \<leftarrow> SIDS_stm1_list] @
  [(exited_stm1_C (sid1, sid2), exited_stm1_C (sid1, sid2)) . 
          sid1 \<leftarrow> SIDS_stm1_list, 
          sid2 \<leftarrow> SIDS_stm1_list] 
"
*)
definition rename_stm1_events where
"rename_stm1_events = 
  concat ((enumchan1 (forget_first e2__stm1_C e2_stm1_C TIDS_stm1_list) InOut_list) @
  (enumchan2 (forget_first2 e3__stm1_C e3_stm1_C TIDS_stm1_list) InOut_list rc.core_int_list))
"

definition rename_stm1_events_others where
"rename_stm1_events_others = 
  (enumchanp1 terminate_stm1_C [()]) @
  (enumchansp1 [get_x_stm1_C, set_x_stm1_C, set_EXT_x_stm1_C] rc.core_int_list) @
  (enumchansp1 [e2_stm1_C] InOut_list) @
  (enumchansp2 [e3_stm1_C] InOut_list rc.core_int_list) @
  (enumchansp2 [enter_stm1_C, entered_stm1_C, exit_stm1_C, exited_stm1_C] SIDS_stm1_list SIDS_stm1_list)
"

definition rename_MemorySTM_opt_stm1 where
"rename_MemorySTM_opt_stm1 idd = 
  ((MemorySTM_opt_stm1 idd) \<lbrakk>(set (rename_stm1_events @ rename_stm1_events_others))\<rbrakk>)
"

(* Exception: P [| A |> Q*)
(* Renaming *)
definition AUX_opt_stm1 where
"AUX_opt_stm1 (idd::integer) = 
  ( 
    ( 
      (rename_MemorySTM_opt_stm1 idd) \<lbrakk> set [terminate_stm1_C ()] \<Zrres> skip
    ) \<setminus> stm1_MachineInternalEvents
  )
"

definition D__stm1 where
"D__stm1 (idd::integer) = 
  (AUX_opt_stm1 idd) \<setminus> internal_events_stm1
"

subsection \<open> Controller \<close>
chantype Chan_ctr0 =
(* terminates of stm0 and stm1 are mapped to it *)
  terminate_ctr0 :: unit 
(* variable channels: set_x and get_x of stm0 and stm1 are mapped to these channels *)
  set_x_ctr0 :: core_int
  get_x_ctr0 :: core_int
(* shared variable channels *)
  set_EXT_x_ctr0 :: core_int
(* set_EXT_x of stm0 is mapped to this *)
  set_EXT_x_ctr0_stm0 :: core_int
(* set_EXT_x of stm1 is mapped to this *)
  set_EXT_x_ctr0_stm1 :: core_int
(* e1 of stm0 is mapped to it *)
  e1_ctr0 :: "InOut \<times> core_int"
(* e2 of stm1 is mapped to it *)
  e2_ctr0 :: "InOut"
(* e3 of stm0 is mapped to e3_ctr0.out and e3 of stm1 is mapped to e3_ctr0.in *)
  e3_ctr0 :: "InOut \<times> core_int"

definition shared_variable_events_ctr0 where
"shared_variable_events_ctr0 = 
  set (enumchan1 set_EXT_x_ctr0_C rc.core_int_list)"

subsubsection \<open> Memory \<close>
definition Memory_ctr0 where
"Memory_ctr0 = loop (\<lambda> id::integer.
  ( do {x \<leftarrow> inp_in set_EXT_x_ctr0 rc.core_int_set; 
        outp set_EXT_x_ctr0_stm0 x; 
        outp set_EXT_x_ctr0_stm1 x; Ret (id)}
  )
)"

subsubsection \<open> Controller \<close>
(*
definition rename_ctr0_stm0_events where
"rename_ctr0_stm0_events = 
  [(terminate_stm0_C (), terminate_ctr0_C ())] @
  [(set_x_stm0_C n, set_x_ctr0_C n). n \<leftarrow> rc.core_int_list] @
  [(get_x_stm0_C n, get_x_ctr0_C n). n \<leftarrow> rc.core_int_list] @
  [(e1_stm0_C (d, n), e1_ctr0_C (d, n)). d \<leftarrow> InOut_list, n \<leftarrow> rc.core_int_list] @
  [(e3_stm0_C (d, n), e3_ctr0_C (d, n)). d \<leftarrow> InOut_list, n \<leftarrow> rc.core_int_list] @
  [(set_EXT_x_stm0_C x, set_EXT_x_ctr0_stm0_C x) . x \<leftarrow> rc.core_int_list]
" *)
definition rename_ctr0_stm0_events where
"rename_ctr0_stm0_events = 
  (enumchanp2_1 (terminate_stm0_C,terminate_ctr0_C) [()]) @
  (enumchansp2_1 [(set_x_stm0_C, set_x_ctr0_C), (get_x_stm0_C, get_x_ctr0_C), 
      (set_EXT_x_stm0_C, set_EXT_x_ctr0_stm0_C)] rc.core_int_list) @
  (enumchansp2_2 [(e1_stm0_C, e1_ctr0_C), (e3_stm0_C, e3_ctr0_C)] InOut_list rc.core_int_list)"

definition rename_D__stm0 where
"rename_D__stm0 idd = ((D__stm0 idd) \<lbrakk>(set rename_ctr0_stm0_events)\<rbrakk>)"
(*
definition rename_ctr0_stm1_events where
"rename_ctr0_stm1_events = 
  [(terminate_stm1_C (), terminate_ctr0_C ())] @
  [(set_x_stm1_C n, set_x_ctr0_C n). n \<leftarrow> rc.core_int_list] @
  [(get_x_stm1_C n, get_x_ctr0_C n). n \<leftarrow> rc.core_int_list] @
  [(e2_stm1_C (d), e2_ctr0_C (d)). d \<leftarrow> InOut_list] @
\<comment> \<open>It is important to invert directions in one side: either stm0 or stm1 \<close>
  [(e3_stm1_C (din, n), e3_ctr0_C (dout, n)). n \<leftarrow> rc.core_int_list] @
  [(e3_stm1_C (dout, n), e3_ctr0_C (din, n)). n \<leftarrow> rc.core_int_list] @
  [(set_EXT_x_stm1_C x, set_EXT_x_ctr0_stm1_C x) . x \<leftarrow> rc.core_int_list]
"
*)
definition rename_ctr0_stm1_events where
"rename_ctr0_stm1_events = 
  (enumchanp2_1 (terminate_stm1_C,terminate_ctr0_C) [()]) @
  (enumchansp2_1 [(set_x_stm1_C, set_x_ctr0_C), (get_x_stm1_C, get_x_ctr0_C), 
      (set_EXT_x_stm1_C, set_EXT_x_ctr0_stm1_C)] rc.core_int_list) @
  (enumchansp2_1 [(e2_stm1_C, e2_ctr0_C)] InOut_list) @
\<comment> \<open>It is important to invert directions in one side: either stm0 or stm1 \<close>
  (enumchansp2_1 [((curry e3_stm1_C) din, (curry e3_ctr0_C) dout), 
      ((curry e3_stm1_C) dout, (curry e3_ctr0_C) din)] rc.core_int_list)
"

definition rename_D__stm1 where
"rename_D__stm1 idd = ((D__stm1 idd) \<lbrakk>(set rename_ctr0_stm1_events)\<rbrakk>)"

definition "ctr0_stms_events = set (
  enumchan1 terminate_ctr0_C [()] @
  enumchan2 e3_ctr0_C InOut_list rc.core_int_list
)"

definition "ctr0_mem_events = set (
  enumchans1 [set_EXT_x_ctr0_stm0_C, set_EXT_x_ctr0_stm1_C] rc.core_int_list
)"

definition D__ctr0 where
"D__ctr0 (idd::integer) = 
  (par_hide
    ( 
      ((rename_D__stm0 idd) \<parallel>\<^bsub> ctr0_stms_events \<^esub> (rename_D__stm1 idd))
      \<setminus> (ctr0_stms_events - set [terminate_ctr0_C ()])
    )
    ctr0_mem_events
    (discard_state (Memory_ctr0 idd))
  )  \<lbrakk> set [terminate_ctr0_C ()] \<Zrres> skip
"

subsection \<open> Module \<close>
chantype Chan_mod0 =
(* terminates of ctr0 are mapped to it *)
  terminate_mod0 :: unit 
(* variable channels: set_x and get_x of stm0 and stm1 are mapped to these channels *)
  set_x_mod0 :: core_int
  get_x_mod0 :: core_int
(* shared variable channels *)
  set_EXT_x_mod0_ctr0 :: core_int
(* e1 of stm0 is mapped to it *)
  e1_mod0 :: "InOut \<times> core_int"
(* e2 of stm1 is mapped to it *)
  e2_mod0 :: "InOut"

subsubsection \<open> Memory \<close>
definition Memory_mod0 where
"Memory_mod0 = loop (\<lambda> id::integer.
  ( do {x \<leftarrow> inp_in set_x_mod0 rc.core_int_set; 
        outp set_EXT_x_mod0_ctr0 x; Ret (id)}
  )
)"

(*
definition rename_mod0_ctr0_events where
"rename_mod0_ctr0_events = 
  [(terminate_ctr0_C (), terminate_mod0_C ())] @
  [(set_x_ctr0_C n, set_x_mod0_C n). n \<leftarrow> rc.core_int_list] @
  [(get_x_ctr0_C n, get_x_mod0_C n). n \<leftarrow> rc.core_int_list] @
  [(e1_ctr0_C (d, n), e1_mod0_C (d, n)). d \<leftarrow> InOut_list, n \<leftarrow> rc.core_int_list] @
  [(e2_ctr0_C (d), e2_mod0_C (d)). d \<leftarrow> InOut_list] @
  [(set_EXT_x_ctr0_C n, set_EXT_x_mod0_ctr0_C n). n \<leftarrow> rc.core_int_list]
"
*)

subsubsection \<open> Module \<close>
definition rename_mod0_ctr0_events where
"rename_mod0_ctr0_events = 
  (enumchanp2_1 (terminate_ctr0_C,terminate_mod0_C) [()]) @
  (enumchansp2_1 [(set_x_ctr0_C, set_x_mod0_C), (get_x_ctr0_C, get_x_mod0_C), 
      (set_EXT_x_ctr0_C, set_EXT_x_mod0_ctr0_C)] rc.core_int_list) @
  (enumchanp2_1 (e2_ctr0_C, e2_mod0_C) InOut_list) @
  (enumchanp2_2 (e1_ctr0_C, e1_mod0_C) InOut_list rc.core_int_list)
"

definition rename_D__ctr0 where
"rename_D__ctr0 idd = ((D__ctr0 idd) \<lbrakk>(set rename_mod0_ctr0_events)\<rbrakk>)"

definition "mod0_set_x_events = set (
  enumchan1 set_x_mod0_C  rc.core_int_list
)"

definition "mod0_get_x_events = set (
  enumchan1 get_x_mod0_C  rc.core_int_list
)"

definition "mod0_set_EXT_x_events = set (
  enumchan1 set_EXT_x_mod0_ctr0_C  rc.core_int_list
)"

definition D__ctr_mem where
"D__ctr_mem (idd::integer) = (
              (rename_D__ctr0 idd) 
              \<parallel>\<^bsub> (mod0_set_x_events \<union> mod0_set_EXT_x_events) \<^esub> 
              (discard_state (Memory_mod0 idd))
            )"

definition D__mod0 where
"D__mod0 (idd::integer) = 
  (
    (
      (skip \<parallel>\<^bsub> {} \<^esub> 
        (
          (
            (rename_D__ctr0 idd) 
            \<parallel>\<^bsub> (mod0_set_x_events \<union> mod0_set_EXT_x_events) \<^esub> 
            (discard_state (Memory_mod0 idd))
          ) \<setminus> ((mod0_set_x_events \<union> mod0_get_x_events) \<union> mod0_set_EXT_x_events)
        )
      )  \<lbrakk> set [terminate_mod0_C ()] \<Zrres> skip
    ) \<setminus> (set [terminate_mod0_C ()])
  )
"

subsection \<open> Export code \<close>
export_code
  stm0_Memory_opt_x
  stm0_Memory_opt_l
  stm0_MemoryTransitions_opt_0
  stm0_MemoryTransitions_opt_1
  I_stm0_i0
  State_stm0_s0
  State_stm0_s0_R
  STM_stm0
  MemorySTM_opt_stm0 
  rename_MemorySTM_opt_stm0
  D__stm0 
  stm1_Memory_opt_x
  stm1_MemoryTransitions_opt_0
  I_stm1_i0
  State_stm1_s0
  State_stm1_s0_R
  STM_stm1
  MemorySTM_opt_stm1
  D__stm1
  rename_D__stm0
  rename_D__stm1
  D__ctr0
  rename_D__ctr0
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

generate_file \<open>code/RoboChart_basic/Main.hs\<close> = 
\<open>import qualified Interaction_Trees;
import qualified Partial_Fun;
import qualified Simulate;
import qualified RoboChart_basic;

main :: IO ()
main =
  do
    Simulate.simulate (RoboChart_basic.d_mod0 0);
\<close>

export_generated_files 
  \<open>code/RoboChart_basic/Simulate.hs\<close>
  \<open>code/RoboChart_basic/Main.hs\<close>

end
