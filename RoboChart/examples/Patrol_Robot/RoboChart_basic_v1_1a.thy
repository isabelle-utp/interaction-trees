(* History of changes:
v1.1a: add a shared_x event to achieve an atomic update of a shared variable. This hasn't been done yet.
v1.1: add two left and right events to indicate required actions for RP with current value of x
v1: add another one transition to MoveSTM to have a nondeterministic choice between the triggers 
  (update) of t1 and t3
*)
section \<open> Simulation of a very basic RoboChart model \<close>
text \<open> This theory aims for simulation of a trivial RoboChart model (see 
Figure~\ref{fig:robochart_basic}) based on its CSP semantics. 
\begin{figure}
  \includegraphics[scale=0.25]{images/system}
  \caption{The RoboChart model of a trivial example}
  \label{fig:robochart_basic}
\end{figure}

This model contains one robotic
platform @{text RP} and one controller @{text Ctrl}. The controller is further composed of two 
state machines: @{text CalSTM} and @{text MoveSTM}. A shared variable @{text x} is provided by @{text RP} 
and required by the controller and its two state machines. The machine @{text CalSTM} additionally has 
a local variable @{text l}. The controller communicates with the platform through two input events:
@{text e1} and @{text e2}, which are further connected to @{text CalSTM} and @{text MoveSTM}. The two 
state machines are also connected through an event: @{text update} (from @{text CalSTM} to @{text MoveSTM}).

We note this theory is not directly translated from the RoboChart model. 
Instead, it is translated from the standard CSP semantics (under @{verbatim "csp-gen/defs"}) of 
the model which is generated in RoboTool, particularly the file @{verbatim "PatrolMod.csp"}. 
In the CSP semantics, there are a variety of versions, such as default 
(@{verbatim "Dunopt__"}), optimised (@{verbatim "D__"}), optimised with compressions 
(@{verbatim "O__"}), visible (@{verbatim "VS__"}) etc. Here, we choose the optimised version 
(@{verbatim "D__"}) because the version of the optimised with compressions (@{verbatim "O__"}) is 
used for checking core assertions in RoboTool and compressions are not implemented here.

To decide which part of the CSP semantics should be translated, we use the top-down approach, 
starting from the @{verbatim "D__(id__)"} process for the module @{text PatrolMod}, then to the controller,
and finally to the state machines. By this way, we know which channels, definitions, and processes 
are used in the version, and, therefore, they should be translated in this theory. For example, 
channel @{verbatim "enter"} should be included, but channel @{verbatim "enterV"} is not. 

This theory, on the contrary, is built from the bottom up because the definition of a top process 
relies on the definitions of other processes in the top process. 
\<close>
theory RoboChart_basic_v1_1a
  imports "ITree_RoboChart.ITree_RoboChart" 
    "ITree_Simulation.ITree_Simulation"
    "ITree_RoboChart.RoboChart_Simulation"
begin

text \<open>We, therefore, structure the theory as follows. In Sect.~\ref{ssec:basic_general}, we give 
general definitions. 
Then we define processes for @{text CalSTM} in Sect.~\ref{ssec:basic_CalSTM}, for @{text MoveSTM} in 
Sect.~\ref{ssec:basic_MoveSTM}, for @{text Ctrl} in Sect.~\ref{ssec:basic_Ctrl}, and for @{text PatrolMod} 
in Sect.~\ref{ssec:basic_PatrolMod}.
\<close>

subsection \<open> General definitions \label{ssec:basic_general}\<close>
text \<open> The interpretation of the locale @{text robochart_confs} below instantiates 
@{term "min_int"}, @{term "max_int"}, @{term "max_nat"}, @{term "min_real"}, 
and @{term "max_real"}, to -1, 1, 1, -1, and 1 separately. In the CSP semantics, these values are 
set in the @{verbatim "instantiation.csp"} file.
\<close>
interpretation rc: robochart_confs "-3" "3" "1" "-1" "1".

(* We can animate this theory with [-50, 50]. 
For the input E2, the animation is very smooth, and we can see the next events available to execute 
quite fast. This is the same case for the E1(Din, 0).
But for other cases, it will take about 15 seconds to compute 2000 internal steps in simulation, and 
then we see the next "Many steps (> 2000); Continue? [Y/N]" available to choose continuation or 
termination.
*)
(* interpretation rc: robochart_confs "-50" "50" "1" "-1" "1". *)

subsection \<open> State machine @{text CalSTM} \label{ssec:basic_CalSTM}\<close>
text \<open> Each state machine shares common definitions:
\begin{itemize}
\item two data types: @{text SIDS} and @{text TIDS} for state and transition identifiers, 
\item one channel type @{text Chan}, 
\item sets of events used in synchronisation and hiding,
\item state machine memory: memory cell and memory transition processes,
\item restricted state processes,
\item state machine processes: composition of memory processes and state processes.
\end{itemize}

We note the CSP process for a state machine is encapsulated in a module such as 
@{verbatim "module CalSTM"}, and so the names like @{verbatim SIDS} can be used in the module directly.
This theory here, however, is not based on a modular approach, and so the names like @{text SIDS} 
cannot be used to denote a state identifier type for @{text CalSTM}. Otherwise, it will cause a name 
conflict with @{text SIDS} for other state machines. For this reason, we add a suffix 
(the state machine name) to these names such as @{text SIDS_CalSTM}.
\<close>

text \<open> @{term "SIDS_CalSTM"} defines state identifiers for @{text "CalSTM"}, which include 
the machine itself and the state @{text "Cal"}.
Another possibly better way to define such a type for identifiers is through a more generic typedef 
with two type variables: one to make the type distinct for a particular state machine, and another 
is a enumerable type (@{class enum}), such as a numeral type (@{typ "2"}), to denote all identifiers 
(0 and 1 for this example). Please see @{term TrID} in @{verbatim ITree_RoboChart.thy} for more 
details. At this moment, we cannot use it now because we have not instantiated @{term TrID} for 
@{class enum}, which is necessary to enumerate all elements for such a type, like 
@{term "SIDS_CalSTM_list"} below.
\<close>
datatype SIDS_CalSTM = SID_CalSTM
                   | SID_CalSTM_Cal

text \<open> @{term "SIDS_CalSTM_list"} defines a list of all possible values in @{term "SIDS_CalSTM"}.\<close>
definition "SIDS_CalSTM_list = [SID_CalSTM, SID_CalSTM_Cal]"

text \<open> @{term "SIDS_CalSTM_set"} defines a set of all possible values in @{term "SIDS_CalSTM"}.\<close>
definition "SIDS_CalSTM_set = set SIDS_CalSTM_list"

definition "SIDS_CalSTM_without_Cal = (removeAll SID_CalSTM_Cal SIDS_CalSTM_list)"

text \<open> @{term "TIDS_CalSTM"} defines transition identifiers for state machine @{text "CalSTM"}.\<close>
datatype TIDS_CalSTM = NULLTRANSITION_CalSTM
                   | TID_CalSTM_t0
                   | TID_CalSTM_t1
                   | TID_CalSTM_t2

definition "TIDS_CalSTM_list = [NULLTRANSITION_CalSTM, TID_CalSTM_t0, TID_CalSTM_t1, TID_CalSTM_t2]"
definition "TIDS_CalSTM_set = set TIDS_CalSTM_list"

text \<open> @{term "ITIDS_CalSTM_list"} gives a list of transition IDs that can interrupt a state. \<close>
definition "ITIDS_CalSTM_list = [TID_CalSTM_t1, TID_CalSTM_t2]"
definition "ITIDS_CalSTM_set = set ITIDS_CalSTM_list"  

text \<open> @{term "Chan_CalSTM"} is a channel type for the state machine, and it declares various channels 
including flow channels, variable channels, and event channels.
\<close>
chantype Chan_CalSTM =
  internal_CalSTM :: TIDS_CalSTM
  enter_CalSTM :: "SIDS_CalSTM \<times> SIDS_CalSTM"
  entered_CalSTM :: "SIDS_CalSTM \<times> SIDS_CalSTM"
  exit_CalSTM :: "SIDS_CalSTM \<times> SIDS_CalSTM"
  exited_CalSTM :: "SIDS_CalSTM \<times> SIDS_CalSTM"
  terminate_CalSTM :: unit
  get_l_CalSTM :: core_int (* variable channels : the next 3 channels will be hidden *)
  set_l_CalSTM :: core_int
  get_x_CalSTM :: core_int
  set_x_CalSTM :: core_int (* this won't be hidden, and will be renamed to set_x_Ctrl *)
  shared_x_CalSTM :: unit (* this won't be hidden, and will be renamed to set_x_Ctrl *)
  set_EXT_x_CalSTM :: core_int (* shared variable channels, and will be renamed to set_EXT_x_Ctrl_CalSTM *)
  cal__CalSTM :: "TIDS_CalSTM \<times> InOut \<times> core_int" (* event channels will be renamed to cal_CalSTM (may introduce nondeterminism) *)
  cal_CalSTM :: "InOut \<times> core_int"   (* will be further renamed to cal_Ctrl *)
  update__CalSTM :: "TIDS_CalSTM \<times> InOut \<times> core_int"   (* will be renamed to update_Ctrl.out *)
  update_CalSTM :: "InOut \<times> core_int"

text \<open> Here, we use the following conventions.
\begin{itemize}
  \item a channel type: @{term "Chan_CalSTM"},
  \item channels (declared in @{term "Chan_CalSTM"}): @{term "internal_CalSTM"}, @{term "cal_CalSTM"}, etc.
  \begin{itemize}
    \item an internal trigger channel: @{term "internal_CalSTM"};
    \item flow control channels: @{term "enter_CalSTM"}, @{term "entered_CalSTM"}, @{term "exit_CalSTM"}, 
      and @{term "exited_CalSTM"};
    \item a terminate channel: @{term "terminate_CalSTM"};
    \item local variable channels: @{term "get_l_CalSTM"}, and @{term "set_l_CalSTM"};
    \item shared variable channels: @{term "get_x_CalSTM"}, @{term "set_x_CalSTM"}, and 
      @{term "set_EXT_x_CalSTM"};
    \item Event channels: trigger event channels (@{term "cal__CalSTM"} and @{term "update__CalSTM"}), 
      and action event channels (@{term "cal_CalSTM"} and @{term "update_CalSTM"}).
  \end{itemize}
  \item a channel event: an event starting with the name of a channel and carrying a value on the 
  channel, such as @{text "internal_CalSTM TID_CalSTM_t1"};
  %\item the data type of a channel (@{term "cal_CalSTM"}): @{typeof "cal_CalSTM_C"};
  \item the type of a channel (@{term "cal_CalSTM"}): @{typeof "cal_CalSTM"}, a prism from the data type 
    of the channel to the channel type.
\end{itemize}
\<close>

subsubsection \<open> Sets of events \<close>
text \<open> @{term "int_int_CalSTM"} defines a set of internal channel events that can interrupt states.  
\<close>
definition int_int_CalSTM where
"int_int_CalSTM = 
  set ((enumchans3 [cal__CalSTM_C, update__CalSTM_C] [TID_CalSTM_t1,TID_CalSTM_t2] [din, dout] rc.core_int_list) @
       (enumchan1 internal_CalSTM_C [TID_CalSTM_t1,TID_CalSTM_t2])
)"

text \<open> @{term "internal_events_CalSTM"} defines a set of internal flow control events. \<close>
definition internal_events_CalSTM_l where
"internal_events_CalSTM_l = 
  (enumchans2 [enter_CalSTM_C, entered_CalSTM_C, exit_CalSTM_C, exited_CalSTM_C] SIDS_CalSTM_list 
  SIDS_CalSTM_list)"

definition internal_events_CalSTM where
"internal_events_CalSTM = set internal_events_CalSTM_l"

(*
definition shared_variable_events_CalSTM where
"shared_variable_events_CalSTM = 
  set ([set_EXT_x_CalSTM_C (x). 
          x \<leftarrow> rc.core_int_list]
)"
*)

definition CS_CalSTM_Cal_sync where
"CS_CalSTM_Cal_sync = 
  set (
      \<comment> \<open> enter and exit from x to y \<close>
      (enumchans2 [enter_CalSTM_C, entered_CalSTM_C, exit_CalSTM_C, exited_CalSTM_C] [SID_CalSTM_Cal] [SID_CalSTM_Cal])@
      \<comment> \<open> enter and exit from y to x \<close>
      (enumchans2 [enter_CalSTM_C, entered_CalSTM_C, exit_CalSTM_C, exited_CalSTM_C] [SID_CalSTM_Cal] [SID_CalSTM_Cal])
)"

text \<open> @{term "CalSTM_Cal_triggers"} defines a set of channel events that act as triggers of transitions
. \<close>
definition CalSTM_Cal_triggers where
"CalSTM_Cal_triggers = 
  set ((enumchan3 cal__CalSTM_C [TID_CalSTM_t1,TID_CalSTM_t2] [din, dout] rc.core_int_list) @
  (enumchan1 internal_CalSTM_C [TID_CalSTM_t2])
)
"

text \<open> @{term "CalSTM_l_events"} defines a set of variable channel events for @{text "l"}. \<close>
definition CalSTM_l_events_l where
"CalSTM_l_events_l = 
    (enumchans1 [get_l_CalSTM_C, set_l_CalSTM_C] rc.core_int_list)
"

definition CalSTM_l_events where
"CalSTM_l_events = set CalSTM_l_events_l
"

text \<open> @{term "CalSTM_x_events"} defines a set of variable channel events for @{text "x"}. \<close>
definition CalSTM_x_events where
"CalSTM_x_events = 
    set (
        (enumchans1 [get_x_CalSTM_C, set_x_CalSTM_C] rc.core_int_list) @
        (enumchan1 set_EXT_x_CalSTM_C rc.core_int_list)
    )
"

text \<open> @{term "CalSTM_MachineInternalEvents"} defines a set of @{text "internal_"} channel events. \<close>
definition CalSTM_MachineInternalEvents_l where
"CalSTM_MachineInternalEvents_l = 
  (enumchan1 internal_CalSTM_C TIDS_CalSTM_list)
"
definition CalSTM_MachineInternalEvents where
"CalSTM_MachineInternalEvents = 
  set CalSTM_MachineInternalEvents_l
"

subsubsection \<open> State Machine Memory \<close>
paragraph \<open> Memory cell processes \<close>

text \<open> The @{term "CalSTM_Memory_opt_x"} defines a memory cell process for a shared variable @{term x}.\<close>
(*
definition CalSTM_Memory_opt_x where
"CalSTM_Memory_opt_x = 
  mem_of_svar get_x_CalSTM set_x_CalSTM set_EXT_x_CalSTM rc.core_int_set"
*)

definition CalSTM_Memory_opt_x where
"CalSTM_Memory_opt_x = loop (\<lambda> s.
  (do {outp get_x_CalSTM s; Ret (s)} \<box> 
   do {x \<leftarrow> inp_in set_x_CalSTM rc.core_int_set; 
       x \<leftarrow> inp_in set_EXT_x_CalSTM rc.core_int_set; 
            outp shared_x_CalSTM (); Ret (x)} \<box>
   do {x \<leftarrow> inp_in set_EXT_x_CalSTM rc.core_int_set; Ret (x)})
)"                            

text \<open> The type of @{term "CalSTM_Memory_opt_x"} is @{typeof "CalSTM_Memory_opt_x"}, a function from 
the type of the variable @{term x} to an @{term itree} whose channel type is @{term Chan_CalSTM} and 
return type is the same as the type of the variable.\<close>

text \<open> The @{term "CalSTM_Memory_opt_l"} is a memory cell process for a local variable @{term l}.\<close>
definition CalSTM_Memory_opt_l where
"CalSTM_Memory_opt_l = mem_of_lvar get_l_CalSTM set_l_CalSTM rc.core_int_set"

paragraph \<open> Memory transition processes \<close>
text \<open> Both @{term "CalSTM_MemoryTransitions_opt_0"} and @{term "CalSTM_MemoryTransitions_opt_1"} are memory 
processes for transitions, particularly the guards of transitions evaluated in the processes. They also 
have a parameter @{text "id"}.
\<close>
text \<open> For @{term "CalSTM_MemoryTransitions_opt_0"}, we manually add an external choice with 
@{term deadlock} to tackle an issue that the instance of @{verbatim \<open>(Eq Chan_CalSTM)\<close>} won't be 
generated if there is no equality checking. However, this instance is necessary for our animation. 
We, therefore, deliberately enable an equality checking by adding an external choice with 
@{term deadlock} (and this will not change the semantics). For this theory, actually this addition is
not necessary because there are equality checking in other processes. But, in case of an error like 
(@{verbatim "No instance for (Eq Chan) arising from a use of simulate"}), this is a feasible 
solution.
\<close>
definition CalSTM_MemoryTransitions_opt_0 where
"CalSTM_MemoryTransitions_opt_0 = 
  loop (\<lambda> id::integer. 
    (do {outp internal_CalSTM TID_CalSTM_t0 ; Ret (id)} \<box> deadlock)
  )
"

definition CalSTM_MemoryTransitions_opt_1 where
"CalSTM_MemoryTransitions_opt_1 = 
  loop (\<lambda> id::integer.
    do {x \<leftarrow> inp_in get_x_CalSTM rc.core_int_set ; 
      (
        \<comment> \<open>This constrained input prefixing corresponds to the input trigger with guard 
        (@{verbatim \<open>e1?l[x==0]\<close>}) of @{text t1}. \<close>
        do {inp_in cal__CalSTM (set [(TID_CalSTM_t1, din, l). l \<leftarrow> rc.core_int_list, (x = 0)])
              ; Ret (id)} \<box>
        \<comment> \<open>This corresponds to the guard (@{verbatim \<open>[x!=0]\<close>}) of @{text t2}.\<close>
        do {guard (x \<noteq> 0); outp internal_CalSTM TID_CalSTM_t2 ; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_x_CalSTM rc.core_int_set; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_EXT_x_CalSTM rc.core_int_set; Ret (id)}
      )
    }
  )
"

subsubsection \<open> States \<close>
text \<open> This section defines processes for junctions and states in the state machine. \<close>

text \<open> @{term "I_CalSTM_i0"} is for the initial junction @{verbatim i0} and the only transition from it
is @{verbatim t0} (to the state @{verbatim Cal}). This transition has no trigger (and so an internal 
trigger channel @{term internal_CalSTM} is used to model it), no guard (and so 
@{term CalSTM_MemoryTransitions_opt_0} has no guard), has an action @{verbatim "x=0"} (update through 
a channel @{term set_x_CalSTM} with value @{term 0}. After it, @{text CalSTM} enters @{text Cal}. 
We note @{term "I_CalSTM_i0"} is not a loop because it only executes once and then terminates.
\<close>

definition I_CalSTM_i0 where
"I_CalSTM_i0 = (\<lambda> (id::integer) . 
  do {outp internal_CalSTM TID_CalSTM_t0 ; 
      outp set_x_CalSTM 0; 
      outp enter_CalSTM (SID_CalSTM, SID_CalSTM_Cal);
      outp entered_CalSTM (SID_CalSTM, SID_CalSTM_Cal)
  })
"

definition tids_CalSTM_Cal where
" tids_CalSTM_Cal = 
    (filter 
        (\<lambda> s. s \<notin> {NULLTRANSITION_CalSTM,TID_CalSTM_t1,TID_CalSTM_t2})
        ITIDS_CalSTM_list)"

text \<open> The definition of the CSP process @{verbatim State_CalSTM_Cal} has a mutual recursion. 
The process calls @{verbatim State_CalSTM_Cal_execute} with an extra parameter for the source state of 
a transition entering this state @{text Cal}, in addition to a normal @{verbatim id} parameter.
The process @{verbatim State_CalSTM_Cal_execute} also calls @{verbatim State_CalSTM_Cal}. Here, in the 
definition @{term State_CalSTM_Cal} below, we use a 
loop (a special iteration whose boolean condition is always true) to model @{verbatim State_CalSTM_Cal}
 and an embedded iteration to model @{verbatim State_CalSTM_Cal_execute}. 
\<close>
definition State_CalSTM_Cal where 
"State_CalSTM_Cal = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_CalSTM (set 
          [(s, SID_CalSTM_Cal) . s \<leftarrow> (removeAll SID_CalSTM_Cal SIDS_CalSTM_list)]) ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> @{text State_CalSTM_Cal_execute} \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_CalSTM (snd (snd s), SID_CalSTM_Cal);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> @{text T_CalSTM_t1} \<close>
                do {t \<leftarrow> inp_in cal__CalSTM (set [(TID_CalSTM_t1, din, l) . l \<leftarrow> rc.core_int_list]) ;
                      outp set_l_CalSTM (snd (snd t)) ; 
                      outp exit_CalSTM (SID_CalSTM_Cal, SID_CalSTM_Cal);
                      outp exited_CalSTM (SID_CalSTM_Cal, SID_CalSTM_Cal);
                      l \<leftarrow> inp_in get_l_CalSTM rc.core_int_set ; 
                        outp set_x_CalSTM (l);
                        outp enter_CalSTM (SID_CalSTM_Cal, SID_CalSTM_Cal);
                        Ret(True, fst (snd s), SID_CalSTM_Cal)
                    } \<box>
                \<comment> \<open> @{text T_CalSTM_t2} \<close>
                do {outp internal_CalSTM TID_CalSTM_t2;
                    outp exit_CalSTM (SID_CalSTM_Cal, SID_CalSTM_Cal);
                    outp exited_CalSTM (SID_CalSTM_Cal, SID_CalSTM_Cal);
                      x \<leftarrow> inp_in get_x_CalSTM rc.core_int_set ; 
                        outp update_CalSTM (dout, x);
                        outp enter_CalSTM (SID_CalSTM_Cal, SID_CalSTM_Cal);
                        Ret(True, fst (snd s), SID_CalSTM_Cal)
                    } \<box>
                \<comment> \<open> @{text internal_CalSTM} \<close>
                do {
                    x \<leftarrow> inp_in internal_CalSTM 
                      (set tids_CalSTM_Cal);
                    y \<leftarrow> inp_in exit_CalSTM (set 
                      [(s, SID_CalSTM_Cal) . s \<leftarrow> (removeAll SID_CalSTM_Cal SIDS_CalSTM_list)]);
                      outp exited_CalSTM (fst y, SID_CalSTM_Cal);
                      Ret (False, fst (snd s), SID_CalSTM_Cal)
                    } \<box>
                \<comment> \<open> @{text cal__CalSTM} \<close>
                do {
                    x \<leftarrow> inp_in cal__CalSTM (set [(s, d, l) . 
                        s \<leftarrow> tids_CalSTM_Cal, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> rc.core_int_list]) ;
                    y \<leftarrow> inp_in exit_CalSTM (set 
                        [(s, SID_CalSTM_Cal) . s \<leftarrow> (removeAll SID_CalSTM_Cal SIDS_CalSTM_list)]);
                      outp exited_CalSTM (fst y, SID_CalSTM_Cal);
                      Ret (False, fst (snd s), SID_CalSTM_Cal)
                    } \<box>
                \<comment> \<open> @{text update__CalSTM} \<close>
                do {
                    x \<leftarrow> inp_in update__CalSTM (set [(s, d, l) . 
                        s \<leftarrow> tids_CalSTM_Cal, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> rc.core_int_list]) ;
                    y \<leftarrow> inp_in exit_CalSTM (set 
                        [(s, SID_CalSTM_Cal) . s \<leftarrow> (removeAll SID_CalSTM_Cal SIDS_CalSTM_list)]);
                      outp exited_CalSTM (fst y, SID_CalSTM_Cal);
                      Ret (False, fst (snd s), SID_CalSTM_Cal)
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

text \<open>In the definition above, we assemble the return value of the embedded iteration as a triple 
@{text ret}, whose first element is a boolean value denoting the condition of this iteration, whose 
second element is @{text id} from the parameter of @{term State_CalSTM_Cal}, and whose third element is 
the source state of a transition entering @{text Cal}. So in the body of the loop, we return a triple 
and pass it to the embedded iteration. Inside the iteration, if a process (such as the one for 
@{text T_CalSTM_t1}) continues the iteration (the definition of @{verbatim T_CalSTM_t1} calls 
@{verbatim State_CalSTM_Cal_execute}), it just returns with a triple whose first element is 
true. Otherwise, the first element is false (see the process for the trigger event @{text cal__CalSTM}).
This corresponds to the termination of the iteration. In the body of the loop, then only @{text id} 
is returned to the loop. 
\<close>

text \<open>In the definition of @{term State_CalSTM_Cal_R} below, its parameter is named @{text idd}, 
instead of @{text id}, due to the fact that @{term "id"} is a predefined identity function in 
Isabelle/HOL. 
We also note that @{term State_CalSTM_Cal} is not directly in parallel with @{term skip}. 
Instead, its return value is discarded by @{term discard_state} (simply by being sequentially 
composed with @{term skip}, and so the type of the return value matches with the type @{type unit} 
of the return value in @{term skip}. This is necessary for the parallel composition.
\<close>
definition State_CalSTM_Cal_R where
"State_CalSTM_Cal_R (idd::integer) = 
   (discard_state (State_CalSTM_Cal idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_CalSTM - CalSTM_Cal_triggers) \<^esub> 
   skip
"

text \<open> The @{term flow_event_CalSTM_not_Cal} defined below gives a set of flow events that represents 
entering (or exiting from) @{text Cal} from the all other states. 
\<close>
definition flow_event_CalSTM_not_Cal where 
"flow_event_CalSTM_not_Cal = set (
  enumchans2 [enter_CalSTM_C, entered_CalSTM_C,exit_CalSTM_C,exited_CalSTM_C] 
             SIDS_CalSTM_without_Cal [SID_CalSTM_Cal]
)"

text \<open> @{term STM_CalSTM} is the composition of the processes for the initial junction and states. \<close>
definition STM_CalSTM where
"STM_CalSTM (idd::integer) = 
   (I_CalSTM_i0(idd))
    \<parallel>\<^bsub> flow_event_CalSTM_not_Cal \<^esub> 
   State_CalSTM_Cal_R(idd)
"

subsubsection \<open> State machine \<close>
definition CalSTM_cal_x_internal_set where
"CalSTM_cal_x_internal_set = 
  set ((enumchan3 cal__CalSTM_C [TID_CalSTM_t1] [din, dout] rc.core_int_list) @ 
       [internal_CalSTM_C TID_CalSTM_t2] @
       (enumchan1 set_x_CalSTM_C rc.core_int_list)
)"

text \<open> @{text MemorySTM_opt_CalSTM} is the composition of @{term STM_CalSTM} and the memory (for 
variables and transitions) of the state machine. 
\<close>
definition MemorySTM_opt_CalSTM where
"MemorySTM_opt_CalSTM (idd::integer) = 
  (
    (
      (discard_state (CalSTM_Memory_opt_x 0))
      \<parallel>\<^bsub> CalSTM_x_events \<^esub>
      ( 
        (
          (par_hide
            (par_hide (discard_state (CalSTM_Memory_opt_l 0)) CalSTM_l_events (STM_CalSTM idd))
            {internal_CalSTM_C TID_CalSTM_t0}
            (discard_state (CalSTM_MemoryTransitions_opt_0 idd))
          )
          \<parallel>\<^bsub> CalSTM_cal_x_internal_set \<^esub> 
          (discard_state (CalSTM_MemoryTransitions_opt_1 idd))
        ) \<setminus> {internal_CalSTM_C TID_CalSTM_t2}
      )
    ) \<setminus> (set [get_x_CalSTM_C n. n \<leftarrow> rc.core_int_list])
  )   
"

definition MemorySTM_opt_CalSTM_p where
"MemorySTM_opt_CalSTM_p (idd::integer) = 
  (
    (
      (discard_state (CalSTM_Memory_opt_x 0))
      \<parallel>\<^bsub> CalSTM_x_events \<^esub>
      ( 
        (
          (par_hidep
            (par_hidep (discard_state (CalSTM_Memory_opt_l 0)) CalSTM_l_events_l (STM_CalSTM idd))
            [internal_CalSTM_C TID_CalSTM_t0]
            (discard_state (CalSTM_MemoryTransitions_opt_0 idd))
          )
          \<parallel>\<^bsub> CalSTM_cal_x_internal_set \<^esub> 
          (discard_state (CalSTM_MemoryTransitions_opt_1 idd))
        ) \<setminus>\<^sub>p [internal_CalSTM_C TID_CalSTM_t2]
      )
    ) \<setminus>\<^sub>p ([get_x_CalSTM_C n. n \<leftarrow> rc.core_int_list])
  )   
"

text \<open> This definition actually defines a non-injective mapping as shown below.
@{text
  "[
    (cal__CalSTM_C (TID_CalSTM_t0, din, 0), cal_CalSTM_C (din, 0)),
    (cal__CalSTM_C (TID_CalSTM_t1, din, 0), cal_CalSTM_C (din, 0)), 
    ...
  ]"
}
here multiple @{term "cal__CalSTM"} events are mapped to one @{term "cal_CalSTM"} event.
\<close>
definition rename_CalSTM_events where
"rename_CalSTM_events = 
  concat ((enumchan2 (forget_first2 cal__CalSTM_C cal_CalSTM_C TIDS_CalSTM_list) InOut_list rc.core_int_list) @
          (enumchan2 (forget_first2 update__CalSTM_C update_CalSTM_C TIDS_CalSTM_list) InOut_list rc.core_int_list))
"

text \<open>For the events that are not renamed in CSP, we still need to have them in the relation map (
otherwise, these events will not be present in the renamed process), and they shall be mapped to 
themselves. 
\<close>
definition rename_CalSTM_events_others where
"rename_CalSTM_events_others = 
  (enumchanp1 terminate_CalSTM_C [()]) @
  (enumchanp1 shared_x_CalSTM_C [()]) @
  (enumchansp1 [get_x_CalSTM_C, set_x_CalSTM_C, set_EXT_x_CalSTM_C] rc.core_int_list) @
  (enumchansp2 [cal_CalSTM_C, update_CalSTM_C] InOut_list rc.core_int_list) @
  (enumchansp2 [enter_CalSTM_C, entered_CalSTM_C, exit_CalSTM_C, exited_CalSTM_C] SIDS_CalSTM_list SIDS_CalSTM_list)
"

text \<open>So the renaming of @{term MemorySTM_opt_CalSTM} includes the events to be renamed 
(@{term rename_CalSTM_events}) and not to be renamed (@{term rename_CalSTM_events_others}).
\<close>
definition rename_MemorySTM_opt_CalSTM where
"rename_MemorySTM_opt_CalSTM idd =
    ((MemorySTM_opt_CalSTM idd) \<lbrace>(set (rename_CalSTM_events @ rename_CalSTM_events_others))\<rbrace>)
"

definition rename_MemorySTM_opt_CalSTM_p where
"rename_MemorySTM_opt_CalSTM_p idd =
    ((MemorySTM_opt_CalSTM_p idd) \<lbrace>(rename_CalSTM_events @ rename_CalSTM_events_others)\<rbrace>\<^sub>p)
"

text \<open>The exception operator allows @{term rename_MemorySTM_opt_CalSTM} to be terminated by the
@{term terminate_CalSTM} event. Furthermore, the @{term internal_CalSTM} channel events will be hidden.
\<close>
definition AUX_opt_CalSTM where
"AUX_opt_CalSTM (idd::integer) = 
  ( 
    ( 
      (rename_MemorySTM_opt_CalSTM idd) \<lbrakk> set [terminate_CalSTM_C ()] \<Zrres> skip
    ) \<setminus> CalSTM_MachineInternalEvents
  )
"

definition AUX_opt_CalSTM_p where
"AUX_opt_CalSTM_p (idd::integer) = 
  ( 
    ( 
      (rename_MemorySTM_opt_CalSTM_p idd) \<lbrakk> set [terminate_CalSTM_C ()] \<Zrres> skip
    ) \<setminus>\<^sub>p CalSTM_MachineInternalEvents_l
  )
"

text \<open>Additionally, the flow channel events are hidden.\<close>
definition D__CalSTM where
"D__CalSTM (idd::integer) = 
  (AUX_opt_CalSTM idd) \<setminus> internal_events_CalSTM
"

definition D__CalSTM_p where
"D__CalSTM_p (idd::integer) = 
  (AUX_opt_CalSTM_p idd) \<setminus>\<^sub>p internal_events_CalSTM_l
"

subsection \<open> State machine @{text MoveSTM} \label{ssec:basic_MoveSTM}\<close>

definition "const_PatrolMod_ctrl0_MoveSTM_MAX \<equiv> 2"

datatype SIDS_MoveSTM = SID_MoveSTM | SID_MoveSTM_Move

definition "SIDS_MoveSTM_list = [SID_MoveSTM, SID_MoveSTM_Move]"
definition "SIDS_MoveSTM_set = set SIDS_MoveSTM_list"
definition "SIDS_MoveSTM_without_Move = (removeAll SID_MoveSTM_Move SIDS_MoveSTM_list)"

datatype TIDS_MoveSTM = NULLTRANSITION_MoveSTM
	              | TID_MoveSTM_t0
	              | TID_MoveSTM_t1
	              | TID_MoveSTM_t2
	              | TID_MoveSTM_t3

instantiation TIDS_MoveSTM :: enum
begin
definition enum_TIDS_MoveSTM :: "TIDS_MoveSTM list" where
"enum_TIDS_MoveSTM = [NULLTRANSITION_MoveSTM, TID_MoveSTM_t0, TID_MoveSTM_t1, TID_MoveSTM_t2, TID_MoveSTM_t3]"

definition enum_all_TIDS_MoveSTM :: "(TIDS_MoveSTM \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_TIDS_MoveSTM P = (\<forall>b :: TIDS_MoveSTM \<in> set enum_class.enum. P b)"

definition enum_ex_TIDS_MoveSTM :: "(TIDS_MoveSTM \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_TIDS_MoveSTM P = (\<exists>b ::  TIDS_MoveSTM \<in> set enum_class.enum. P b)"

instance
proof (intro_classes)
  show "distinct (enum_class.enum :: TIDS_MoveSTM list)"
    by (simp add: enum_TIDS_MoveSTM_def)

  show univ_eq: "UNIV = set (enum_class.enum:: TIDS_MoveSTM list)"
    apply (simp add: enum_TIDS_MoveSTM_def)
    apply (auto simp add: enum_UNIV)
    by (meson TIDS_MoveSTM.exhaust)

  fix P :: "TIDS_MoveSTM \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P" 
    by (simp_all add: univ_eq enum_all_TIDS_MoveSTM_def enum_ex_TIDS_MoveSTM_def)
qed
end

definition "TIDS_MoveSTM_list = [NULLTRANSITION_MoveSTM, TID_MoveSTM_t0, TID_MoveSTM_t1, TID_MoveSTM_t2, TID_MoveSTM_t3]"
definition "TIDS_MoveSTM_set = set TIDS_MoveSTM_list"

definition "ITIDS_MoveSTM_list = [TID_MoveSTM_t1, TID_MoveSTM_t2, TID_MoveSTM_t3]"
definition "ITIDS_MoveSTM = set ITIDS_MoveSTM_list"

chantype Chan_MoveSTM =
(* flow channels *)
  internal_MoveSTM :: TIDS_MoveSTM
(*
  enteredV_MoveSTM :: SIDS_MoveSTM
  enterV_MoveSTM :: SIDS_MoveSTM 
  exitV_MoveSTM  :: SIDS_MoveSTM 
  exitedV_MoveSTM :: SIDS_MoveSTM
*)
  enter_MoveSTM :: "SIDS_MoveSTM \<times> SIDS_MoveSTM"
  entered_MoveSTM :: "SIDS_MoveSTM \<times> SIDS_MoveSTM"
  exit_MoveSTM :: "SIDS_MoveSTM \<times> SIDS_MoveSTM"
  exited_MoveSTM :: "SIDS_MoveSTM \<times> SIDS_MoveSTM"
  terminate_MoveSTM :: unit
(* variable channels *)
  get_l_MoveSTM :: core_int
  set_l_MoveSTM :: core_int
  get_x_MoveSTM :: core_int
  set_x_MoveSTM :: core_int
  shared_x_MoveSTM :: unit
(* shared variable channels *)
  set_EXT_x_MoveSTM :: core_int
(* event channels *)
  reset__MoveSTM :: "TIDS_MoveSTM \<times> InOut"
  reset_MoveSTM :: "InOut"
  update__MoveSTM :: "TIDS_MoveSTM \<times> InOut \<times> core_int"
  update_MoveSTM :: "InOut \<times> core_int"
  left__MoveSTM :: "TIDS_MoveSTM \<times> InOut \<times> core_int"
  left_MoveSTM :: "InOut \<times> core_int"
  right__MoveSTM :: "TIDS_MoveSTM \<times> InOut \<times> core_int"
  right_MoveSTM :: "InOut \<times> core_int"

subsubsection \<open> Sets of events \<close>
definition int_int_MoveSTM where
"int_int_MoveSTM = 
  set ((enumchan2 reset__MoveSTM_C [TID_MoveSTM_t1,TID_MoveSTM_t2,TID_MoveSTM_t3] [din, dout]) @
       (enumchan3 update__MoveSTM_C [TID_MoveSTM_t1,TID_MoveSTM_t2,TID_MoveSTM_t3] [din, dout] rc.core_int_list) @
       (enumchan1 internal_MoveSTM_C [TID_MoveSTM_t1,TID_MoveSTM_t2,TID_MoveSTM_t3]) @
       (enumchan3 left__MoveSTM_C [TID_MoveSTM_t1,TID_MoveSTM_t2,TID_MoveSTM_t3] [din, dout] rc.core_int_list) @
       (enumchan3 right__MoveSTM_C [TID_MoveSTM_t1,TID_MoveSTM_t2,TID_MoveSTM_t3] [din, dout] rc.core_int_list)
)"

definition internal_events_MoveSTM_l where
"internal_events_MoveSTM_l = 
  (enumchans2 [enter_MoveSTM_C, entered_MoveSTM_C, exit_MoveSTM_C, exited_MoveSTM_C] 
              SIDS_MoveSTM_list SIDS_MoveSTM_list)
"

definition internal_events_MoveSTM where
"internal_events_MoveSTM = set internal_events_MoveSTM_l"

(*
definition shared_variable_events_MoveSTM where
"shared_variable_events_MoveSTM = 
  set ([set_EXT_x_MoveSTM_C (x). 
          x \<leftarrow> rc.core_int_list]
)"
*)

definition MoveSTM_Move_triggers where
"MoveSTM_Move_triggers = 
  set ((enumchan2 reset__MoveSTM_C [TID_MoveSTM_t2] [din, dout]) @
       (enumchan3 update__MoveSTM_C [TID_MoveSTM_t1] [din, dout] rc.core_int_list)@
       (enumchan3 update__MoveSTM_C [TID_MoveSTM_t3] [din, dout] rc.core_int_list)
)
"

definition MoveSTM_l_events_l where
"MoveSTM_l_events_l = 
  (enumchans1 [get_l_MoveSTM_C, set_l_MoveSTM_C] rc.core_int_list)
"

definition MoveSTM_l_events where
"MoveSTM_l_events = set MoveSTM_l_events_l
"

definition MoveSTM_x_events where
"MoveSTM_x_events = 
  set (enumchans1 [get_x_MoveSTM_C, set_x_MoveSTM_C] rc.core_int_list)
"

definition MoveSTM_MachineInternalEvents_l where
"MoveSTM_MachineInternalEvents_l = (enumchan1 internal_MoveSTM_C TIDS_MoveSTM_list)"

definition MoveSTM_MachineInternalEvents where
"MoveSTM_MachineInternalEvents = set MoveSTM_MachineInternalEvents_l"

subsubsection \<open> State Machine Memory \<close>
text \<open> Memory cell processes \<close>
(* for the shared variable x *)
(*&
definition MoveSTM_Memory_opt_x where
"MoveSTM_Memory_opt_x = 
  mem_of_svar get_x_MoveSTM set_x_MoveSTM set_EXT_x_MoveSTM rc.core_int_set"
*)
definition MoveSTM_Memory_opt_x where
"MoveSTM_Memory_opt_x = loop (\<lambda> s.
  (do {outp get_x_MoveSTM s; Ret (s)} \<box> 
   do {x \<leftarrow> inp_in set_x_MoveSTM rc.core_int_set;
       x \<leftarrow> inp_in set_EXT_x_MoveSTM rc.core_int_set; 
            outp shared_x_MoveSTM () ; Ret (x)} \<box>
   do {x \<leftarrow> inp_in set_EXT_x_MoveSTM rc.core_int_set; Ret (x)})
)"

definition MoveSTM_Memory_opt_l where
"MoveSTM_Memory_opt_l = mem_of_lvar get_l_MoveSTM set_l_MoveSTM rc.core_int_set"

text \<open> Memory transition processes \<close>
definition MoveSTM_MemoryTransitions_opt_0 where
"MoveSTM_MemoryTransitions_opt_0 = 
  loop (\<lambda> id::integer. 
    (do {outp internal_MoveSTM TID_MoveSTM_t0 ; Ret (id)} \<box> 
     do {outp reset__MoveSTM (TID_MoveSTM_t2, din) ; Ret (id)}
    )
  )
"
(*
definition MoveSTM_MemoryTransitions_opt_1 where
"MoveSTM_MemoryTransitions_opt_1 = 
  loop (\<lambda> id::integer. 
    do {
      x \<leftarrow> inp_in get_x_MoveSTM rc.core_int_set ;
      (do {guard (x \<le> const_PatrolMod_ctrl0_MoveSTM_MAX); 
           inp_in update__MoveSTM (set [(TID_MoveSTM_t1, din, x). x \<leftarrow> rc.core_int_list]) ; 
           Ret (id)} \<box> 
       do {guard (x \<ge> rc.Neg const_PatrolMod_ctrl0_MoveSTM_MAX rc.core_int_set); 
           inp_in update__MoveSTM (set [(TID_MoveSTM_t3, din, x). x \<leftarrow> rc.core_int_list]) ; 
           Ret (id)}
      )
    }
  )
"
*)
definition MoveSTM_MemoryTransitions_opt_1 where
"MoveSTM_MemoryTransitions_opt_1 = 
  loop (\<lambda> id::integer. 
    do {
      (do {inp_in update__MoveSTM (set [(TID_MoveSTM_t1, din, l). l \<leftarrow> rc.core_int_list, l < const_PatrolMod_ctrl0_MoveSTM_MAX]) ; 
           Ret (id)} \<box> 
       do {inp_in update__MoveSTM (set [(TID_MoveSTM_t3, din, l). l \<leftarrow> rc.core_int_list, 
           (l > rc.Neg const_PatrolMod_ctrl0_MoveSTM_MAX rc.core_int_set)]) ; 
           Ret (id)}
      )
    }
  )
"


subsubsection \<open> States \<close>
definition I_MoveSTM_i0 where
"I_MoveSTM_i0 = (\<lambda> (id::integer) . 
  do {outp internal_MoveSTM TID_MoveSTM_t0 ; 
      outp enter_MoveSTM (SID_MoveSTM, SID_MoveSTM_Move);
      outp entered_MoveSTM (SID_MoveSTM, SID_MoveSTM_Move)
  })
"


definition tids_MoveSTM_Move where
" tids_MoveSTM_Move = 
    (filter 
        (\<lambda> s. s \<notin> {NULLTRANSITION_MoveSTM,TID_MoveSTM_t1,TID_MoveSTM_t2,TID_MoveSTM_t3}) 
        ITIDS_MoveSTM_list)"

(* We need an interrupt operator for during actions *) 
(* ::"integer \<Rightarrow> SIDS_CalSTM \<Rightarrow> (Chan_CalSTM, SIDS_CalSTM) itree" *)
definition State_MoveSTM_Move where 
"State_MoveSTM_Move = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_MoveSTM (set 
          [(s, SID_MoveSTM_Move) . s \<leftarrow> (removeAll SID_MoveSTM_Move SIDS_MoveSTM_list)]) ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> @{text State_MoveSTM_Move_execute} \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_MoveSTM (snd (snd s), SID_MoveSTM_Move);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> @{text T_MoveSTM_t1} \<close>
                do {t \<leftarrow> inp_in update__MoveSTM (set [(TID_MoveSTM_t1, din, l) . l \<leftarrow> rc.core_int_list]) ;
                      outp set_l_MoveSTM (snd (snd t)) ; 
                      outp exit_MoveSTM (SID_MoveSTM_Move, SID_MoveSTM_Move);
                      outp exited_MoveSTM (SID_MoveSTM_Move, SID_MoveSTM_Move);
                      x \<leftarrow> inp_in get_x_MoveSTM rc.core_int_set ; 
                      outp right_MoveSTM (dout, x);
                      l \<leftarrow> inp_in get_l_MoveSTM rc.core_int_set ; 
                        \<comment> \<open> @{text \<open>outp set_x_MoveSTM (x+1);\<close>} \<close>
                        outp set_x_MoveSTM (rc.Plus l 1 rc.core_int_set);
                        outp enter_MoveSTM (SID_MoveSTM_Move, SID_MoveSTM_Move);
                        Ret(True, fst (snd s), SID_MoveSTM_Move)
                    } \<box>
                \<comment> \<open> @{text T_MoveSTM_t2} \<close>
                do {outp reset__MoveSTM (TID_MoveSTM_t2, din);
                    outp exit_MoveSTM (SID_MoveSTM_Move, SID_MoveSTM_Move);
                    outp exited_MoveSTM (SID_MoveSTM_Move, SID_MoveSTM_Move);
                    outp set_x_MoveSTM 0;
                    outp enter_MoveSTM (SID_MoveSTM_Move, SID_MoveSTM_Move);
                    Ret(True, fst (snd s), SID_MoveSTM_Move)
                    } \<box>
                \<comment> \<open> @{text T_MoveSTM_t3} \<close>
                do {t \<leftarrow> inp_in update__MoveSTM (set [(TID_MoveSTM_t3, din, l) . l \<leftarrow> rc.core_int_list]) ;
                      outp set_l_MoveSTM (snd (snd t)) ; 
                      outp exit_MoveSTM (SID_MoveSTM_Move, SID_MoveSTM_Move);
                      outp exited_MoveSTM (SID_MoveSTM_Move, SID_MoveSTM_Move);
                      x \<leftarrow> inp_in get_x_MoveSTM rc.core_int_set ; 
                      outp left_MoveSTM (dout, x);
                      l \<leftarrow> inp_in get_l_MoveSTM rc.core_int_set ; 
                        \<comment> \<open> @{text \<open>outp set_x_MoveSTM (l-1);\<close>} \<close>
                        outp set_x_MoveSTM (rc.Minus l 1 rc.core_int_set);
                        outp enter_MoveSTM (SID_MoveSTM_Move, SID_MoveSTM_Move);
                        Ret(True, fst (snd s), SID_MoveSTM_Move)
                    } \<box>
                do {
                    x \<leftarrow> inp_in internal_MoveSTM(set tids_MoveSTM_Move);
                    y \<leftarrow> inp_in exit_MoveSTM (set 
                      [(s, SID_MoveSTM_Move) . s \<leftarrow> (removeAll SID_MoveSTM_Move SIDS_MoveSTM_list)]);
                      outp exited_MoveSTM (fst y, SID_MoveSTM_Move);
                      Ret (False, fst (snd s), SID_MoveSTM_Move)
                    } \<box>
                do {
                    x \<leftarrow> inp_in reset__MoveSTM (set [(s, d) . 
                        s \<leftarrow> tids_MoveSTM_Move, 
                        d \<leftarrow> InOut_list]) ;
                    y \<leftarrow> inp_in exit_MoveSTM (set 
                        [(s, SID_MoveSTM_Move) . s \<leftarrow> (removeAll SID_MoveSTM_Move SIDS_MoveSTM_list)]);
                      outp exited_MoveSTM (fst y, SID_MoveSTM_Move);
                      Ret (False, fst (snd s), SID_MoveSTM_Move)
                    } \<box>
                do {
                    x \<leftarrow> inp_in update__MoveSTM (set [(s, d, l) . 
                        s \<leftarrow> tids_MoveSTM_Move, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> rc.core_int_list]) ;
                    y \<leftarrow> inp_in exit_MoveSTM (set 
                        [(s, SID_MoveSTM_Move) . s \<leftarrow> (removeAll SID_MoveSTM_Move SIDS_MoveSTM_list)]);
                      outp exited_MoveSTM (fst y, SID_MoveSTM_Move);
                      Ret (False, fst (snd s), SID_MoveSTM_Move)
                    } \<box>
                do {
                    x \<leftarrow> inp_in left__MoveSTM (set [(s, d, l) . 
                        s \<leftarrow> tids_MoveSTM_Move, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> rc.core_int_list]) ;
                    y \<leftarrow> inp_in exit_MoveSTM (set 
                        [(s, SID_MoveSTM_Move) . s \<leftarrow> (removeAll SID_MoveSTM_Move SIDS_MoveSTM_list)]);
                      outp exited_MoveSTM (fst y, SID_MoveSTM_Move);
                      Ret (False, fst (snd s), SID_MoveSTM_Move)
                    } \<box>
                do {
                    x \<leftarrow> inp_in right__MoveSTM (set [(s, d, l) . 
                        s \<leftarrow> tids_MoveSTM_Move, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> rc.core_int_list]) ;
                    y \<leftarrow> inp_in exit_MoveSTM (set 
                        [(s, SID_MoveSTM_Move) . s \<leftarrow> (removeAll SID_MoveSTM_Move SIDS_MoveSTM_list)]);
                      outp exited_MoveSTM (fst y, SID_MoveSTM_Move);
                      Ret (False, fst (snd s), SID_MoveSTM_Move)
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


definition State_MoveSTM_Move_R where
"State_MoveSTM_Move_R (idd::integer) = 
   (discard_state (State_MoveSTM_Move idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_MoveSTM - MoveSTM_Move_triggers) \<^esub> 
   skip
"

definition flow_event_MoveSTM_not_Move where 
"flow_event_MoveSTM_not_Move = set (
  enumchans2 [enter_MoveSTM_C, entered_MoveSTM_C,exit_MoveSTM_C,exited_MoveSTM_C] 
             SIDS_MoveSTM_without_Move [SID_MoveSTM_Move]
)"

definition STM_MoveSTM where
"STM_MoveSTM (idd::integer) = 
   (I_MoveSTM_i0(idd))
    \<parallel>\<^bsub> flow_event_MoveSTM_not_Move \<^esub> 
   State_MoveSTM_Move_R(idd)
"

definition MoveSTM_opt_0_internal_set where
"MoveSTM_opt_0_internal_set = 
   set ([internal_MoveSTM_C TID_MoveSTM_t0] @
       (enumchan2 reset__MoveSTM_C [TID_MoveSTM_t2] [din, dout])
)"

definition MoveSTM_opt_1_internal_set where
"MoveSTM_opt_1_internal_set = 
   set ((enumchan3 update__MoveSTM_C [TID_MoveSTM_t1] [din, dout] rc.core_int_list) @ 
      (enumchan3 update__MoveSTM_C [TID_MoveSTM_t3] [din, dout] rc.core_int_list)
)"

subsubsection \<open> State machine \<close>
definition MemorySTM_opt_MoveSTM where
"MemorySTM_opt_MoveSTM (idd::integer) = 
  (
    (
      (
        (
          (
            (
              (discard_state (MoveSTM_Memory_opt_l 0))
              \<parallel>\<^bsub> MoveSTM_l_events \<^esub>
              (
                (
                  (discard_state (MoveSTM_Memory_opt_x 0))
                  \<parallel>\<^bsub> MoveSTM_x_events \<^esub>
                  (STM_MoveSTM idd)
                ) \<setminus> (set [get_x_MoveSTM_C n. n \<leftarrow> rc.core_int_list])
              )
            ) \<setminus> MoveSTM_l_events
          ) 
          \<parallel>\<^bsub> MoveSTM_opt_0_internal_set \<^esub>
          (discard_state (MoveSTM_MemoryTransitions_opt_0 idd))
        ) \<setminus> {internal_MoveSTM_C TID_MoveSTM_t0}
      )
      \<parallel>\<^bsub> MoveSTM_opt_1_internal_set \<^esub>
      (discard_state (MoveSTM_MemoryTransitions_opt_1 idd))
    ) \<setminus> {}
  )
"

definition MemorySTM_opt_MoveSTM_p where
"MemorySTM_opt_MoveSTM_p (idd::integer) = 
  (
    (
      (
        (
          (
            (
              (discard_state (MoveSTM_Memory_opt_l 0))
              \<parallel>\<^bsub> MoveSTM_l_events \<^esub>
              (
                (
                  (discard_state (MoveSTM_Memory_opt_x 0))
                  \<parallel>\<^bsub> MoveSTM_x_events \<^esub>
                  (STM_MoveSTM idd)
                ) \<setminus>\<^sub>p ([get_x_MoveSTM_C n. n \<leftarrow> rc.core_int_list])
              )
            ) \<setminus>\<^sub>p MoveSTM_l_events_l
          ) 
          \<parallel>\<^bsub> MoveSTM_opt_0_internal_set \<^esub>
          (discard_state (MoveSTM_MemoryTransitions_opt_0 idd))
        ) \<setminus>\<^sub>p [internal_MoveSTM_C TID_MoveSTM_t0]
      )
      \<parallel>\<^bsub> MoveSTM_opt_1_internal_set \<^esub>
      (discard_state (MoveSTM_MemoryTransitions_opt_1 idd))
    ) \<setminus>\<^sub>p []
  )
"

(* [..., (update__MoveSTM_C. TID_MoveSTM_t1), ..., (update__MoveSTM_C. TID_MoveSTM_t3), ...] *)
definition rename_MoveSTM_events where
"rename_MoveSTM_events = concat (
  (enumchan1 (forget_first reset__MoveSTM_C reset_MoveSTM_C TIDS_MoveSTM_list) InOut_list) @
  (enumchan2 (forget_first2 left__MoveSTM_C left_MoveSTM_C TIDS_MoveSTM_list) InOut_list rc.core_int_list) @
  (enumchan2 (forget_first2 right__MoveSTM_C right_MoveSTM_C TIDS_MoveSTM_list) InOut_list rc.core_int_list) @
  (enumchan2 (forget_first2 update__MoveSTM_C update_MoveSTM_C TIDS_MoveSTM_list) InOut_list rc.core_int_list)
)
"

value "rename_MoveSTM_events"

definition rename_MoveSTM_events_others where
"rename_MoveSTM_events_others = 
  (enumchanp1 terminate_MoveSTM_C [()]) @
  (enumchanp1 shared_x_MoveSTM_C [()]) @
  (enumchansp1 [get_x_MoveSTM_C, set_x_MoveSTM_C, set_EXT_x_MoveSTM_C] rc.core_int_list) @
  (enumchansp1 [reset_MoveSTM_C] InOut_list) @
  (enumchansp2 [left_MoveSTM_C] InOut_list rc.core_int_list) @
  (enumchansp2 [right_MoveSTM_C] InOut_list rc.core_int_list) @
  (enumchansp2 [update_MoveSTM_C] InOut_list rc.core_int_list) @
  (enumchansp2 [enter_MoveSTM_C, entered_MoveSTM_C, exit_MoveSTM_C, exited_MoveSTM_C] SIDS_MoveSTM_list SIDS_MoveSTM_list)
"

value "rename_MoveSTM_events_others"
(* For this syntax to work, the types in a channel type must be enumerable. Here integer seems not to be enumerable. *)
value "\<lbrace>update__MoveSTM (t, d, x) \<mapsto> update_MoveSTM (d, x) | (t, d, x). d \<in> InOut_set \<and> x \<in> rc.core_int_set\<rbrace>"

(*
  How to rename this process to avoid deadlock (resolve nondeterminism in some ways) between two transitions
from Move with overlapped guards and the same trigger?
Brain storms:
S1. Preprocess renaming map (which is a list of pairs in this example) to drop the later pairs whose 
range are the same as one of pair in the early (top) of the list.
- This doesn't work because each renaming map should be only applied to the initial events of the process.
so (a \<rightarrow> P \<box> b \<rightarrow> c \<rightarrow> Q) \<lbrace> (a, d), (c, d) \<rbrace> = (d \<rightarrow> P \<lbrace> (a, d), (c, d) \<rbrace>) \<box> (b \<rightarrow> d \<rightarrow> Q \<lbrace> (a, d), (c, d) \<rbrace>)

*)
definition rename_MemorySTM_opt_MoveSTM where
"rename_MemorySTM_opt_MoveSTM idd = 
  ((MemorySTM_opt_MoveSTM idd) \<lbrace>(set (rename_MoveSTM_events @ rename_MoveSTM_events_others))\<rbrace>)
"

text \<open>In the renaming list, @{text "(update__MoveSTM_C. TID_MoveSTM_t1)"}  has a higher priority than 
@{text "(update__MoveSTM_C. TID_MoveSTM_t3)"}, and finally moving right (the @{text "right"} event) 
is chosen. \<close>
definition rename_MemorySTM_opt_MoveSTM_p where
"rename_MemorySTM_opt_MoveSTM_p idd = 
  ((MemorySTM_opt_MoveSTM_p idd) \<lbrace>(rename_MoveSTM_events @ rename_MoveSTM_events_others)\<rbrace>\<^sub>p)
"

definition AUX_opt_MoveSTM where
"AUX_opt_MoveSTM (idd::integer) = 
  ( 
    ( 
      (rename_MemorySTM_opt_MoveSTM idd) \<lbrakk> set [terminate_MoveSTM_C ()] \<Zrres> skip
    ) \<setminus> MoveSTM_MachineInternalEvents
  )
"

definition AUX_opt_MoveSTM_p where
"AUX_opt_MoveSTM_p (idd::integer) = 
  ( 
    ( 
      (rename_MemorySTM_opt_MoveSTM_p idd) \<lbrakk> set [terminate_MoveSTM_C ()] \<Zrres> skip
    ) \<setminus>\<^sub>p MoveSTM_MachineInternalEvents_l
  )
"

definition D__MoveSTM where
"D__MoveSTM (idd::integer) = 
  (AUX_opt_MoveSTM idd) \<setminus> internal_events_MoveSTM
"

definition D__MoveSTM_p where
"D__MoveSTM_p (idd::integer) = 
  (AUX_opt_MoveSTM_p idd) \<setminus>\<^sub>p internal_events_MoveSTM_l
"

subsection \<open> Controller \label{ssec:basic_Ctrl}\<close>
text \<open> A controller has a different channel type from those of state machines. Here, we declare a 
new channel type @{term Chan_Ctrl} for @{text Ctrl}. The events of @{text CalSTM} and @{text MoveSTM} are 
renamed to the events in @{term Chan_Ctrl}.

We note the event @{text update} in the model is not an event of @{text Ctrl}, and we introduce the 
event @{term update_Ctrl} here to let the events @{term update_CalSTM} and @{term update_MoveSTM} mapped to it.
By this way, @{term update_CalSTM} and @{term update_MoveSTM} are linked.
\<close>

chantype Chan_Ctrl =
(* terminates of CalSTM and MoveSTM are mapped to it *)
  terminate_Ctrl :: unit 
(* variable channels: set_x and get_x of CalSTM and MoveSTM are mapped to these channels *)
  set_x_Ctrl :: core_int
  get_x_Ctrl :: core_int
  shared_x_Ctrl :: unit
(* shared variable channels *)
  set_EXT_x_Ctrl :: core_int
(* set_EXT_x of CalSTM is mapped to this *)
  set_EXT_x_Ctrl_CalSTM :: core_int
(* set_EXT_x of MoveSTM is mapped to this *)
  set_EXT_x_Ctrl_MoveSTM :: core_int
(* rec of CalSTM is mapped to it *)
  cal_Ctrl :: "InOut \<times> core_int"
(* reset of MoveSTM is mapped to it *)
  reset_Ctrl :: "InOut"
  left_Ctrl :: "InOut \<times> core_int"
  right_Ctrl :: "InOut \<times> core_int"
(* update of CalSTM is mapped to update_Ctrl.out and update of MoveSTM is mapped to update_Ctrl.in *)
  update_Ctrl :: "InOut \<times> core_int"

definition shared_variable_events_Ctrl where
"shared_variable_events_Ctrl = 
  set (enumchan1 set_EXT_x_Ctrl_C rc.core_int_list)"

subsubsection \<open> Memory \<close>
text \<open> The memory of @{text Ctrl}, @{term Memory_Ctrl}, relays the update of @{text x} 
from @{text PatrolMod} to @{text CalSTM} and @{text MoveSTM}.
We note that the update of @{text x} here introduces nondeterminism because it is possible that 
@{text x} in @{text CalSTM} has been updated, but @{text x} in @{text MoveSTM} has not been updated.
The @{text "Ret (id)"} here passes the value of @{text id} to the next loop.
\<close>

definition Memory_Ctrl where
"Memory_Ctrl = loop (\<lambda> id::integer.
  ( do {x \<leftarrow> inp_in set_EXT_x_Ctrl rc.core_int_set; 
        outp set_EXT_x_Ctrl_CalSTM x; 
        outp set_EXT_x_Ctrl_MoveSTM x; 
        outp shared_x_Ctrl (); Ret (id)}
  )
)"

subsubsection \<open> Controller \<close>
text \<open>For @{term D__CalSTM}, its events are renamed to the corresponding events in @{term Chan_Ctrl}. 
The renaming relation is defined in @{term rename_Ctrl_CalSTM_events} where the event of 
@{term update_CalSTM_C} is renamed to that of @{term update_Ctrl_C} with the same direction and value.
\<close>

definition rename_Ctrl_CalSTM_events where
"rename_Ctrl_CalSTM_events = 
  (enumchanp2_1 (terminate_CalSTM_C,terminate_Ctrl_C) [()]) @
  (enumchanp2_1 (shared_x_CalSTM_C, shared_x_Ctrl_C) [()]) @
  (enumchansp2_1 [(set_x_CalSTM_C, set_x_Ctrl_C), (get_x_CalSTM_C, get_x_Ctrl_C), 
      (set_EXT_x_CalSTM_C, set_EXT_x_Ctrl_CalSTM_C)] rc.core_int_list) @
  (enumchansp2_2 [(cal_CalSTM_C, cal_Ctrl_C), (update_CalSTM_C, update_Ctrl_C)] InOut_list rc.core_int_list)"

definition rename_D__CalSTM where
"rename_D__CalSTM idd = ((D__CalSTM idd) \<lbrace>(set rename_Ctrl_CalSTM_events)\<rbrace>)"

definition rename_D__CalSTM_p where
"rename_D__CalSTM_p idd = ((D__CalSTM_p idd) \<lbrace>(rename_Ctrl_CalSTM_events)\<rbrace>\<^sub>p)"


text \<open>For @{term D__MoveSTM}, its events are also renamed to the corresponding events in @{term Chan_Ctrl}. 
The renaming relation is defined in @{term rename_Ctrl_MoveSTM_events} where the event of 
@{term update_CalSTM_C} is renamed to that of @{term update_Ctrl_C} with the opposite direction and the same 
value. By this way, we connect the output of @{text update} in @{text CalSTM} to the input of @{text update} 
in @{text MoveSTM}.
\<close>
definition rename_Ctrl_MoveSTM_events where
"rename_Ctrl_MoveSTM_events = 
  (enumchanp2_1 (terminate_MoveSTM_C,terminate_Ctrl_C) [()]) @
  (enumchanp2_1 (shared_x_MoveSTM_C, shared_x_Ctrl_C) [()]) @
  (enumchansp2_1 [(set_x_MoveSTM_C, set_x_Ctrl_C), (get_x_MoveSTM_C, get_x_Ctrl_C), 
      (set_EXT_x_MoveSTM_C, set_EXT_x_Ctrl_MoveSTM_C)] rc.core_int_list) @
  (enumchansp2_1 [(reset_MoveSTM_C, reset_Ctrl_C)] InOut_list) @
  (enumchansp2_2 [(left_MoveSTM_C, left_Ctrl_C)] InOut_list rc.core_int_list) @
  (enumchansp2_2 [(right_MoveSTM_C, right_Ctrl_C)] InOut_list rc.core_int_list) @
\<comment> \<open>It is important to invert directions in one side: either CalSTM or MoveSTM \<close>
  (enumchansp2_1 [((curry update_MoveSTM_C) din, (curry update_Ctrl_C) dout), 
      ((curry update_MoveSTM_C) dout, (curry update_Ctrl_C) din)] rc.core_int_list)
"

definition rename_D__MoveSTM where
"rename_D__MoveSTM idd = ((D__MoveSTM idd) \<lbrace>(set rename_Ctrl_MoveSTM_events)\<rbrace>)"

definition rename_D__MoveSTM_p where
"rename_D__MoveSTM_p idd = ((D__MoveSTM_p idd) \<lbrace>rename_Ctrl_MoveSTM_events\<rbrace>\<^sub>p)"

text \<open>The @{term Ctrl_stms_events} below gives a set of synchronisation events between @{text CalSTM} 
and @{text MoveSTM} which includes termination and @{text update}.
\<close>
definition "Ctrl_stms_events_l = 
  enumchan2 update_Ctrl_C InOut_list rc.core_int_list
"

definition "Ctrl_stms_events = set (
  enumchan1 terminate_Ctrl_C [()] @ 
  Ctrl_stms_events_l
)"

text \<open>The memory update events for @{text CalSTM} and @{text MoveSTM} are defined in 
@{term Ctrl_mem_events}. \<close>
definition "Ctrl_mem_events_l = (
  enumchans1 [set_EXT_x_Ctrl_CalSTM_C, set_EXT_x_Ctrl_MoveSTM_C] rc.core_int_list @
  enumchan1 shared_x_Ctrl_C [()]
)"

definition "Ctrl_mem_events = set Ctrl_mem_events_l"

text \<open>So the controller @{text Ctrl} is the composition of the renamed @{text CalSTM}, the renamed 
@{text MoveSTM}, and its memory with appropriate event hiding. \<close>
definition D__Ctrl where
"D__Ctrl (idd::integer) = 
  (par_hide
    ( 
      ((rename_D__CalSTM idd) \<parallel>\<^bsub> Ctrl_stms_events \<^esub> (rename_D__MoveSTM idd))
      \<setminus> (Ctrl_stms_events - set [terminate_Ctrl_C ()])
    )
    Ctrl_mem_events
    (discard_state (Memory_Ctrl idd))
  )  \<lbrakk> set [terminate_Ctrl_C ()] \<Zrres> skip
"

definition D__Ctrl_p where
"D__Ctrl_p (idd::integer) = 
  (par_hidep
    ( 
      ((rename_D__CalSTM_p idd) \<parallel>\<^bsub> Ctrl_stms_events \<^esub> (rename_D__MoveSTM_p idd))
      \<setminus>\<^sub>p Ctrl_stms_events_l
    )
    Ctrl_mem_events_l
    (discard_state (Memory_Ctrl idd))
  )  \<lbrakk> set [terminate_Ctrl_C ()] \<Zrres> skip
"

subsection \<open> Module \label{ssec:basic_PatrolMod}\<close>
text \<open>Similar to the controller, a module also has a different channel type from that of the 
controller. Here, we declare a new channel type @{term Chan_PatrolMod} for @{text PatrolMod}. 
The events of @{text Ctrl} are renamed to those of @{term Chan_PatrolMod}.
\<close>
chantype Chan_PatrolMod =
(* terminates of Ctrl are mapped to it *)
  terminate_PatrolMod :: unit 
(* variable channels: set_x and get_x of CalSTM and MoveSTM are mapped to these channels *)
  shared_x_PatrolMod :: unit
  set_x_PatrolMod :: core_int
  get_x_PatrolMod :: core_int
(* shared variable channels *)
  set_EXT_x_PatrolMod_Ctrl :: core_int
(* e1 of CalSTM is mapped to it *)
  cal_PatrolMod :: "InOut \<times> core_int"
(* e2 of MoveSTM is mapped to it *)
  reset_PatrolMod :: "InOut"
  left_PatrolMod :: "InOut \<times> core_int"
  right_PatrolMod :: "InOut \<times> core_int"

subsubsection \<open> Memory \<close>
text \<open>The memory of @{text PatrolMod} accepts an update to @{text x} and then propagates this update to 
the controller. Finally, the update will reach the all controllers and state machines 
that require @{text x}, such as @{text Ctrl}, @{text CalSTM}, and @{text MoveSTM} in this model.
\<close>
definition Memory_PatrolMod where
"Memory_PatrolMod = loop (\<lambda> id::integer.
  ( do {x \<leftarrow> inp_in set_x_PatrolMod rc.core_int_set; 
        outp set_EXT_x_PatrolMod_Ctrl x; 
        outp shared_x_PatrolMod ();
        Ret (id)}
  )
)"

subsubsection \<open> Module \<close>
text \<open>The renaming relation from @{text Ctrl} to @{text PatrolMod}, defined by 
@{term rename_PatrolMod_Ctrl_events} is simple and straightforward.
\<close>
definition rename_PatrolMod_Ctrl_events where
"rename_PatrolMod_Ctrl_events = 
  (enumchanp2_1 (terminate_Ctrl_C,terminate_PatrolMod_C) [()]) @
  (enumchanp2_1 (shared_x_Ctrl_C, shared_x_PatrolMod_C) [()]) @
  (enumchansp2_1 [(set_x_Ctrl_C, set_x_PatrolMod_C), (get_x_Ctrl_C, get_x_PatrolMod_C), 
      (set_EXT_x_Ctrl_C, set_EXT_x_PatrolMod_Ctrl_C)] rc.core_int_list) @
  (enumchanp2_1 (reset_Ctrl_C, reset_PatrolMod_C) InOut_list) @
  (enumchanp2_2 (left_Ctrl_C, left_PatrolMod_C) InOut_list rc.core_int_list) @
  (enumchanp2_2 (right_Ctrl_C, right_PatrolMod_C) InOut_list rc.core_int_list) @
  (enumchanp2_2 (cal_Ctrl_C, cal_PatrolMod_C) InOut_list rc.core_int_list)
"

definition rename_D__Ctrl where
"rename_D__Ctrl idd = ((D__Ctrl idd) \<lbrace>(set rename_PatrolMod_Ctrl_events)\<rbrace>)"

definition rename_D__Ctrl_p where
"rename_D__Ctrl_p idd = ((D__Ctrl_p idd) \<lbrace>rename_PatrolMod_Ctrl_events\<rbrace>\<^sub>p)"

definition "PatrolMod_set_x_events_l = (
  enumchan1 set_x_PatrolMod_C  rc.core_int_list
)"

definition "PatrolMod_set_x_events = set PatrolMod_set_x_events_l"

definition "PatrolMod_get_x_events_l = (
  enumchan1 get_x_PatrolMod_C  rc.core_int_list
)"

definition "PatrolMod_get_x_events = set PatrolMod_get_x_events_l"

definition "PatrolMod_set_EXT_x_events_l = (
  enumchan1 set_EXT_x_PatrolMod_Ctrl_C  rc.core_int_list
)"

definition "PatrolMod_set_EXT_x_events = set PatrolMod_set_EXT_x_events_l"

definition D__ctr_mem where
"D__ctr_mem (idd::integer) = (
              (rename_D__Ctrl idd) 
              \<parallel>\<^bsub> (PatrolMod_set_x_events \<union> PatrolMod_set_EXT_x_events) \<^esub> 
              (discard_state (Memory_PatrolMod idd))
            )"

text \<open>Finally, the module is a composition of the renamed @{text Ctrl} and the memory of 
@{text PatrolMod} with a possibility to terminate through the exception operator.
\<close>
definition D__PatrolMod where
"D__PatrolMod (idd::integer) = 
  (
    (
      (skip \<parallel>\<^bsub> {} \<^esub> 
        (
          (
            (rename_D__Ctrl idd) 
            \<parallel>\<^bsub> (PatrolMod_set_x_events \<union> PatrolMod_set_EXT_x_events) \<^esub> 
            (discard_state (Memory_PatrolMod idd))
          ) \<setminus> ((PatrolMod_set_x_events \<union> PatrolMod_get_x_events) \<union> PatrolMod_set_EXT_x_events)
        )
      )  \<lbrakk> set [terminate_PatrolMod_C ()] \<Zrres> skip
    ) \<setminus> (set [terminate_PatrolMod_C ()])
  )
"

definition D__PatrolMod_p where
"D__PatrolMod_p (idd::integer) = 
  (
    (
      (skip \<parallel>\<^bsub> {} \<^esub> 
        (
          (
            (rename_D__Ctrl_p idd) 
            \<parallel>\<^bsub> (PatrolMod_set_x_events \<union> PatrolMod_set_EXT_x_events \<union> {(shared_x_PatrolMod_C ())}) \<^esub> 
            (discard_state (Memory_PatrolMod idd))
          ) \<setminus>\<^sub>p (PatrolMod_set_EXT_x_events_l @ (PatrolMod_set_x_events_l @ PatrolMod_get_x_events_l))
        )
      )  \<lbrakk> set [terminate_PatrolMod_C ()] \<Zrres> skip
    ) \<setminus>\<^sub>p ([terminate_PatrolMod_C ()])
  )
"

(*
definition D__PatrolMod_p where
"D__PatrolMod_p (idd::integer) = 
  (
    (
      (skip \<parallel>\<^bsub> {} \<^esub> 
        (
          (
            (rename_D__Ctrl_p idd) 
            \<parallel>\<^bsub> (PatrolMod_set_x_events \<union> PatrolMod_set_EXT_x_events) \<^esub> 
            (discard_state (Memory_PatrolMod idd))
          ) \<setminus>\<^sub>p ((PatrolMod_set_x_events_l @ PatrolMod_get_x_events_l) @ PatrolMod_set_EXT_x_events_l)
        )
      )  \<lbrakk> set [terminate_PatrolMod_C ()] \<Zrres> skip
    ) \<setminus>\<^sub>p ([terminate_PatrolMod_C ()])
  )
"
*)

text \<open>We can animate @{term D__PatrolMod} in Isabelle/HOL by the @{term animate} command. This command 
only works on a customised version of Isabelle, based on Isabelle2021.
\<close>
definition "D_PatrolMod_sim = D__PatrolMod 0"
(* animate1 D_PatrolMod_sim *)

definition "D_PatrolMod_p_sim = D__PatrolMod_p 0"
animate1 D_PatrolMod_p_sim

subsection \<open> Export code \<close>
text \<open>We export various processes to Haskell. These processes can be animated with ghci. 
By this way, we can debug a process at the first place when it is defined. Actually, it is not 
mandatory to export code since we have supported the @{term animate} command. However, due to the 
fact that the command cannot work on a standard Isabelle, it is better to keep exporting code because 
this way works on both the standard Isabelle and the customised version.
\<close>
export_code
  CalSTM_Memory_opt_x
  CalSTM_Memory_opt_l
  CalSTM_MemoryTransitions_opt_0
  CalSTM_MemoryTransitions_opt_1
  I_CalSTM_i0
  State_CalSTM_Cal
  State_CalSTM_Cal_R
  STM_CalSTM
  MemorySTM_opt_CalSTM 
  rename_MemorySTM_opt_CalSTM
  D__CalSTM 
  MoveSTM_Memory_opt_x
  MoveSTM_MemoryTransitions_opt_0
  I_MoveSTM_i0
  State_MoveSTM_Move
  State_MoveSTM_Move_R
  STM_MoveSTM
  MemorySTM_opt_MoveSTM
  rename_MemorySTM_opt_MoveSTM
  rename_MemorySTM_opt_MoveSTM_p
  D__MoveSTM
  rename_D__CalSTM
  rename_D__MoveSTM
  D__Ctrl
  rename_D__Ctrl
  D__ctr_mem
  D__PatrolMod
  in Haskell 
  (* module_name RoboChart_basic *)
  file_prefix RoboChart_basic_v1 
  (string_classes) 

text \<open>A simulation file is generated as a pure Haskell code. \<close>
generate_file \<open>code/RoboChart_basic_v1/Simulate.hs\<close> = 
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

text \<open>The @{verbatim Main.hs} generated below is the main module in the generated code which is used 
to compile and build the generated code to an executable file by ghc. We note a compiled version has 
better performance than the interpreted version by ghci.
\<close>
generate_file \<open>code/RoboChart_basic_v1/Main.hs\<close> = 
\<open>import qualified Interaction_Trees;
import qualified Partial_Fun;
import qualified Simulate;
import qualified RoboChart_basic_v1;

main :: IO ()
main =
  do
    Simulate.simulate (RoboChart_basic_v1.d_PatrolMod 0);
\<close>

export_generated_files 
  \<open>code/RoboChart_basic_v1/Simulate.hs\<close>
  \<open>code/RoboChart_basic_v1/Main.hs\<close>

end
