section \<open> Simulation of a very basic RoboChart model \<close>
text \<open> This theory aims for simulation of a trivial RoboChart model (see 
Figure~\ref{fig:robochart_basic}) based on its CSP semantics. We add a transition t4 in stm1 to 
investigate further about nondeterminism in this model version, compared to RoboChart_basic_v1.
\begin{figure}
  \includegraphics[scale=0.25]{images/system}
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

We note this theory is not directly translated from the RoboChart model. 
Instead, it is translated from the standard CSP semantics (under @{verbatim "csp-gen/defs"}) of 
the model which is generated in RoboTool, particularly the file @{verbatim "mod0.csp"}. 
In the CSP semantics, there are a variety of versions, such as default 
(@{verbatim "Dunopt__"}), optimised (@{verbatim "D__"}), optimised with compressions 
(@{verbatim "O__"}), visible (@{verbatim "VS__"}) etc. Here, we choose the optimised version 
(@{verbatim "D__"}) because the version of the optimised with compressions (@{verbatim "O__"}) is 
used for checking core assertions in RoboTool and compressions are not implemented here.

To decide which part of the CSP semantics should be translated, we use the top-down approach, 
starting from the @{verbatim "D__(id__)"} process for the module @{text mod0}, then to the controller,
and finally to the state machines. By this way, we know which channels, definitions, and processes 
are used in the version, and, therefore, they should be translated in this theory. For example, 
channel @{verbatim "enter"} should be included, but channel @{verbatim "enterV"} is not. 

This theory, on the contrary, is built from the bottom up because the definition of a top process 
relies on the definitions of other processes in the top process. 
\<close>
theory RoboChart_basic_v1_add_t4
  imports "ITree_RoboChart.ITree_RoboChart" 
    "ITree_Simulation.ITree_Simulation"
    "ITree_RoboChart.RoboChart_Simulation"
begin

text \<open>We, therefore, structure the theory as follows. In Sect.~\ref{ssec:basic_general}, we give 
general definitions. 
Then we define processes for @{text stm0} in Sect.~\ref{ssec:basic_stm0}, for @{text stm1} in 
Sect.~\ref{ssec:basic_stm1}, for @{text ctr0} in Sect.~\ref{ssec:basic_ctr0}, and for @{text mod0} 
in Sect.~\ref{ssec:basic_mod0}.
\<close>

subsection \<open> General definitions \label{ssec:basic_general}\<close>
text \<open> The interpretation of the locale @{text robochart_confs} below instantiates 
@{term "min_int"}, @{term "max_int"}, @{term "max_nat"}, @{term "min_real"}, 
and @{term "max_real"}, to -1, 1, 1, -1, and 1 separately. In the CSP semantics, these values are 
set in the @{verbatim "instantiation.csp"} file.
\<close>
interpretation rc: robochart_confs "-2" "2" "1" "-1" "1".

(* We can animate this theory with [-50, 50]. 
For the input E2, the animation is very smooth, and we can see the next events available to execute 
quite fast. This is the same case for the E1(Din, 0).
But for other cases, it will take about 15 seconds to compute 2000 internal steps in simulation, and 
then we see the next "Many steps (> 2000); Continue? [Y/N]" available to choose continuation or 
termination.
*)
(* interpretation rc: robochart_confs "-50" "50" "1" "-1" "1". *)

subsection \<open> State machine @{text stm0} \label{ssec:basic_stm0}\<close>
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
@{verbatim "module stm0"}, and so the names like @{verbatim SIDS} can be used in the module directly.
This theory here, however, is not based on a modular approach, and so the names like @{text SIDS} 
cannot be used to denote a state identifier type for @{text stm0}. Otherwise, it will cause a name 
conflict with @{text SIDS} for other state machines. For this reason, we add a suffix 
(the state machine name) to these names such as @{text SIDS_stm0}.
\<close>

text \<open> @{term "SIDS_stm0"} defines state identifiers for @{text "stm0"}, which include 
the machine itself and the state @{text "s0"}.
Another possibly better way to define such a type for identifiers is through a more generic typedef 
with two type variables: one to make the type distinct for a particular state machine, and another 
is a enumerable type (@{class enum}), such as a numeral type (@{typ "2"}), to denote all identifiers 
(0 and 1 for this example). Please see @{term TrID} in @{verbatim ITree_RoboChart.thy} for more 
details. At this moment, we cannot use it now because we have not instantiated @{term TrID} for 
@{class enum}, which is necessary to enumerate all elements for such a type, like 
@{term "SIDS_stm0_list"} below.
\<close>
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
  internal_stm0 :: TIDS_stm0
  enter_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  entered_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  exit_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  exited_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  terminate_stm0 :: unit
  get_l_stm0 :: core_int (* variable channels : the next 3 channels will be hidden *)
  set_l_stm0 :: core_int
  get_x_stm0 :: core_int
  set_x_stm0 :: core_int (* this won't be hidden, and will be renamed to set_x_ctr0 *)
  set_EXT_x_stm0 :: core_int (* shared variable channels, and will be renamed to set_EXT_x_ctr0_stm0 *)
  rec__stm0 :: "TIDS_stm0 \<times> InOut \<times> core_int" (* event channels will be renamed to rec_stm0 (may introduce nondeterminism) *)
  rec_stm0 :: "InOut \<times> core_int"   (* will be further renamed to rec_ctr0 *)
  update__stm0 :: "TIDS_stm0 \<times> InOut \<times> core_int"   (* will be renamed to update_ctr0.out *)
  update_stm0 :: "InOut \<times> core_int"

text \<open> Here, we use the following conventions.
\begin{itemize}
  \item a channel type: @{term "Chan_stm0"},
  \item channels (declared in @{term "Chan_stm0"}): @{term "internal_stm0"}, @{term "rec_stm0"}, etc.
  \begin{itemize}
    \item an internal trigger channel: @{term "internal_stm0"};
    \item flow control channels: @{term "enter_stm0"}, @{term "entered_stm0"}, @{term "exit_stm0"}, 
      and @{term "exited_stm0"};
    \item a terminate channel: @{term "terminate_stm0"};
    \item local variable channels: @{term "get_l_stm0"}, and @{term "set_l_stm0"};
    \item shared variable channels: @{term "get_x_stm0"}, @{term "set_x_stm0"}, and 
      @{term "set_EXT_x_stm0"};
    \item Event channels: trigger event channels (@{term "rec__stm0"} and @{term "update__stm0"}), 
      and action event channels (@{term "rec_stm0"} and @{term "update_stm0"}).
  \end{itemize}
  \item a channel event: an event starting with the name of a channel and carrying a value on the 
  channel, such as @{text "internal_stm0 TID_stm0_t1"};
  %\item the data type of a channel (@{term "rec_stm0"}): @{typeof "rec_stm0_C"};
  \item the type of a channel (@{term "rec_stm0"}): @{typeof "rec_stm0"}, a prism from the data type 
    of the channel to the channel type.
\end{itemize}
\<close>

subsubsection \<open> Sets of events \<close>
text \<open> @{term "int_int_stm0"} defines a set of internal channel events that can interrupt states.  
\<close>
definition int_int_stm0 where
"int_int_stm0 = 
  set ((enumchans3 [rec__stm0_C, update__stm0_C] [TID_stm0_t1,TID_stm0_t2] [din, dout] rc.core_int_list) @
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
      \<comment> \<open> enter and exit from x to y \<close>
      (enumchans2 [enter_stm0_C, entered_stm0_C, exit_stm0_C, exited_stm0_C] [SID_stm0_s0] [SID_stm0_s0])@
      \<comment> \<open> enter and exit from y to x \<close>
      (enumchans2 [enter_stm0_C, entered_stm0_C, exit_stm0_C, exited_stm0_C] [SID_stm0_s0] [SID_stm0_s0])
)"

text \<open> @{term "stm0_s0_triggers"} defines a set of channel events that act as triggers of transitions
. \<close>
definition stm0_s0_triggers where
"stm0_s0_triggers = 
  set ((enumchan3 rec__stm0_C [TID_stm0_t1,TID_stm0_t2] [din, dout] rc.core_int_list) @
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

text \<open> The @{term "stm0_Memory_opt_x"} defines a memory cell process for a shared variable @{term x}.\<close>
definition stm0_Memory_opt_x where
"stm0_Memory_opt_x = 
  mem_of_svar get_x_stm0 set_x_stm0 set_EXT_x_stm0 rc.core_int_set"

text \<open> The type of @{term "stm0_Memory_opt_x"} is @{typeof "stm0_Memory_opt_x"}, a function from 
the type of the variable @{term x} to an @{term itree} whose channel type is @{term Chan_stm0} and 
return type is the same as the type of the variable.\<close>

text \<open> The @{term "stm0_Memory_opt_l"} is a memory cell process for a local variable @{term l}.\<close>
definition stm0_Memory_opt_l where
"stm0_Memory_opt_l = mem_of_lvar get_l_stm0 set_l_stm0 rc.core_int_set"

paragraph \<open> Memory transition processes \<close>
text \<open> Both @{term "stm0_MemoryTransitions_opt_0"} and @{term "stm0_MemoryTransitions_opt_1"} are memory 
processes for transitions, particularly the guards of transitions evaluated in the processes. They also 
have a parameter @{text "id"}.
\<close>
text \<open> For @{term "stm0_MemoryTransitions_opt_0"}, we manually add an external choice with 
@{term deadlock} to tackle an issue that the instance of @{verbatim \<open>(Eq Chan_stm0)\<close>} won't be 
generated if there is no equality checking. However, this instance is necessary for our animation. 
We, therefore, deliberately enable an equality checking by adding an external choice with 
@{term deadlock} (and this will not change the semantics). For this theory, actually this addition is
not necessary because there are equality checking in other processes. But, in case of an error like 
(@{verbatim "No instance for (Eq Chan) arising from a use of simulate"}), this is a feasible 
solution.
\<close>
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
        \<comment> \<open>This constrained input prefixing corresponds to the input trigger with guard 
        (@{verbatim \<open>e1?l[x==0]\<close>}) of @{text t1}. \<close>
        do {inp_in rec__stm0 (set [(TID_stm0_t1, din, l). l \<leftarrow> rc.core_int_list, (x = 0)])
              ; Ret (id)} \<box>
        \<comment> \<open>This corresponds to the guard (@{verbatim \<open>[x!=0]\<close>}) of @{text t2}.\<close>
        do {guard (x \<noteq> 0); outp internal_stm0 TID_stm0_t2 ; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_x_stm0 rc.core_int_set; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_EXT_x_stm0 rc.core_int_set; Ret (id)}
      )
    }
  )
"

subsubsection \<open> States \<close>
text \<open> This section defines processes for junctions and states in the state machine. \<close>

text \<open> @{term "I_stm0_i0"} is for the initial junction @{verbatim i0} and the only transition from it
is @{verbatim t0} (to the state @{verbatim s0}). This transition has no trigger (and so an internal 
trigger channel @{term internal_stm0} is used to model it), no guard (and so 
@{term stm0_MemoryTransitions_opt_0} has no guard), has an action @{verbatim "x=0"} (update through 
a channel @{term set_x_stm0} with value @{term 0}. After it, @{text stm0} enters @{text s0}. 
We note @{term "I_stm0_i0"} is not a loop because it only executes once and then terminates.
\<close>

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

text \<open> The definition of the CSP process @{verbatim State_stm0_s0} has a mutual recursion. 
The process calls @{verbatim State_stm0_s0_execute} with an extra parameter for the source state of 
a transition entering this state @{text s0}, in addition to a normal @{verbatim id} parameter.
The process @{verbatim State_stm0_s0_execute} also calls @{verbatim State_stm0_s0}. Here, in the 
definition @{term State_stm0_s0} below, we use a 
loop (a special iteration whose boolean condition is always true) to model @{verbatim State_stm0_s0}
 and an embedded iteration to model @{verbatim State_stm0_s0_execute}. 
\<close>
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
                do {t \<leftarrow> inp_in rec__stm0 (set [(TID_stm0_t1, din, l) . l \<leftarrow> rc.core_int_list]) ;
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
                        outp update_stm0 (dout, x);
                        outp enter_stm0 (SID_stm0_s0, SID_stm0_s0);
                        Ret(True, fst (snd s), SID_stm0_s0)
                    } \<box>
                \<comment> \<open> @{text internal_stm0} \<close>
                do {
                    x \<leftarrow> inp_in internal_stm0 
                      (set tids_stm0_s0);
                    y \<leftarrow> inp_in exit_stm0 (set 
                      [(s, SID_stm0_s0) . s \<leftarrow> (removeAll SID_stm0_s0 SIDS_stm0_list)]);
                      outp exited_stm0 (fst y, SID_stm0_s0);
                      Ret (False, fst (snd s), SID_stm0_s0)
                    } \<box>
                \<comment> \<open> @{text rec__stm0} \<close>
                do {
                    x \<leftarrow> inp_in rec__stm0 (set [(s, d, l) . 
                        s \<leftarrow> tids_stm0_s0, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> rc.core_int_list]) ;
                    y \<leftarrow> inp_in exit_stm0 (set 
                        [(s, SID_stm0_s0) . s \<leftarrow> (removeAll SID_stm0_s0 SIDS_stm0_list)]);
                      outp exited_stm0 (fst y, SID_stm0_s0);
                      Ret (False, fst (snd s), SID_stm0_s0)
                    } \<box>
                \<comment> \<open> @{text update__stm0} \<close>
                do {
                    x \<leftarrow> inp_in update__stm0 (set [(s, d, l) . 
                        s \<leftarrow> tids_stm0_s0, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> rc.core_int_list]) ;
                    y \<leftarrow> inp_in exit_stm0 (set 
                        [(s, SID_stm0_s0) . s \<leftarrow> (removeAll SID_stm0_s0 SIDS_stm0_list)]);
                      outp exited_stm0 (fst y, SID_stm0_s0);
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

text \<open>In the definition above, we assemble the return value of the embedded iteration as a triple 
@{text ret}, whose first element is a boolean value denoting the condition of this iteration, whose 
second element is @{text id} from the parameter of @{term State_stm0_s0}, and whose third element is 
the source state of a transition entering @{text s0}. So in the body of the loop, we return a triple 
and pass it to the embedded iteration. Inside the iteration, if a process (such as the one for 
@{text T_stm0_t1}) continues the iteration (the definition of @{verbatim T_stm0_t1} calls 
@{verbatim State_stm0_s0_execute}), it just returns with a triple whose first element is 
true. Otherwise, the first element is false (see the process for the trigger event @{text rec__stm0}).
This corresponds to the termination of the iteration. In the body of the loop, then only @{text id} 
is returned to the loop. 
\<close>

text \<open>In the definition of @{term State_stm0_s0_R} below, its parameter is named @{text idd}, 
instead of @{text id}, due to the fact that @{term "id"} is a predefined identity function in 
Isabelle/HOL. 
We also note that @{term State_stm0_s0} is not directly in parallel with @{term skip}. 
Instead, its return value is discarded by @{term discard_state} (simply by being sequentially 
composed with @{term skip}, and so the type of the return value matches with the type @{type unit} 
of the return value in @{term skip}. This is necessary for the parallel composition.
\<close>
definition State_stm0_s0_R where
"State_stm0_s0_R (idd::integer) = 
   (discard_state (State_stm0_s0 idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_stm0 - stm0_s0_triggers) \<^esub> 
   skip
"

text \<open> The @{term flow_event_stm0_not_s0} defined below gives a set of flow events that represents 
entering (or exiting from) @{text s0} from the all other states. 
\<close>
definition flow_event_stm0_not_s0 where 
"flow_event_stm0_not_s0 = set (
  enumchans2 [enter_stm0_C, entered_stm0_C,exit_stm0_C,exited_stm0_C] 
             SIDS_stm0_without_s0 [SID_stm0_s0]
)"

text \<open> @{term STM_stm0} is the composition of the processes for the initial junction and states. \<close>
definition STM_stm0 where
"STM_stm0 (idd::integer) = 
   (I_stm0_i0(idd))
    \<parallel>\<^bsub> flow_event_stm0_not_s0 \<^esub> 
   State_stm0_s0_R(idd)
"

subsubsection \<open> State machine \<close>
definition stm0_rec_x_internal_set where
"stm0_rec_x_internal_set = 
  set ((enumchan3 rec__stm0_C [TID_stm0_t1] [din, dout] rc.core_int_list) @ 
       [internal_stm0_C TID_stm0_t2] @
       (enumchan1 set_x_stm0_C rc.core_int_list)
)"

text \<open> @{text MemorySTM_opt_stm0} is the composition of @{term STM_stm0} and the memory (for 
variables and transitions) of the state machine. 
\<close>
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
          \<parallel>\<^bsub> stm0_rec_x_internal_set \<^esub> 
          (discard_state (stm0_MemoryTransitions_opt_1 idd))
        ) \<setminus> {internal_stm0_C TID_stm0_t2}
      )
    ) \<setminus> (set [get_x_stm0_C n. n \<leftarrow> rc.core_int_list])
  )   
"

text \<open> This definition actually defines a non-injective mapping as shown below.
@{text
  "[
    (rec__stm0_C (TID_stm0_t0, din, 0), rec_stm0_C (din, 0)),
    (rec__stm0_C (TID_stm0_t1, din, 0), rec_stm0_C (din, 0)), 
    ...
  ]"
}
here multiple @{term "rec__stm0"} events are mapped to one @{term "rec_stm0"} event.
\<close>
definition rename_stm0_events where
"rename_stm0_events = 
  concat ((enumchan2 (forget_first2 rec__stm0_C rec_stm0_C TIDS_stm0_list) InOut_list rc.core_int_list) @
          (enumchan2 (forget_first2 update__stm0_C update_stm0_C TIDS_stm0_list) InOut_list rc.core_int_list))
"

text \<open>For the events that are not renamed in CSP, we still need to have them in the relation map (
otherwise, these events will not be present in the renamed process), and they shall be mapped to 
themselves. 
\<close>
definition rename_stm0_events_others where
"rename_stm0_events_others = 
  (enumchanp1 terminate_stm0_C [()]) @
  (enumchansp1 [get_x_stm0_C, set_x_stm0_C, set_EXT_x_stm0_C] rc.core_int_list) @
  (enumchansp2 [rec_stm0_C, update_stm0_C] InOut_list rc.core_int_list) @
  (enumchansp2 [enter_stm0_C, entered_stm0_C, exit_stm0_C, exited_stm0_C] SIDS_stm0_list SIDS_stm0_list)
"

text \<open>So the renaming of @{term MemorySTM_opt_stm0} includes the events to be renamed 
(@{term rename_stm0_events}) and not to be renamed (@{term rename_stm0_events_others}).
\<close>
definition rename_MemorySTM_opt_stm0 where
"rename_MemorySTM_opt_stm0 idd =
    ((MemorySTM_opt_stm0 idd) \<lbrace>(set (rename_stm0_events @ rename_stm0_events_others))\<rbrace>)
"

text \<open>The exception operator allows @{term rename_MemorySTM_opt_stm0} to be terminated by the
@{term terminate_stm0} event. Furthermore, the @{term internal_stm0} channel events will be hidden.
\<close>
definition AUX_opt_stm0 where
"AUX_opt_stm0 (idd::integer) = 
  ( 
    ( 
      (rename_MemorySTM_opt_stm0 idd) \<lbrakk> set [terminate_stm0_C ()] \<Zrres> skip
    ) \<setminus> stm0_MachineInternalEvents
  )
"

text \<open>Additionally, the flow channel events are hidden.\<close>
definition D__stm0 where
"D__stm0 (idd::integer) = 
  (AUX_opt_stm0 idd) \<setminus> internal_events_stm0
"

subsection \<open> State machine @{text stm1} \label{ssec:basic_stm1}\<close>

definition "const_mod0_ctrl0_stm1_MAX \<equiv> 1"

datatype SIDS_stm1 = SID_stm1 | SID_stm1_s0

definition "SIDS_stm1_list = [SID_stm1, SID_stm1_s0]"
definition "SIDS_stm1_set = set SIDS_stm1_list"
definition "SIDS_stm1_without_s0 = (removeAll SID_stm1_s0 SIDS_stm1_list)"

datatype TIDS_stm1 = NULLTRANSITION_stm1
	              | TID_stm1_t0
	              | TID_stm1_t1
	              | TID_stm1_t2
	              | TID_stm1_t3
	              | TID_stm1_t4

instantiation TIDS_stm1 :: enum
begin
definition enum_TIDS_stm1 :: "TIDS_stm1 list" where
"enum_TIDS_stm1 = [NULLTRANSITION_stm1, TID_stm1_t0, TID_stm1_t1, TID_stm1_t2, TID_stm1_t3, TID_stm1_t4]"

definition enum_all_TIDS_stm1 :: "(TIDS_stm1 \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_TIDS_stm1 P = (\<forall>b :: TIDS_stm1 \<in> set enum_class.enum. P b)"

definition enum_ex_TIDS_stm1 :: "(TIDS_stm1 \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_TIDS_stm1 P = (\<exists>b ::  TIDS_stm1 \<in> set enum_class.enum. P b)"

instance
proof (intro_classes)
  show "distinct (enum_class.enum :: TIDS_stm1 list)"
    by (simp add: enum_TIDS_stm1_def)

  show univ_eq: "UNIV = set (enum_class.enum:: TIDS_stm1 list)"
    apply (simp add: enum_TIDS_stm1_def)
    apply (auto simp add: enum_UNIV)
    by (meson TIDS_stm1.exhaust)

  fix P :: "TIDS_stm1 \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P" 
    by (simp_all add: univ_eq enum_all_TIDS_stm1_def enum_ex_TIDS_stm1_def)
qed
end

definition "TIDS_stm1_list = [NULLTRANSITION_stm1, TID_stm1_t0, TID_stm1_t1, TID_stm1_t2, TID_stm1_t3, TID_stm1_t4]"
definition "TIDS_stm1_set = set TIDS_stm1_list"

definition "ITIDS_stm1_list = [TID_stm1_t1, TID_stm1_t2, TID_stm1_t3, TID_stm1_t4]"
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
  reset__stm1 :: "TIDS_stm1 \<times> InOut"
  reset_stm1 :: "InOut"
  update__stm1 :: "TIDS_stm1 \<times> InOut \<times> core_int"
  update_stm1 :: "InOut \<times> core_int"

subsubsection \<open> Sets of events \<close>
definition int_int_stm1 where
"int_int_stm1 = 
  set ((enumchan2 reset__stm1_C [TID_stm1_t1,TID_stm1_t2,TID_stm1_t3,TID_stm1_t4] [din, dout]) @
       (enumchan3 update__stm1_C [TID_stm1_t1,TID_stm1_t2,TID_stm1_t3,TID_stm1_t4] [din, dout] rc.core_int_list) @
       (enumchan1 internal_stm1_C [TID_stm1_t1,TID_stm1_t2,TID_stm1_t3,TID_stm1_t4])
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
  set ((enumchan2 reset__stm1_C [TID_stm1_t2] [din, dout]) @
       (enumchan3 update__stm1_C [TID_stm1_t1] [din, dout] rc.core_int_list)@
       (enumchan3 update__stm1_C [TID_stm1_t3] [din, dout] rc.core_int_list)
)
"

definition stm1_l_events where
"stm1_l_events = 
  set (enumchans1 [get_l_stm1_C, set_l_stm1_C] rc.core_int_list)
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

definition stm1_Memory_opt_l where
"stm1_Memory_opt_l = mem_of_lvar get_l_stm1 set_l_stm1 rc.core_int_set"

text \<open> Memory transition processes \<close>
definition stm1_MemoryTransitions_opt_0 where
"stm1_MemoryTransitions_opt_0 = 
  loop (\<lambda> id::integer. 
    (do {outp internal_stm1 TID_stm1_t0 ; Ret (id)} \<box>
     do {outp internal_stm1 TID_stm1_t4 ; Ret (id)} \<box> 
     do {outp reset__stm1 (TID_stm1_t2, din) ; Ret (id)}
    )
  )
"
(*
definition stm1_MemoryTransitions_opt_1 where
"stm1_MemoryTransitions_opt_1 = 
  loop (\<lambda> id::integer. 
    do {
      x \<leftarrow> inp_in get_x_stm1 rc.core_int_set ;
      (do {guard (x \<le> const_mod0_ctrl0_stm1_MAX); 
           inp_in update__stm1 (set [(TID_stm1_t1, din, x). x \<leftarrow> rc.core_int_list]) ; 
           Ret (id)} \<box> 
       do {guard (x \<ge> rc.Neg const_mod0_ctrl0_stm1_MAX rc.core_int_set); 
           inp_in update__stm1 (set [(TID_stm1_t3, din, x). x \<leftarrow> rc.core_int_list]) ; 
           Ret (id)}
      )
    }
  )
"
*)
definition stm1_MemoryTransitions_opt_1 where
"stm1_MemoryTransitions_opt_1 = 
  loop (\<lambda> id::integer. 
    do {
      (do {inp_in update__stm1 (set [(TID_stm1_t1, din, l). l \<leftarrow> rc.core_int_list, l \<le> const_mod0_ctrl0_stm1_MAX]) ; 
           Ret (id)} \<box> 
       do {inp_in update__stm1 (set [(TID_stm1_t3, din, l). l \<leftarrow> rc.core_int_list, 
           (l \<ge> rc.Neg const_mod0_ctrl0_stm1_MAX rc.core_int_set)]) ; 
           Ret (id)}
      )
    }
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
        (\<lambda> s. s \<notin> {NULLTRANSITION_stm1,TID_stm1_t1,TID_stm1_t2,TID_stm1_t3,TID_stm1_t4}) 
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
                do {t \<leftarrow> inp_in update__stm1 (set [(TID_stm1_t1, din, l) . l \<leftarrow> rc.core_int_list]) ;
                      outp set_l_stm1 (snd (snd t)) ; 
                      outp exit_stm1 (SID_stm1_s0, SID_stm1_s0);
                      outp exited_stm1 (SID_stm1_s0, SID_stm1_s0);
                      l \<leftarrow> inp_in get_l_stm1 rc.core_int_set ; 
                        \<comment> \<open> @{text \<open>outp set_x_stm1 (x+1);\<close>} \<close>
                        outp set_x_stm1 (rc.Plus l 1 rc.core_int_set);
                        outp enter_stm1 (SID_stm1_s0, SID_stm1_s0);
                        Ret(True, fst (snd s), SID_stm1_s0)
                    } \<box>
                \<comment> \<open> @{text T_stm1_t2} \<close>
                do {outp reset__stm1 (TID_stm1_t2, din);
                    outp exit_stm1 (SID_stm1_s0, SID_stm1_s0);
                    outp exited_stm1 (SID_stm1_s0, SID_stm1_s0);
                    outp set_x_stm1 0;
                    outp enter_stm1 (SID_stm1_s0, SID_stm1_s0);
                    Ret(True, fst (snd s), SID_stm1_s0)
                    } \<box>
                \<comment> \<open> @{text T_stm1_t3} \<close>
                do {t \<leftarrow> inp_in update__stm1 (set [(TID_stm1_t3, din, l) . l \<leftarrow> rc.core_int_list]) ;
                      outp set_l_stm1 (snd (snd t)) ; 
                      outp exit_stm1 (SID_stm1_s0, SID_stm1_s0);
                      outp exited_stm1 (SID_stm1_s0, SID_stm1_s0);
                      l \<leftarrow> inp_in get_l_stm1 rc.core_int_set ; 
                        \<comment> \<open> @{text \<open>outp set_x_stm1 (l-1);\<close>} \<close>
                        outp set_x_stm1 (rc.Minus l 1 rc.core_int_set);
                        outp enter_stm1 (SID_stm1_s0, SID_stm1_s0);
                        Ret(True, fst (snd s), SID_stm1_s0)
                    } \<box>
                \<comment> \<open> @{text T_stm1_t4} \<close>
                do {
                      outp internal_stm1 TID_stm1_t4;
                      outp exit_stm1 (SID_stm1_s0, SID_stm1_s0);
                      outp exited_stm1 (SID_stm1_s0, SID_stm1_s0);
                      x \<leftarrow> inp_in get_x_stm1 rc.core_int_set ; 
                      outp set_x_stm1 (rc.Neg x rc.core_int_set);
                      outp enter_stm1 (SID_stm1_s0, SID_stm1_s0);
                      Ret(True, fst (snd s), SID_stm1_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in internal_stm1(set tids_stm1_s0);
                    y \<leftarrow> inp_in exit_stm1 (set 
                      [(s, SID_stm1_s0) . s \<leftarrow> (removeAll SID_stm1_s0 SIDS_stm1_list)]);
                      outp exited_stm1 (fst y, SID_stm1_s0);
                      Ret (False, fst (snd s), SID_stm1_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in reset__stm1 (set [(s, d) . 
                        s \<leftarrow> tids_stm1_s0, 
                        d \<leftarrow> InOut_list]) ;
                    y \<leftarrow> inp_in exit_stm1 (set 
                        [(s, SID_stm1_s0) . s \<leftarrow> (removeAll SID_stm1_s0 SIDS_stm1_list)]);
                      outp exited_stm1 (fst y, SID_stm1_s0);
                      Ret (False, fst (snd s), SID_stm1_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in update__stm1 (set [(s, d, l) . 
                        s \<leftarrow> tids_stm1_s0, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> rc.core_int_list]) ;
                    y \<leftarrow> inp_in exit_stm1 (set 
                        [(s, SID_stm1_s0) . s \<leftarrow> (removeAll SID_stm1_s0 SIDS_stm1_list)]);
                      outp exited_stm1 (fst y, SID_stm1_s0);
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

definition stm1_opt_0_internal_set where
"stm1_opt_0_internal_set = 
   set ([internal_stm1_C TID_stm1_t0] @
        [internal_stm1_C TID_stm1_t4] @
       (enumchan2 reset__stm1_C [TID_stm1_t2] [din, dout])
)"

definition stm1_opt_1_internal_set where
"stm1_opt_1_internal_set = 
   set ((enumchan3 update__stm1_C [TID_stm1_t1] [din, dout] rc.core_int_list) @ 
      (enumchan3 update__stm1_C [TID_stm1_t3] [din, dout] rc.core_int_list)
)"

subsubsection \<open> State machine \<close>
definition MemorySTM_opt_stm1 where
"MemorySTM_opt_stm1 (idd::integer) = 
  (
    (
      (
        (
          (
            (
              (discard_state (stm1_Memory_opt_l 0))
              \<parallel>\<^bsub> stm1_l_events \<^esub>
              (
                (
                  (discard_state (stm1_Memory_opt_x 0))
                  \<parallel>\<^bsub> stm1_x_events \<^esub>
                  (STM_stm1 idd)
                ) \<setminus> (set [get_x_stm1_C n. n \<leftarrow> rc.core_int_list])
              )
            ) \<setminus> stm1_l_events
          ) 
          \<parallel>\<^bsub> stm1_opt_0_internal_set \<^esub>
          (discard_state (stm1_MemoryTransitions_opt_0 idd))
        ) \<setminus> {internal_stm1_C TID_stm1_t0, internal_stm1_C TID_stm1_t4}
      )
      \<parallel>\<^bsub> stm1_opt_1_internal_set \<^esub>
      (discard_state (stm1_MemoryTransitions_opt_1 idd))
    ) \<setminus> {}
  )
"

definition rename_stm1_events where
"rename_stm1_events = 
  concat ((enumchan1 (forget_first reset__stm1_C reset_stm1_C TIDS_stm1_list) InOut_list) @
  (enumchan2 (forget_first2 update__stm1_C update_stm1_C TIDS_stm1_list) InOut_list rc.core_int_list))
"

value "rename_stm1_events"

definition rename_stm1_events_others where
"rename_stm1_events_others = 
  (enumchanp1 terminate_stm1_C [()]) @
  (enumchansp1 [get_x_stm1_C, set_x_stm1_C, set_EXT_x_stm1_C] rc.core_int_list) @
  (enumchansp1 [reset_stm1_C] InOut_list) @
  (enumchansp2 [update_stm1_C] InOut_list rc.core_int_list) @
  (enumchansp2 [enter_stm1_C, entered_stm1_C, exit_stm1_C, exited_stm1_C] SIDS_stm1_list SIDS_stm1_list)
"

value "rename_stm1_events_others"
(* For this syntax to work, the types in a channel type must be enumerable. Here integer seems not to be enumerable. *)
value "\<lbrace>update__stm1 (t, d, x) \<mapsto> update_stm1 (d, x) | (t, d, x). d \<in> InOut_set \<and> x \<in> rc.core_int_set\<rbrace>"

(*
  How to rename this process to avoid deadlock (resolve nondeterminism in some ways) between two transitions
from s0 with overlapped guards and the same trigger?
Brain storms:
S1. Preprocess renaming map (which is a list of pairs in this example) to drop the later pairs whose 
range are the same as one of pair in the early (top) of the list.
- This doesn't work because each renaming map should be only applied to the initial events of the process.
so (a \<rightarrow> P \<box> b \<rightarrow> c \<rightarrow> Q) \<lbrace> (a, d), (c, d) \<rbrace> = (d \<rightarrow> P \<lbrace> (a, d), (c, d) \<rbrace>) \<box> (b \<rightarrow> d \<rightarrow> Q \<lbrace> (a, d), (c, d) \<rbrace>)

*)
definition rename_MemorySTM_opt_stm1 where
"rename_MemorySTM_opt_stm1 idd = 
  ((MemorySTM_opt_stm1 idd) \<lbrace>(set (rename_stm1_events @ rename_stm1_events_others))\<rbrace>)
"

definition rename_MemorySTM_opt_stm1' where
"rename_MemorySTM_opt_stm1' idd = 
  renamel (rename_stm1_events @ rename_stm1_events_others) (MemorySTM_opt_stm1 idd)
" 

definition AUX_opt_stm1 where
"AUX_opt_stm1 (idd::integer) = 
  ( 
    ( 
      (rename_MemorySTM_opt_stm1' idd) \<lbrakk> set [terminate_stm1_C ()] \<Zrres> skip
    ) \<setminus> stm1_MachineInternalEvents
  )
"

definition D__stm1 where
"D__stm1 (idd::integer) = 
  (AUX_opt_stm1 idd) \<setminus> internal_events_stm1
"

subsection \<open> Controller \label{ssec:basic_ctr0}\<close>
text \<open> A controller has a different channel type from those of state machines. Here, we declare a 
new channel type @{term Chan_ctr0} for @{text ctr0}. The events of @{text stm0} and @{text stm1} are 
renamed to the events in @{term Chan_ctr0}.

We note the event @{text e3} in the model is not an event of @{text ctr0}, and we introduce the 
event @{term update_ctr0} here to let the events @{term update_stm0} and @{term update_stm1} mapped to it.
By this way, @{term update_stm0} and @{term update_stm1} are linked.
\<close>

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
  rec_ctr0 :: "InOut \<times> core_int"
(* e2 of stm1 is mapped to it *)
  reset_ctr0 :: "InOut"
(* e3 of stm0 is mapped to update_ctr0.out and e3 of stm1 is mapped to update_ctr0.in *)
  update_ctr0 :: "InOut \<times> core_int"

definition shared_variable_events_ctr0 where
"shared_variable_events_ctr0 = 
  set (enumchan1 set_EXT_x_ctr0_C rc.core_int_list)"

subsubsection \<open> Memory \<close>
text \<open> The memory of @{text ctr0}, @{term Memory_ctr0}, relays the update of @{text x} 
from @{text mod0} to @{text stm0} and @{text stm1}.
We note that the update of @{text x} here introduces nondeterminism because it is possible that 
@{text x} in @{text stm0} has been updated, but @{text x} in @{text stm1} has not been updated.
The @{text "Ret (id)"} here passes the value of @{text id} to the next loop.
\<close>

definition Memory_ctr0 where
"Memory_ctr0 = loop (\<lambda> id::integer.
  ( do {x \<leftarrow> inp_in set_EXT_x_ctr0 rc.core_int_set; 
        outp set_EXT_x_ctr0_stm0 x; 
        outp set_EXT_x_ctr0_stm1 x; Ret (id)}
  )
)"

subsubsection \<open> Controller \<close>
text \<open>For @{term D__stm0}, its events are renamed to the corresponding events in @{term Chan_ctr0}. 
The renaming relation is defined in @{term rename_ctr0_stm0_events} where the event of 
@{term update_stm0_C} is renamed to that of @{term update_ctr0_C} with the same direction and value.
\<close>

definition rename_ctr0_stm0_events where
"rename_ctr0_stm0_events = 
  (enumchanp2_1 (terminate_stm0_C,terminate_ctr0_C) [()]) @
  (enumchansp2_1 [(set_x_stm0_C, set_x_ctr0_C), (get_x_stm0_C, get_x_ctr0_C), 
      (set_EXT_x_stm0_C, set_EXT_x_ctr0_stm0_C)] rc.core_int_list) @
  (enumchansp2_2 [(rec_stm0_C, rec_ctr0_C), (update_stm0_C, update_ctr0_C)] InOut_list rc.core_int_list)"

definition rename_D__stm0 where
"rename_D__stm0 idd = ((D__stm0 idd) \<lbrace>(set rename_ctr0_stm0_events)\<rbrace>)"

text \<open>For @{term D__stm1}, its events are also renamed to the corresponding events in @{term Chan_ctr0}. 
The renaming relation is defined in @{term rename_ctr0_stm1_events} where the event of 
@{term update_stm0_C} is renamed to that of @{term update_ctr0_C} with the opposite direction and the same 
value. By this way, we connect the output of @{text e3} in @{text stm0} to the input of @{text e3} 
in @{text stm1}.
\<close>
definition rename_ctr0_stm1_events where
"rename_ctr0_stm1_events = 
  (enumchanp2_1 (terminate_stm1_C,terminate_ctr0_C) [()]) @
  (enumchansp2_1 [(set_x_stm1_C, set_x_ctr0_C), (get_x_stm1_C, get_x_ctr0_C), 
      (set_EXT_x_stm1_C, set_EXT_x_ctr0_stm1_C)] rc.core_int_list) @
  (enumchansp2_1 [(reset_stm1_C, reset_ctr0_C)] InOut_list) @
\<comment> \<open>It is important to invert directions in one side: either stm0 or stm1 \<close>
  (enumchansp2_1 [((curry update_stm1_C) din, (curry update_ctr0_C) dout), 
      ((curry update_stm1_C) dout, (curry update_ctr0_C) din)] rc.core_int_list)
"

definition rename_D__stm1 where
"rename_D__stm1 idd = ((D__stm1 idd) \<lbrace>(set rename_ctr0_stm1_events)\<rbrace>)"

text \<open>The @{term ctr0_stms_events} below gives a set of synchronisation events between @{text stm0} 
and @{text stm1} which includes termination and @{text e3}.
\<close>
definition "ctr0_stms_events = set (
  enumchan1 terminate_ctr0_C [()] @
  enumchan2 update_ctr0_C InOut_list rc.core_int_list
)"

text \<open>The memory update events for @{text stm0} and @{text stm1} are defined in 
@{term ctr0_mem_events}. \<close>
definition "ctr0_mem_events = set (
  enumchans1 [set_EXT_x_ctr0_stm0_C, set_EXT_x_ctr0_stm1_C] rc.core_int_list
)"

text \<open>So the controller @{text ctr0} is the composition of the renamed @{text stm0}, the renamed 
@{text stm1}, and its memory with appropriate event hiding. \<close>
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

subsection \<open> Module \label{ssec:basic_mod0}\<close>
text \<open>Similar to the controller, a module also has a different channel type from that of the 
controller. Here, we declare a new channel type @{term Chan_mod0} for @{text mod0}. 
The events of @{text ctr0} are renamed to those of @{term Chan_mod0}.
\<close>
chantype Chan_mod0 =
(* terminates of ctr0 are mapped to it *)
  terminate_mod0 :: unit 
(* variable channels: set_x and get_x of stm0 and stm1 are mapped to these channels *)
  set_x_mod0 :: core_int
  get_x_mod0 :: core_int
(* shared variable channels *)
  set_EXT_x_mod0_ctr0 :: core_int
(* e1 of stm0 is mapped to it *)
  rec_mod0 :: "InOut \<times> core_int"
(* e2 of stm1 is mapped to it *)
  reset_mod0 :: "InOut"

subsubsection \<open> Memory \<close>
text \<open>The memory of @{text mod0} accepts an update to @{text x} and then propagates this update to 
the controller. Finally, the update will reach the all controllers and state machines 
that require @{text x}, such as @{text ctr0}, @{text stm0}, and @{text stm1} in this model.
\<close>
definition Memory_mod0 where
"Memory_mod0 = loop (\<lambda> id::integer.
  ( do {x \<leftarrow> inp_in set_x_mod0 rc.core_int_set; 
        outp set_EXT_x_mod0_ctr0 x; Ret (id)}
  )
)"

subsubsection \<open> Module \<close>
text \<open>The renaming relation from @{text ctr0} to @{text mod0}, defined by 
@{term rename_mod0_ctr0_events} is simple and straightforward.
\<close>
definition rename_mod0_ctr0_events where
"rename_mod0_ctr0_events = 
  (enumchanp2_1 (terminate_ctr0_C,terminate_mod0_C) [()]) @
  (enumchansp2_1 [(set_x_ctr0_C, set_x_mod0_C), (get_x_ctr0_C, get_x_mod0_C), 
      (set_EXT_x_ctr0_C, set_EXT_x_mod0_ctr0_C)] rc.core_int_list) @
  (enumchanp2_1 (reset_ctr0_C, reset_mod0_C) InOut_list) @
  (enumchanp2_2 (rec_ctr0_C, rec_mod0_C) InOut_list rc.core_int_list)
"

definition rename_D__ctr0 where
"rename_D__ctr0 idd = ((D__ctr0 idd) \<lbrace>(set rename_mod0_ctr0_events)\<rbrace>)"

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

text \<open>Finally, the module is a composition of the renamed @{text ctr0} and the memory of 
@{text mod0} with a possibility to terminate through the exception operator.
\<close>
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

text \<open>We can animate @{term D__mod0} in Isabelle/HOL by the @{term animate} command. This command 
only works on a customised version of Isabelle, based on Isabelle2021.
\<close>
definition "D_mod0_sim = D__mod0 0"
animate1 D_mod0_sim
 
subsection \<open> Export code \<close>
text \<open>We export various processes to Haskell. These processes can be animated with ghci. 
By this way, we can debug a process at the first place when it is defined. Actually, it is not 
mandatory to export code since we have supported the @{term animate} command. However, due to the 
fact that the command cannot work on a standard Isabelle, it is better to keep exporting code because 
this way works on both the standard Isabelle and the customised version.
\<close>
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
  rename_MemorySTM_opt_stm1
  rename_MemorySTM_opt_stm1'
  D__stm1
  rename_D__stm0
  rename_D__stm1
  D__ctr0
  rename_D__ctr0
  D__ctr_mem
  D__mod0
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
    Simulate.simulate (RoboChart_basic_v1.d_mod0 0);
\<close>

export_generated_files 
  \<open>code/RoboChart_basic_v1/Simulate.hs\<close>
  \<open>code/RoboChart_basic_v1/Main.hs\<close>

end
