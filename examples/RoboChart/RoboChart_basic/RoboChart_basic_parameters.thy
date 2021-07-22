section \<open> CSP Semantics of a very basic RoboChart model \<close>
text \<open> This theory aims for simulation of a trivial RoboChart model based on its CSP
 semantics. In this version, we use parametrisation for renaming of events.
\<close>

theory RoboChart_basic_parameters
  imports "../../ITree_RoboChart"
begin

subsection \<open> General definitions \<close>
definition "int_max = (1::integer)"
definition "int_min = (-1::integer)"

abbreviation "core_int_list \<equiv> 
  int2integer_list [(int_of_integer int_min)..(int_of_integer int_max)]"

abbreviation "core_int_set \<equiv> set core_int_list"

subsubsection \<open> stm0 \<close>
datatype SIDS_stm0 = SID_stm0
  | SID_stm0_s0

definition "SIDS_stm0_list = [SID_stm0, SID_stm0_s0]"
definition "SIDS_stm0_set = set SIDS_stm0_list"
definition "SIDS_stm0_without_s0 = (removeAll SID_stm0_s0 SIDS_stm0_list)"

datatype TIDS_stm0 = NULLTRANSITION_stm0
	              | TID_stm0_t0
	              | TID_stm0_t1
	              | TID_stm0_t2

definition "TIDS_stm0_list = [NULLTRANSITION_stm0, TID_stm0_t0, TID_stm0_t1, TID_stm0_t2]"
definition "TIDS_stm0_set = set TIDS_stm0_list"

definition "ITIDS_stm0_list = [TID_stm0_t1, TID_stm0_t2]"
definition "ITIDS_stm0 = set ITIDS_stm0_list"  

subsubsection \<open> stm1 \<close>

datatype SIDS_stm1 = SID_stm1
  | SID_stm1_s0

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

subsection \<open> Channel type\<close>
chantype Chan =
(* flow channels *)
  (* will be hidden *)
  internal_stm0 :: TIDS_stm0
  enteredV_stm0 :: SIDS_stm0
  enterV_stm0 :: SIDS_stm0 
  exitV_stm0  :: SIDS_stm0 
  exitedV_stm0 :: SIDS_stm0
  enter_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  entered_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  exit_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  exited_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  (* terminate_stm0 :: unit *) 
(* variable channels : the next 3 channels will be hidden *)
  get_l_stm0 :: core_int
  set_l_stm0 :: core_int
  (* get_x_stm0 :: core_int*)
(* this won't be hidden, and will be renamed to set_x_ctr0 *)
  (* set_x_stm0 :: core_int *)
(* shared variable channels, and will be renamed to set_EXT_x_ctr0_stm0 *)
(*  set_EXT_x_stm0 :: core_int *)
(* event channels *)
  (* will be renamed to e1_stm0 (may introduce nondeterminism) *)
  (* e1__stm0 :: "TIDS_stm0 \<times> InOut \<times> core_int" *)
  (* will be further renamed to e1_ctr0 *)
  (* e1_stm0 :: "InOut \<times> core_int" *)
  (* will be renamed to e3_ctr0.out *)
  (*e3__stm0 :: "TIDS_stm0 \<times> InOut \<times> core_int" *)
  (*e3_stm0 :: "InOut \<times> core_int"*)

(* flow channels *)
  internal_stm1 :: TIDS_stm1
  enteredV_stm1 :: SIDS_stm1
  enterV_stm1 :: SIDS_stm1 
  exitV_stm1  :: SIDS_stm1 
  exitedV_stm1 :: SIDS_stm1
  enter_stm1 :: "SIDS_stm1 \<times> SIDS_stm1"
  entered_stm1 :: "SIDS_stm1 \<times> SIDS_stm1"
  exit_stm1 :: "SIDS_stm1 \<times> SIDS_stm1"
  exited_stm1 :: "SIDS_stm1 \<times> SIDS_stm1"
  terminate_stm1 :: unit (* Is this right? *)
(* variable channels *)
  (* get_x_stm1 :: core_int *)
(* set_x_stm1 :: core_int *)
(* shared variable channels *)
(*  set_EXT_x_stm1 :: core_int *)
(* event channels *)
(*
  e2__stm1 :: "TIDS_stm1 \<times> InOut"
  e2_stm1 :: "InOut"
  e3__stm1 :: "TIDS_stm1 \<times> InOut \<times> core_int"
  e3_stm1 :: "InOut \<times> core_int"
*)

(* terminates of stm0 and stm1 are mapped to it *)
(*  terminate_ctr0 :: unit *)
(* variable channels: set_x and get_x of stm0 and stm1 are mapped to these channels *)
(*  set_x_ctr0 :: core_int
  get_x_ctr0 :: core_int *)
(* shared variable channels *)
  (* set_EXT_x_ctr0 :: core_int *)
(* set_EXT_x of stm0 is mapped to this *)
  set_EXT_x_ctr0_stm0 :: core_int
(* set_EXT_x of stm1 is mapped to this *)
  set_EXT_x_ctr0_stm1 :: core_int
(* e1 of stm0 is mapped to it *)
(*  e1_ctr0 :: "InOut \<times> core_int" *)
(* e2 of stm1 is mapped to it *)
(*  e2_ctr0 :: "InOut" *)
(* e3 of stm0 is mapped to e3_ctr0.out and e3 of stm1 is mapped to e3_ctr0.in *)
  e3_ctr0 :: "InOut \<times> core_int"

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

subsection \<open> stm0 \<close>
subsubsection \<open> Sets of events \<close>

definition internal_events_stm0 where
"internal_events_stm0 = 
  set ([enter_stm0_C (sid1, sid2). 
          sid1 \<leftarrow> SIDS_stm0_list, 
          sid2 \<leftarrow> SIDS_stm0_list] @
      [entered_stm0_C (sid1, sid2). 
          sid1 \<leftarrow> SIDS_stm0_list, 
          sid2 \<leftarrow> SIDS_stm0_list] @
      [exit_stm0_C (sid1, sid2). 
          sid1 \<leftarrow> SIDS_stm0_list, 
          sid2 \<leftarrow> SIDS_stm0_list] @
      [exited_stm0_C (sid1, sid2). 
          sid1 \<leftarrow> SIDS_stm0_list, 
          sid2 \<leftarrow> SIDS_stm0_list]
)"

(*
definition shared_variable_events_stm0 where
"shared_variable_events_stm0 = 
  set ([set_EXT_x_stm0_C (x). 
          x \<leftarrow> core_int_list]
)"

definition CS_stm0_s0_sync where
"CS_stm0_s0_sync = 
  set ([enter_stm0_C (sidx, sidy). 
          sidx \<leftarrow> [SID_stm0_s0], 
          sidy \<leftarrow> [SID_stm0_s0]] @
      [entered_stm0_C (sidx, sidy). 
          sidx \<leftarrow> [SID_stm0_s0], 
          sidy \<leftarrow> [SID_stm0_s0]] @
      [exit_stm0_C (sidx, sidy). 
          sidx \<leftarrow> [SID_stm0_s0], 
          sidy \<leftarrow> [SID_stm0_s0]] @
      [exited_stm0_C (sidx, sidy). 
          sidx \<leftarrow> [SID_stm0_s0], 
          sidy \<leftarrow> [SID_stm0_s0]] @
      [enter_stm0_C (sidy, sidx). 
          sidx \<leftarrow> [SID_stm0_s0], 
          sidy \<leftarrow> [SID_stm0_s0]] @
      [entered_stm0_C (sidy, sidx). 
          sidx \<leftarrow> [SID_stm0_s0], 
          sidy \<leftarrow> [SID_stm0_s0]] @
      [exit_stm0_C (sidy, sidx). 
          sidx \<leftarrow> [SID_stm0_s0], 
          sidy \<leftarrow> [SID_stm0_s0]] @
      [exited_stm0_C (sidy, sidx). 
          sidx \<leftarrow> [SID_stm0_s0], 
          sidy \<leftarrow> [SID_stm0_s0]]
)"
*)

definition stm0_l_events where
"stm0_l_events = 
    set (
        [get_l_stm0_C l . l \<leftarrow> core_int_list] @
        [set_l_stm0_C l . l \<leftarrow> core_int_list]
    )
"

definition stm0_MachineInternalEvents where
"stm0_MachineInternalEvents = 
  set ([internal_stm0_C t . t \<leftarrow> TIDS_stm0_list])
"

definition stm0_x_events_p where
"stm0_x_events_p (set_x) (get_x) (set_EXT_x) = 
    set (
        [build\<^bsub>set_x\<^esub> x . x \<leftarrow> core_int_list] @
        [build\<^bsub>get_x\<^esub> x . x \<leftarrow> core_int_list] @
        [build\<^bsub>set_EXT_x\<^esub> x . x \<leftarrow> core_int_list]
    )
"

definition int_int_stm0_p where
"int_int_stm0_p (e1_internal) (e3_internal) = 
  set ([build\<^bsub>e1_internal\<^esub> (tid, dir, n). 
          tid \<leftarrow> [TID_stm0_t1,TID_stm0_t2], 
          dir \<leftarrow> [din, dout], 
          n \<leftarrow> core_int_list] @ 
       [build\<^bsub>e3_internal\<^esub> (tid, dir, n). 
          tid \<leftarrow> [TID_stm0_t1,TID_stm0_t2], 
          dir \<leftarrow> [din, dout], 
          n \<leftarrow> core_int_list] @
       [internal_stm0_C (tid). 
          tid \<leftarrow> [TID_stm0_t1,TID_stm0_t2]]
)"

definition stm0_s0_triggers_p where
"stm0_s0_triggers_p (e1_internal) = 
  set ([build\<^bsub>e1_internal\<^esub> (tid, dir, n). 
          tid \<leftarrow> [TID_stm0_t1], 
          dir \<leftarrow> [din, dout], 
          n \<leftarrow> core_int_list] @
  [internal_stm0_C (tid). 
          tid \<leftarrow> [TID_stm0_t2]]
)
"

subsubsection \<open> State Machine Memory \<close>
text \<open> Memory cell processes \<close>

(* for the shared variable x *)
definition stm0_Memory_opt_x_p where
"stm0_Memory_opt_x_p (set_x) (get_x) (set_EXT_x) = 
  mem_of_svar get_x set_x set_EXT_x core_int_set"

(* for the local variable l *)
definition stm0_Memory_opt_l where
"stm0_Memory_opt_l = mem_of_lvar get_l_stm0 set_l_stm0 core_int_set"

text \<open> Memory transition processes \<close>
definition stm0_MemoryTransitions_opt_0 where
"stm0_MemoryTransitions_opt_0 = 
  loop (\<lambda> id::integer. 
    (do {outp internal_stm0 TID_stm0_t0 ; Ret (id)} \<box> deadlock)
  )
"

subsubsection \<open> States \<close>

definition tids_stm0_s0 where
" tids_stm0_s0 = 
    (filter 
        (\<lambda> s. s \<notin> {NULLTRANSITION_stm0,TID_stm0_t1,TID_stm0_t2}) 
        ITIDS_stm0_list)"


subsubsection \<open> State machine \<close>
definition I_stm0_i0_p where
"I_stm0_i0_p (idd::integer) (set_x) = (
  do {outp internal_stm0 TID_stm0_t0 ; 
      outp set_x 0; 
      outp enter_stm0 (SID_stm0, SID_stm0_s0);
      outp entered_stm0 (SID_stm0, SID_stm0_s0)
  })
"

(* We need an interrupt operator for during actions *) 
(* ::"integer \<Rightarrow> SIDS_stm0 \<Rightarrow> (Chan_stm0, SIDS_stm0) itree" *)
definition State_stm0_s0_p where 
"State_stm0_s0_p (terminate) (set_x) (get_x) (e1) (e1_internal) (e3) (e3_internal) (set_EXT_x) = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_stm0 (set 
          [(s, SID_stm0_s0) . s \<leftarrow> (removeAll SID_stm0_s0 SIDS_stm0_list)]) ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_stm0_s0_execute \<close>
        (while 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_stm0 (snd (snd s), SID_stm0_s0);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_stm0_t1 \<close>
                do {t \<leftarrow> inp_in e1_internal (set [(TID_stm0_t1, din, l) . l \<leftarrow> core_int_list]) ;
                      outp set_l_stm0 (snd (snd t)) ; 
                      outp exit_stm0 (SID_stm0_s0, SID_stm0_s0);
                      outp exited_stm0 (SID_stm0_s0, SID_stm0_s0);
                      l \<leftarrow> inp_in get_l_stm0 core_int_set ; 
                        outp set_x (l);
                        outp enter_stm0 (SID_stm0_s0, SID_stm0_s0);
                        Ret(True, fst (snd s), SID_stm0_s0)
                    } \<box>
                \<comment> \<open> T_stm0_t2 \<close>
                do {outp internal_stm0 TID_stm0_t2;
                    outp exit_stm0 (SID_stm0_s0, SID_stm0_s0);
                    outp exited_stm0 (SID_stm0_s0, SID_stm0_s0);
                      x \<leftarrow> inp_in get_x core_int_set ; 
                        \<comment> \<open>Here, NULLTRANSITION_stm0 actually is not necessary and just to make sure
                          e3 is well-typed. Alternatively, we can give two e3 events as parameters. 
                          one is of type (TIDS_stm0 \<times> InOut \<times> core_int}) and another is of type 
                          (InOut \<times> core_int})
                        \<close>
                        outp e3 (dout, x); 
                        outp enter_stm0 (SID_stm0_s0, SID_stm0_s0);
                        Ret(True, fst (snd s), SID_stm0_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in internal_stm0 (set tids_stm0_s0);
                    y \<leftarrow> inp_in exit_stm0 (set 
                      [(s, SID_stm0_s0) . s \<leftarrow> (removeAll SID_stm0_s0 SIDS_stm0_list)]);
                      outp exit_stm0 (fst y, SID_stm0_s0);
                      Ret (False, fst (snd s), SID_stm0_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in e1_internal (set [(s, d, l) . 
                        s \<leftarrow> tids_stm0_s0, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> core_int_list]) ;
                    y \<leftarrow> inp_in exit_stm0 (set 
                        [(s, SID_stm0_s0) . s \<leftarrow> (removeAll SID_stm0_s0 SIDS_stm0_list)]);
                      outp exit_stm0 (fst y, SID_stm0_s0);
                      Ret (False, fst (snd s), SID_stm0_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in e3_internal (set [(s, d, l) . 
                        s \<leftarrow> tids_stm0_s0, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> core_int_list]) ;
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

subsubsection \<open> Parametrised processes \<close>

term "internal_stm0"
term "internal_stm0_C"

\<comment> \<open> How to convert between a channel such as internal_stm0 and the corresponding function internal_stm0_C???
because int_int_stm0_p uses a function instead of a channel.
\<close>

term "e1__stm0"
term "match\<^bsub>internal_stm0\<^esub>"
term "build\<^bsub>e1__stm0\<^esub>"
term "match\<^bsub>e1__stm0\<^esub>"
term "build\<^bsub>e1_stm0\<^esub>"
term "match\<^bsub>e1_stm0\<^esub>"

\<comment> \<open>
Extend a channel type to another with transition ids, such as 
(@{text "TIDS_stm0 \<times> InOut \<times> integer \<Longrightarrow>\<^sub>\<triangle> Chan_stm0"}).
This is necessary because an event has more details about transitions inside a state machine, but 
the details are forgotten by renaming outside the state machine.
\<close>
definition extend_channel_tid_stm0 ::"('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> (TIDS_stm0 \<times> 'a \<Longrightarrow>\<^sub>\<triangle> 'b)" where
"extend_channel_tid_stm0 X = \<lparr> 
    prism_match = (\<lambda> s. case match\<^bsub>X\<^esub> s of Some x \<Rightarrow> Some (NULLTRANSITION_stm0, x) | _ \<Rightarrow> None)
  , prism_build = (\<lambda> v. build\<^bsub>X\<^esub> (snd v)) 
\<rparr>"

definition State_stm0_s0_R_p where
"State_stm0_s0_R_p (idd::integer) (terminate) (set_x) (get_x) (e1) (e1_internal) (e3) (e3_internal) (set_EXT_x) = 
   (discard_state (State_stm0_s0_p (terminate) (set_x) (get_x) (e1) (e1_internal) (e3) (e3_internal) (set_EXT_x) idd )) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> ((int_int_stm0_p (e1_internal) (e3_internal)) - stm0_s0_triggers_p (e1_internal)) \<^esub> 
   skip
"
definition STM_stm0_p where
"STM_stm0_p (idd::integer) (terminate) (set_x) (get_x) (e1) (e1_internal) (e3) (e3_internal) (set_EXT_x) = 
   (I_stm0_i0_p idd set_x)
    \<parallel>\<^bsub> set (
        [enter_stm0_C (s, d). 
          s \<leftarrow> SIDS_stm0_without_s0, 
          d \<leftarrow> [SID_stm0_s0]] @ 
        [entered_stm0_C (s, d). 
          s \<leftarrow> SIDS_stm0_without_s0, 
          d \<leftarrow> [SID_stm0_s0]] @ 
        [exit_stm0_C (s, d). 
          s \<leftarrow> SIDS_stm0_without_s0, 
          d \<leftarrow> [SID_stm0_s0]] @ 
        [exited_stm0_C (s, d). 
          s \<leftarrow> SIDS_stm0_without_s0, 
          d \<leftarrow> [SID_stm0_s0]] 
        ) \<^esub> 
   (State_stm0_s0_R_p (idd) (terminate) (set_x) (get_x) (e1) (e1_internal) (e3) (e3_internal) (set_EXT_x))
"

definition stm0_e1_x_internal_set_p where
"stm0_e1_x_internal_set_p (set_x) (e1_internal) = 
  set ([build\<^bsub>e1_internal\<^esub> (tid, dir, n). 
          tid \<leftarrow> [TID_stm0_t1], 
          dir \<leftarrow> [din, dout], 
          n \<leftarrow> core_int_list] @ 
       [internal_stm0_C TID_stm0_t2] @
       [build\<^bsub>set_x\<^esub> n. n \<leftarrow> core_int_list]
)"

definition stm0_MemoryTransitions_opt_1_p where
"stm0_MemoryTransitions_opt_1_p (set_x) (get_x) (e1_internal)  (set_EXT_x) = 
  loop (\<lambda> id::integer.
    do {x \<leftarrow> inp_in get_x core_int_set ; 
      (
        do {inp_in e1_internal (set [(TID_stm0_t1, din, l). l \<leftarrow> core_int_list, (x = 0)])
              ; Ret (id)} \<box>
        do {guard (x \<noteq> 0); outp internal_stm0 TID_stm0_t2 ; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_x core_int_set; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_EXT_x core_int_set; Ret (id)}
      )
    }
  )
"

definition MemorySTM_opt_stm0_p where
"MemorySTM_opt_stm0_p (idd::integer) (terminate) (set_x) (get_x) (e1) (e1_internal) (e3) (e3_internal) (set_EXT_x) = 
  (hide
    (
      (discard_state (stm0_Memory_opt_x_p set_x get_x set_EXT_x 0))
      \<parallel>\<^bsub> stm0_x_events_p set_x get_x set_EXT_x \<^esub>
      (hide 
        (
          (par_hide
            (par_hide 
              (discard_state (stm0_Memory_opt_l idd)) 
              stm0_l_events 
              (STM_stm0_p idd (terminate) (set_x) (get_x) (e1) (e1_internal) (e3) (e3_internal) (set_EXT_x)))
            {internal_stm0_C TID_stm0_t0}
            (discard_state (stm0_MemoryTransitions_opt_0 idd))
          )
          \<parallel>\<^bsub> stm0_e1_x_internal_set_p set_x e1_internal \<^esub> 
          (discard_state (stm0_MemoryTransitions_opt_1_p (set_x) (get_x) (e1_internal) (set_EXT_x) idd))
        )
        {internal_stm0_C TID_stm0_t2}
      )
    )
    (set [build\<^bsub>get_x\<^esub> n. n \<leftarrow> core_int_list])
  )   
"

definition AUX_opt_stm0_p where
"AUX_opt_stm0_p (idd::integer) (terminate) (set_x) (get_x) (e1) (e3) (set_EXT_x) = 
  (hide 
    ( 
      (MemorySTM_opt_stm0_p idd (terminate) (set_x) (get_x) e1 (extend_channel_tid_stm0 e1) e3 (extend_channel_tid_stm0 e3) (set_EXT_x)) 
      \<lbrakk> set [build\<^bsub>terminate\<^esub> ()] \<Zrres> skip
    )
    stm0_MachineInternalEvents
  )
"

definition D__stm0_p where
"D__stm0_p (idd::integer)  (terminate) (set_x) (get_x) (e1) (e3) (set_EXT_x) = 
  hide (AUX_opt_stm0_p idd (terminate) (set_x) (get_x) (e1) (e3) (set_EXT_x)) internal_events_stm0
"

subsection \<open> stm1 \<close>

subsubsection \<open> Sets of events \<close>
definition int_int_stm1_p where
"int_int_stm1_p (e2_internal) (e3_internal)  = 
  set ([build\<^bsub>e2_internal\<^esub> (tid, dir). 
          tid \<leftarrow> [TID_stm1_t1,TID_stm1_t2], 
          dir \<leftarrow> [din, dout]] @ 
       [build\<^bsub>e3_internal\<^esub> (tid, dir, n). 
          tid \<leftarrow> [TID_stm1_t1,TID_stm1_t2], 
          dir \<leftarrow> [din, dout], 
          n \<leftarrow> core_int_list] @
       [internal_stm1_C (tid). 
          tid \<leftarrow> [TID_stm1_t1,TID_stm1_t2]]
)"

definition internal_events_stm1 where
"internal_events_stm1 = 
  set ([enter_stm1_C (sid1, sid2). 
          sid1 \<leftarrow> SIDS_stm1_list, 
          sid2 \<leftarrow> SIDS_stm1_list] @
      [entered_stm1_C (sid1, sid2). 
          sid1 \<leftarrow> SIDS_stm1_list, 
          sid2 \<leftarrow> SIDS_stm1_list] @
      [exit_stm1_C (sid1, sid2). 
          sid1 \<leftarrow> SIDS_stm1_list, 
          sid2 \<leftarrow> SIDS_stm1_list] @
      [exited_stm1_C (sid1, sid2). 
          sid1 \<leftarrow> SIDS_stm1_list, 
          sid2 \<leftarrow> SIDS_stm1_list]
)"

definition stm1_s0_triggers_p where
"stm1_s0_triggers_p (e2_internal) (e3_internal) = 
  set ([build\<^bsub>e2_internal\<^esub> (tid, dir). 
          tid \<leftarrow> [TID_stm1_t2], 
          dir \<leftarrow> [din, dout]] @
  [build\<^bsub>e3_internal\<^esub> (tid, dir, n). 
          tid \<leftarrow> [TID_stm1_t1], 
          dir \<leftarrow> [din, dout],
          n \<leftarrow> core_int_list]
)
"

definition stm1_x_events_p where
"stm1_x_events_p (set_x) (get_x) = 
    set (
        [build\<^bsub>get_x\<^esub> x . x \<leftarrow> core_int_list] @
        [build\<^bsub>set_x\<^esub> x . x \<leftarrow> core_int_list]
    )
"

definition stm1_e1_x_internal_set_p where
"stm1_e1_x_internal_set_p (e2_internal) (e3_internal) = 
  set ([build\<^bsub>e3_internal\<^esub> (tid, dir, n). 
          tid \<leftarrow> [TID_stm1_t1], 
          dir \<leftarrow> [din, dout], 
          n \<leftarrow> core_int_list] @ 
       [internal_stm1_C TID_stm1_t0] @
       [build\<^bsub>e2_internal\<^esub> (tid, dir). 
          tid \<leftarrow> [TID_stm1_t2], 
          dir \<leftarrow> [din, dout]]
)"
definition stm1_MachineInternalEvents where
"stm1_MachineInternalEvents = 
  set ([internal_stm1_C t . t \<leftarrow> TIDS_stm1_list])
"

subsubsection \<open> State Machine Memory \<close>
text \<open> Memory cell processes \<close>
(* for the shared variable x *)
definition stm1_Memory_opt_x_p where
"stm1_Memory_opt_x_p (set_x) (get_x) (set_EXT_x) = 
  mem_of_svar get_x set_x set_EXT_x core_int_set"

definition stm1_MemoryTransitions_opt_0_p where
"stm1_MemoryTransitions_opt_0_p e2_internal e3_internal = 
  loop (\<lambda> id::integer. 
    (do {outp internal_stm1 TID_stm1_t0 ; Ret (id)} \<box> 
     do {outp e2_internal (TID_stm1_t2, din) ; Ret (id)} \<box> 
     do {inp_in e3_internal (set [(TID_stm1_t1, din, x). x \<leftarrow> core_int_list]) ; Ret (id)}
    )
  )
"

text \<open> Memory transition processes \<close>

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


definition State_stm1_s0_p where 
"State_stm1_s0_p (terminate) (set_x) (get_x) (e2) (e2_internal) (e3) (e3_internal) (set_EXT_x) = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_stm1 (set 
          [(s, SID_stm1_s0) . s \<leftarrow> (removeAll SID_stm1_s0 SIDS_stm1_list)]) ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_stm1_s0_execute \<close>
        (while 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_stm1 (snd (snd s), SID_stm1_s0);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_stm1_t1 \<close>
                do {t \<leftarrow> inp_in e3_internal (set [(TID_stm1_t1, din, l) . l \<leftarrow> core_int_list]) ;
                      outp set_x (snd (snd t)) ; 
                      outp exit_stm1 (SID_stm1_s0, SID_stm1_s0);
                      outp exited_stm1 (SID_stm1_s0, SID_stm1_s0);
                      x \<leftarrow> inp_in get_x core_int_set ; 
                        outp set_x (x+1);
                        outp enter_stm1 (SID_stm1_s0, SID_stm1_s0);
                        Ret(True, fst (snd s), SID_stm1_s0)
                    } \<box>
                \<comment> \<open> T_stm1_t2 \<close>
                do {outp e2_internal (TID_stm1_t2, din);
                    outp exit_stm1 (SID_stm1_s0, SID_stm1_s0);
                    outp exited_stm1 (SID_stm1_s0, SID_stm1_s0);
                    outp set_x 0;
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
                    x \<leftarrow> inp_in e2_internal (set [(s, d) . 
                        s \<leftarrow> tids_stm1_s0, 
                        d \<leftarrow> InOut_list]) ;
                    y \<leftarrow> inp_in exit_stm1 (set 
                        [(s, SID_stm1_s0) . s \<leftarrow> (removeAll SID_stm1_s0 SIDS_stm1_list)]);
                      outp exit_stm1 (fst y, SID_stm1_s0);
                      Ret (False, fst (snd s), SID_stm1_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in e3_internal (set [(s, d, l) . 
                        s \<leftarrow> tids_stm1_s0, 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> core_int_list]) ;
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

definition State_stm1_s0_R_p where
"State_stm1_s0_R_p (idd::integer) (terminate) (set_x) (get_x) (e2) (e2_internal) (e3) (e3_internal) (set_EXT_x) = 
   (discard_state (State_stm1_s0_p (terminate) (set_x) (get_x) (e2) (e2_internal) (e3) (e3_internal) (set_EXT_x) idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_stm1_p e2_internal e3_internal - stm1_s0_triggers_p e2_internal e3_internal) \<^esub> 
   skip
"

subsubsection \<open> State machine \<close>

definition STM_stm1_p where
"STM_stm1_p (idd::integer) (terminate) (set_x) (get_x) (e2) (e2_internal) (e3) (e3_internal) (set_EXT_x) = 
   (I_stm1_i0 (idd))
    \<parallel>\<^bsub> set (
        [enter_stm1_C (s, d). 
          s \<leftarrow> SIDS_stm1_without_s0, 
          d \<leftarrow> [SID_stm1_s0]] @ 
        [entered_stm1_C (s, d). 
          s \<leftarrow> SIDS_stm1_without_s0, 
          d \<leftarrow> [SID_stm1_s0]] @ 
        [exit_stm1_C (s, d). 
          s \<leftarrow> SIDS_stm1_without_s0, 
          d \<leftarrow> [SID_stm1_s0]] @ 
        [exited_stm1_C (s, d). 
          s \<leftarrow> SIDS_stm1_without_s0, 
          d \<leftarrow> [SID_stm1_s0]] 
        ) \<^esub> 
   State_stm1_s0_R_p (idd) (terminate) (set_x) (get_x) (e2) (e2_internal) (e3) (e3_internal) (set_EXT_x)
"

definition MemorySTM_opt_stm1_p where
"MemorySTM_opt_stm1_p (idd::integer) (terminate) (set_x) (get_x) (e2) (e2_internal) (e3) (e3_internal) (set_EXT_x) = 
  (hide
    (
      (hide
        (
          (discard_state (stm1_Memory_opt_x_p (set_x) (get_x) (set_EXT_x) 0))
          \<parallel>\<^bsub> stm1_x_events_p (set_x) (get_x) \<^esub>
          (STM_stm1_p idd (terminate) (set_x) (get_x) (e2) (e2_internal) (e3) (e3_internal) (set_EXT_x))
        )
        (set [build\<^bsub>get_x\<^esub> n. n \<leftarrow> core_int_list])
      )
      \<parallel>\<^bsub> stm1_e1_x_internal_set_p (e2_internal) (e3_internal)\<^esub>
      (discard_state (stm1_MemoryTransitions_opt_0_p e2_internal e3_internal idd))
    )
    {internal_stm1_C TID_stm1_t0}
  )
"

subsubsection \<open> Parametrised processes \<close>

definition extend_channel_tid_stm1 ::"('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> (TIDS_stm1 \<times> 'a \<Longrightarrow>\<^sub>\<triangle> 'b)" where
"extend_channel_tid_stm1 X = \<lparr> 
    prism_match = (\<lambda> s. case match\<^bsub>X\<^esub> s of Some x \<Rightarrow> Some (NULLTRANSITION_stm1, x) | _ \<Rightarrow> None)
  , prism_build = (\<lambda> v. build\<^bsub>X\<^esub> (snd v)) 
\<rparr>"

definition AUX_opt_stm1_p where
"AUX_opt_stm1_p (idd::integer) (terminate) (set_x) (get_x) (e2) (e3) (set_EXT_x) = 
  (hide 
    ( 
      (MemorySTM_opt_stm1_p idd (terminate) (set_x) (get_x) (e2) (extend_channel_tid_stm1 e2) (e3) (extend_channel_tid_stm1 e3) (set_EXT_x)) 
      \<lbrakk> set [build\<^bsub>terminate\<^esub> ()] \<Zrres> skip
    )
    stm1_MachineInternalEvents
  )
"

definition D__stm1_p where
"D__stm1_p (idd::integer)  (terminate) (set_x) (get_x) (e2) (e3) (set_EXT_x) = 
  hide (AUX_opt_stm1_p idd (terminate) (set_x) (get_x) (e2) (e3) (set_EXT_x)) internal_events_stm1
"

subsection \<open> Controller \<close>

subsubsection \<open> Memory \<close>
definition Memory_ctr0_p where
"Memory_ctr0_p set_EXT_x = loop (\<lambda> id::integer.
  ( do {x \<leftarrow> inp_in set_EXT_x core_int_set; 
        outp set_EXT_x_ctr0_stm0 x; 
        outp set_EXT_x_ctr0_stm1 x; Ret (id)}
  )
)"

subsubsection \<open> Controller \<close>

definition "ctr0_stms_events_p terminate = set (
  [build\<^bsub>terminate\<^esub> ()] @ 
    [e3_ctr0_C (d, n). d \<leftarrow> InOut_list, n \<leftarrow> core_int_list]
)"

definition "ctr0_mem_events = set (
    [set_EXT_x_ctr0_stm0_C x. x \<leftarrow> core_int_list] @ 
    [set_EXT_x_ctr0_stm1_C x. x \<leftarrow> core_int_list]
)"

\<comment> \<open>How to link e3.in of stm1 to e3.out of stm0, and vice versa?\<close>
definition D__ctr0_p where
"D__ctr0_p (idd::integer) (terminate) (set_x) (get_x) (e1) (e2) (set_EXT_x)
 = 
  (par_hide
    (hide 
      ((D__stm0_p idd terminate set_x get_x e1 e3_ctr0 set_EXT_x_ctr0_stm0) 
        \<parallel>\<^bsub> ctr0_stms_events_p terminate \<^esub> 
       (D__stm1_p idd terminate set_x get_x e2 e3_ctr0 set_EXT_x_ctr0_stm1))
      (ctr0_stms_events_p terminate - set [build\<^bsub>terminate\<^esub> ()])
    )
    ctr0_mem_events
    (discard_state (Memory_ctr0_p set_EXT_x idd))
  )  \<lbrakk> set [build\<^bsub>terminate\<^esub> ()] \<Zrres> skip
"


subsection \<open> Module \<close>
definition Memory_mod0 where
"Memory_mod0 = loop (\<lambda> id::integer.
  ( do {x \<leftarrow> inp_in set_x_mod0 core_int_set; 
        outp set_EXT_x_mod0_ctr0 x; Ret (id)}
  )
)"

(*
definition rename_mod0_ctr0_events where
"rename_mod0_ctr0_events = 
  [(terminate_ctr0_C (), terminate_mod0_C ())] @
  [(set_x_ctr0_C n, set_x_mod0_C n). n \<leftarrow> core_int_list] @
  [(get_x_ctr0_C n, get_x_mod0_C n). n \<leftarrow> core_int_list] @
  [(e1_ctr0_C (d, n), e1_mod0_C (d, n)). d \<leftarrow> InOut_list, n \<leftarrow> core_int_list] @
  [(e2_ctr0_C (d), e2_mod0_C (d)). d \<leftarrow> InOut_list] @
  [(set_EXT_x_ctr0_C (n), set_EXT_x_mod0_ctr0_C (n)). n \<leftarrow> core_int_list]
"
*)

definition "mod0_set_x_events = set (
  [set_x_mod0_C n. n \<leftarrow> core_int_list]
)"

definition "mod0_get_x_events = set (
  [get_x_mod0_C n. n \<leftarrow> core_int_list]
)"

definition "mod0_set_EXT_x_events = set (
  [set_EXT_x_mod0_ctr0_C n. n \<leftarrow> core_int_list]
)"

definition D__mod0_p where
"D__mod0_p (idd::integer) = 
  (hide
    (
      (skip \<parallel>\<^bsub> {} \<^esub> 
        (
          hide 
            (
              (D__ctr0_p idd (terminate_mod0) (set_x_mod0) (get_x_mod0) (e1_mod0) (e2_mod0) (set_EXT_x_mod0_ctr0)) 
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
  stm0_Memory_opt_l
  stm0_MemoryTransitions_opt_0
  stm0_MemoryTransitions_opt_1_p
  I_stm0_i0_p
  State_stm0_s0_p
  State_stm0_s0_R_p
  STM_stm0_p
  MemorySTM_opt_stm0_p
  D__stm0_p
  stm1_Memory_opt_x_p
  stm1_MemoryTransitions_opt_0_p
  I_stm1_i0
  State_stm1_s0_p
  State_stm1_s0_R_p
  STM_stm1_p
  MemorySTM_opt_stm1_p
  D__stm1_p
  D__mod0_p
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
       if (n >= 20) then do { Prelude.putStr "Many steps (> 20); Continue? [Y/N]"; q <- Prelude.getLine;
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