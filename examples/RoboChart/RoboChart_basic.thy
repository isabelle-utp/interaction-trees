section \<open> A very basic RoboChart CSP Semantics \<close>

theory RoboChart_basic
  imports "../../ITree_RoboChart"
begin

subsection \<open> General definitions \<close>
definition "int_max = (1::integer)"
definition "int_min = (-1::integer)"

abbreviation "core_int_list \<equiv> 
  int2integer_list [(int_of_integer int_min)..(int_of_integer int_max)]"

abbreviation "core_int_set \<equiv> set core_int_list"

subsection \<open> stm0 \<close>
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

chantype Chan_stm0 =
(* flow channels *)
  internal_stm0 :: TIDS_stm0
  enteredV_stm0 :: SIDS_stm0
  enterV_stm0 :: SIDS_stm0 
  exitV_stm0  :: SIDS_stm0 
  exitedV_stm0 :: SIDS_stm0
  enter_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  entered_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  exit_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  exited_stm0 :: "SIDS_stm0 \<times> SIDS_stm0"
  terminate_stm0 :: unit (* Is this right? *)
(* variable channels *)
  get_l_stm0 :: core_int
  set_l_stm0 :: core_int
  get_x_stm0 :: core_int
  set_x_stm0 :: core_int
(* shared variable channels *)
  set_EXT_x_stm0 :: core_int
(* event channels *)
  e1__stm0 :: "TIDS_stm0 \<times> InOut \<times> core_int"
  e1_stm0 :: "InOut \<times> core_int"
  e3__stm0 :: "TIDS_stm0 \<times> InOut \<times> core_int"
  e3_stm0 :: "InOut \<times> core_int"

subsubsection \<open> Sets of events \<close>
definition int_int_stm0 where
"int_int_stm0 = 
  set ([e1__stm0_C (tid, dir, n). 
          tid \<leftarrow> [TID_stm0_t1,TID_stm0_t2], 
          dir \<leftarrow> [din, dout], 
          n \<leftarrow> core_int_list] @ 
       [e3__stm0_C (tid, dir, n). 
          tid \<leftarrow> [TID_stm0_t1,TID_stm0_t2], 
          dir \<leftarrow> [din, dout], 
          n \<leftarrow> core_int_list] @
       [internal_stm0_C (tid). 
          tid \<leftarrow> [TID_stm0_t1,TID_stm0_t2]]
)"

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

definition stm0_s0_triggers where
"stm0_s0_triggers = 
  set ([e1__stm0_C (tid, dir, n). 
          tid \<leftarrow> [TID_stm0_t1], 
          dir \<leftarrow> [din, dout], 
          n \<leftarrow> core_int_list] @
  [internal_stm0_C (tid). 
          tid \<leftarrow> [TID_stm0_t2]]
)
"

definition stm0_l_events where
"stm0_l_events = 
    set (
        [get_l_stm0_C l . l \<leftarrow> core_int_list] @
        [set_l_stm0_C l . l \<leftarrow> core_int_list]
    )
"

definition stm0_x_events where
"stm0_x_events = 
    set (
        [get_x_stm0_C x . x \<leftarrow> core_int_list] @
        [set_x_stm0_C x . x \<leftarrow> core_int_list] @
        [set_EXT_x_stm0_C x . x \<leftarrow> core_int_list]
    )
"

definition stm0_MachineInternalEvents where
"stm0_MachineInternalEvents = 
  set ([internal_stm0_C t . t \<leftarrow> TIDS_stm0_list])
"

subsubsection \<open> State Machine Memory \<close>
text \<open> Memory cell processes \<close>

(* for the shared variable x *)
definition stm0_Memory_opt_x where
"stm0_Memory_opt_x = 
  mem_of_svar get_x_stm0 set_x_stm0 set_EXT_x_stm0 core_int_set"

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

definition stm0_MemoryTransitions_opt_1 where
"stm0_MemoryTransitions_opt_1 = 
  loop (\<lambda> id::integer.
    do {x \<leftarrow> inp_in get_x_stm0 core_int_set ; 
      (
        do {inp_in e1__stm0 (set [(TID_stm0_t1, din, l). l \<leftarrow> core_int_list, (x = 0)])
              ; Ret (id)} \<box>
        do {guard (x \<noteq> 0); outp internal_stm0 TID_stm0_t2 ; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_x_stm0 core_int_set; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_EXT_x_stm0 core_int_set; Ret (id)}
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

term "do {skip ; stop} \<triangle> skip"
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
                do {t \<leftarrow> inp_in e1__stm0 (set [(TID_stm0_t1, din, l) . l \<leftarrow> core_int_list]) ;
                      outp set_l_stm0 (snd (snd t)) ; 
                      outp exit_stm0 (SID_stm0_s0, SID_stm0_s0);
                      outp exited_stm0 (SID_stm0_s0, SID_stm0_s0);
                      l \<leftarrow> inp_in get_l_stm0 core_int_set ; 
                        outp set_x_stm0 (l);
                        outp enter_stm0 (SID_stm0_s0, SID_stm0_s0);
                        Ret(True, fst (snd s), SID_stm0_s0)
                    } \<box>
                \<comment> \<open> T_stm0_t2 \<close>
                do {outp internal_stm0 TID_stm0_t2;
                    outp exit_stm0 (SID_stm0_s0, SID_stm0_s0);
                    outp exited_stm0 (SID_stm0_s0, SID_stm0_s0);
                      x \<leftarrow> inp_in get_x_stm0 core_int_set ; 
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
                        l \<leftarrow> core_int_list]) ;
                    y \<leftarrow> inp_in exit_stm0 (set 
                        [(s, SID_stm0_s0) . s \<leftarrow> (removeAll SID_stm0_s0 SIDS_stm0_list)]);
                      outp exit_stm0 (fst y, SID_stm0_s0);
                      Ret (False, fst (snd s), SID_stm0_s0)
                    } \<box>
                do {
                    x \<leftarrow> inp_in e3__stm0 (set [(s, d, l) . 
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

definition State_stm0_s0_R where
"State_stm0_s0_R (idd::integer) = 
   (discard_state (State_stm0_s0 idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_stm0 - stm0_s0_triggers) \<^esub> 
   skip
"

definition STM_stm0 where
"STM_stm0 (idd::integer) = 
   (I_stm0_i0(idd))
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
   State_stm0_s0_R(idd)
"

definition stm0_e1_x_internal_set where
"stm0_e1_x_internal_set = 
  set ([e1__stm0_C (tid, dir, n). 
          tid \<leftarrow> [TID_stm0_t1], 
          dir \<leftarrow> [din, dout], 
          n \<leftarrow> core_int_list] @ 
       [internal_stm0_C TID_stm0_t2] @
       [set_x_stm0_C n. n \<leftarrow> core_int_list]
)"

(*
(Memory_opt_x(0)
 [| {|set_EXT_x,get_x,set_x|} |] 
 (
  (	
   (
     ((Memory_opt_l(0) [| {|get_l,set_l|} |] STM_core(id__))\ {|get_l,set_l|})
     [| {|internal__.TID_stm0_t0|} |]
     MemoryTransitions_opt_0(id__)
   ) \ {|internal__.TID_stm0_t0|}
  )
  [| {|e1__.TID_stm0_t1,internal__.TID_stm0_t2,set_x|} |]
  MemoryTransitions_opt_1(id__)
 )\{|internal__.TID_stm0_t2|}
) \ {|get_x|}
*)

subsubsection \<open> State machine \<close>
definition MemorySTM_opt_stm0 where
"MemorySTM_opt_stm0 (idd::integer) = 
  (hide
    (
      (discard_state (stm0_Memory_opt_x idd))
      \<parallel>\<^bsub> stm0_x_events \<^esub>
      (hide 
        (
          (par_hide
            (par_hide (discard_state (stm0_Memory_opt_l idd)) stm0_l_events (STM_stm0 idd))
            {internal_stm0_C TID_stm0_t0}
            (discard_state (stm0_MemoryTransitions_opt_0 idd))
          )
          \<parallel>\<^bsub> stm0_e1_x_internal_set \<^esub> 
          (discard_state (stm0_MemoryTransitions_opt_1 idd))
        )
        {internal_stm0_C TID_stm0_t2}
      )
    )
    (set [get_x_stm0_C n. n \<leftarrow> core_int_list])
  )   
"

term "(MemorySTM_opt_stm0 idd)"

definition rename_stm0_events :: "Chan_stm0 \<Rightarrow> Chan_stm0" where
(*"rename_stm0_events (e1__stm0_C (tid, dir, c)) = e1_stm0_C (dir, c)" | 
"rename_stm0_events (e3__stm0_C (tid, dir, c)) = e3_stm0_C (dir, c)" | *)
"rename_stm0_events e = e"

definition rename_MemorySTM_opt_stm0 where
"rename_MemorySTM_opt_stm0 idd = 
  rename rename_stm0_events (MemorySTM_opt_stm0 idd)
"

term "map_pfun"

(* Exception: P [| A |> Q*)
(* Renaming *)
definition AUX_opt_stm0 where
"AUX_opt_stm0 (idd::integer) = 
  (hide 
    ( 
      (rename_MemorySTM_opt_stm0 idd) \<lbrakk> set [terminate_stm0_C ()] \<Zrres> skip
    )
    stm0_MachineInternalEvents
  )
"

definition D__stm0 where
"D__stm0 (idd::integer) = 
  hide (AUX_opt_stm0 idd) internal_events_stm0
"

subsection \<open> stm1 \<close>

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

chantype Chan_stm1 =
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
  set ([e2__stm1_C (tid, dir). 
          tid \<leftarrow> [TID_stm1_t1,TID_stm1_t2], 
          dir \<leftarrow> [din, dout]] @ 
       [e3__stm1_C (tid, dir, n). 
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

definition shared_variable_events_stm1 where
"shared_variable_events_stm1 = 
  set ([set_EXT_x_stm1_C (x). 
          x \<leftarrow> core_int_list]
)"

definition CS_stm1_s0_sync where
"CS_stm1_s0_sync = 
  set ([enter_stm1_C (sidx, sidy). 
          sidx \<leftarrow> [SID_stm1_s0], 
          sidy \<leftarrow> [SID_stm1_s0]] @
      [entered_stm1_C (sidx, sidy). 
          sidx \<leftarrow> [SID_stm1_s0], 
          sidy \<leftarrow> [SID_stm1_s0]] @
      [exit_stm1_C (sidx, sidy). 
          sidx \<leftarrow> [SID_stm1_s0], 
          sidy \<leftarrow> [SID_stm1_s0]] @
      [exited_stm1_C (sidx, sidy). 
          sidx \<leftarrow> [SID_stm1_s0], 
          sidy \<leftarrow> [SID_stm1_s0]] @
      [enter_stm1_C (sidy, sidx). 
          sidx \<leftarrow> [SID_stm1_s0], 
          sidy \<leftarrow> [SID_stm1_s0]] @
      [entered_stm1_C (sidy, sidx). 
          sidx \<leftarrow> [SID_stm1_s0], 
          sidy \<leftarrow> [SID_stm1_s0]] @
      [exit_stm1_C (sidy, sidx). 
          sidx \<leftarrow> [SID_stm1_s0], 
          sidy \<leftarrow> [SID_stm1_s0]] @
      [exited_stm1_C (sidy, sidx). 
          sidx \<leftarrow> [SID_stm1_s0], 
          sidy \<leftarrow> [SID_stm1_s0]]
)"

definition stm1_s0_triggers where
"stm1_s0_triggers = 
  set ([e2__stm1_C (tid, dir). 
          tid \<leftarrow> [TID_stm1_t2], 
          dir \<leftarrow> [din, dout]] @
  [e3__stm1_C (tid, dir, n). 
          tid \<leftarrow> [TID_stm1_t1], 
          dir \<leftarrow> [din, dout],
          n \<leftarrow> core_int_list]
)
"

definition stm1_l_events where
"stm1_l_events = 
    set (
        [get_l_stm1_C l . l \<leftarrow> core_int_list] @
        [set_l_stm1_C l . l \<leftarrow> core_int_list]
    )
"

definition stm1_x_events where
"stm1_x_events = 
    set (
        [get_x_stm1_C x . x \<leftarrow> core_int_list] @
        [set_x_stm1_C x . x \<leftarrow> core_int_list] @
        [set_EXT_x_stm1_C x . x \<leftarrow> core_int_list]
    )
"

definition stm1_MachineInternalEvents where
"stm1_MachineInternalEvents = 
  set ([internal_stm1_C t . t \<leftarrow> TIDS_stm1_list])
"

subsubsection \<open> State Machine Memory \<close>
text \<open> Memory cell processes \<close>
(* for the shared variable x *)

definition stm1_Memory_opt_x where
"stm1_Memory_opt_x = 
  loop (\<lambda> s.
  (do {outp get_x_stm1 s; Ret (s)} \<box> 
   do {x \<leftarrow> inp_in set_x_stm1 core_int_set; Ret (x)} \<box>
   do {x \<leftarrow> inp_in set_EXT_x_stm1 core_int_set; Ret (x)})
)"
(*
term "set_x_stm1?(x):(core_int_set) \<rightarrow> (Ret (x))"

definition stm1_Memory_opt_x1 where
"stm1_Memory_opt_x1 = 
  loop (\<lambda> s.
  (do {get_x_stm1!(s) ; Ret (s)}  \<box> 
   do {set_x_stm1?(x):(core_int_set) \<rightarrow> (Ret (x))} \<box>
   do {x \<leftarrow> inp_in set_EXT_x_stm1 core_int_set; Ret (x)})
)"
*)

(* for the local variable l *)
definition stm1_Memory_opt_l where
"stm1_Memory_opt_l = 
  loop (\<lambda> s.
  (do {outp get_l_stm1 s; Ret (s)} \<box> 
   do {l \<leftarrow> inp_in set_l_stm1 core_int_set; Ret (l)})
)"

text \<open> Memory transition processes \<close>
definition stm1_MemoryTransitions_opt_0 where
"stm1_MemoryTransitions_opt_0 = 
  loop (\<lambda> id::integer. 
    (do {outp internal_stm1 TID_stm1_t0 ; Ret (id)} \<box> deadlock)
  )
"
term "do {outp internal_stm1 TID_stm1_t0 ; Ret (id)}"
term "outp internal_stm1 TID_stm1_t0"
term "Ret (id)"
(*
definition stm1_MemoryTransitions_opt_1 where
"stm1_MemoryTransitions_opt_1 = 
  loop (\<lambda> id::integer.
    do {x \<leftarrow> inp_in get_x_stm1 core_int_set ; 
      (
        do {inp_in e1__stm1 (set [(TID_stm1_t1, din, l). l \<leftarrow> core_int_list, (x = 0)])
              ; Ret (id)} \<box>
        do {guard (x \<noteq> 0); outp internal_stm1 TID_stm1_t2 ; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_x_stm1 core_int_set; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_EXT_x_stm1 core_int_set; Ret (id)}
      )
    }
  )
"

subsubsection \<open> States \<close>
definition I_stm1_i0 where
"I_stm1_i0 = (\<lambda> (id::integer) . 
  do {outp internal_stm1 TID_stm1_t0 ; 
      outp set_x_stm1 0; 
      outp enter_stm1 (SID_stm1, SID_stm1_s0);
      outp entered_stm1 (SID_stm1, SID_stm1_s0)
  })
"

term "(\<lambda> s. Ret (s)) \<Zcomp> (\<lambda> s. Ret (SID_stm1_s0))"
term "do { Ret (SID_stm1_s0) ; Ret (SID_stm1_s0)}"
term "do { sd \<leftarrow> inp_in enter_stm1 {(s, SID_stm1_s0) . (s \<in> (SIDS_stm1_set-{SID_stm1_s0}))} ; Ret (snd sd) }"
term "(\<lambda> s. Ret (s)) \<Zcomp> (\<lambda> s. while (\<lambda> s. fst s) (\<lambda> s. do { Ret (s)}) (s))"

term "(\<lambda> s. do {
        sd \<leftarrow> inp_in enter_stm1 {(s, SID_stm1_s0) . (s \<in> (SIDS_stm1_set-{SID_stm1_s0}))} ; 
          Ret (True, idd::integer, fst sd)}) \<Zcomp> 
          (\<lambda> s. while (\<lambda> s. fst s) (\<lambda> s. 
            do { Ret (s)}) (s))
  "

(*
definition State_stm1_s0 where 
"State_stm1_s0 = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_stm1 {(s, SID_stm1_s0) . (s \<in> (SIDS_stm1_set-{SID_stm1_s0}))} ; 
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        (while (\<lambda> s. fst s) 
         (\<lambda> s.
          do {Ret (ret)
          }) (ret)) ;
        Ret (id)
  }
)
"
*)

(* We need an interrupt operator for during actions *) 
(* ::"integer \<Rightarrow> SIDS_stm1 \<Rightarrow> (Chan_stm1, SIDS_stm1) itree" *)
definition State_stm1_s0 where 
"State_stm1_s0 = 
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
                \<comment> \<open> T_stm1_t1 \<close>
                do {t \<leftarrow> inp_in e1__stm1 (set [(TID_stm1_t1, din, l) . l \<leftarrow> core_int_list]) ;
                      outp set_l_stm1 (snd (snd t)) ; 
                      outp exit_stm1 (SID_stm1_s0, SID_stm1_s0);
                      outp exited_stm1 (SID_stm1_s0, SID_stm1_s0);
                      l \<leftarrow> inp_in get_l_stm1 core_int_set ; 
                        outp set_x_stm1 (l);
                        outp enter_stm1 (SID_stm1_s0, SID_stm1_s0);
                        Ret(True, fst (snd s), snd (snd s))
                    } \<box>
                \<comment> \<open> T_stm1_t2 \<close>
                do {outp internal_stm1 TID_stm1_t2;
                    outp exit_stm1 (SID_stm1_s0, SID_stm1_s0);
                    outp exited_stm1 (SID_stm1_s0, SID_stm1_s0);
                      x \<leftarrow> inp_in get_x_stm1 core_int_set ; 
                        outp e3_stm1 (dout, x);
                        outp enter_stm1 (SID_stm1_s0, SID_stm1_s0);
                        Ret(True, fst (snd s), snd (snd s))
                    } \<box>
                do {
                    x \<leftarrow> inp_in internal_stm1 
                      (set (filter (\<lambda> s. s \<in> {NULLTRANSITION_stm1,TID_stm1_t1,TID_stm1_t2}) 
                          ITIDS_stm1_list));
                    y \<leftarrow> inp_in exit_stm1 (set 
                      [(s, SID_stm1_s0) . s \<leftarrow> (removeAll SID_stm1_s0 SIDS_stm1_list)]);
                      outp exit_stm1 (fst y, SID_stm1_s0);
                      Ret (False, fst (snd s), snd (snd s))
                    } \<box>
                do {
                    x \<leftarrow> inp_in e1__stm1 (set [(s, d, l) . 
                        s \<leftarrow> (filter (\<lambda> s. s \<in> {NULLTRANSITION_stm1,TID_stm1_t1,TID_stm1_t2}) 
                          ITIDS_stm1_list), 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> core_int_list]) ;
                    y \<leftarrow> inp_in exit_stm1 (set 
                        [(s, SID_stm1_s0) . s \<leftarrow> (removeAll SID_stm1_s0 SIDS_stm1_list)]);
                      outp exit_stm1 (fst y, SID_stm1_s0);
                      Ret (False, fst (snd s), snd (snd s))
                    } \<box>
                do {
                    x \<leftarrow> inp_in e3__stm1 (set [(s, d, l) . 
                        s \<leftarrow> (filter (\<lambda> s. s \<in> {NULLTRANSITION_stm1,TID_stm1_t1,TID_stm1_t2}) 
                          ITIDS_stm1_list), 
                        d \<leftarrow> InOut_list,
                        l \<leftarrow> core_int_list]) ;
                    y \<leftarrow> inp_in exit_stm1 (set 
                        [(s, SID_stm1_s0) . s \<leftarrow> (removeAll SID_stm1_s0 SIDS_stm1_list)]);
                      outp exit_stm1 (fst y, SID_stm1_s0);
                      Ret (False, fst (snd s), snd (snd s))
                    }
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

definition STM_stm1 where
"STM_stm1 (idd::integer) = 
   (I_stm1_i0(idd))
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
   State_stm1_s0_R(idd)
"

definition stm1_e1_x_internal_set where
"stm1_e1_x_internal_set = 
  set ([e1__stm1_C (tid, dir, n). 
          tid \<leftarrow> [TID_stm1_t1], 
          dir \<leftarrow> [din, dout], 
          n \<leftarrow> core_int_list] @ 
       [internal_stm1_C TID_stm1_t2] @
       [set_x_stm1_C n. n \<leftarrow> core_int_list]
)"

(*
(Memory_opt_x(0)
 [| {|set_EXT_x,get_x,set_x|} |] 
 (
  (	
   (
     ((Memory_opt_l(0) [| {|get_l,set_l|} |] STM_core(id__))\ {|get_l,set_l|})
     [| {|internal__.TID_stm1_t0|} |]
     MemoryTransitions_opt_0(id__)
   ) \ {|internal__.TID_stm1_t0|}
  )
  [| {|e1__.TID_stm1_t1,internal__.TID_stm1_t2,set_x|} |]
  MemoryTransitions_opt_1(id__)
 )\{|internal__.TID_stm1_t2|}
) \ {|get_x|}
*)

subsubsection \<open> State machine \<close>
definition MemorySTM_opt_stm1 where
"MemorySTM_opt_stm1 (idd::integer) = 
  (hide
    (
      (discard_state (stm1_Memory_opt_x idd))
      \<parallel>\<^bsub> stm1_x_events \<^esub>
      (hide 
        (
          (par_hide
            (par_hide (discard_state (stm1_Memory_opt_l idd)) stm1_l_events (STM_stm1 idd))
            {internal_stm1_C TID_stm1_t0}
            (discard_state (stm1_MemoryTransitions_opt_0 idd))
          )
          \<parallel>\<^bsub> stm1_e1_x_internal_set \<^esub> 
          (discard_state (stm1_MemoryTransitions_opt_1 idd))
        )
        {internal_stm1_C TID_stm1_t2}
      )
    )
    (set [get_x_stm1_C n. n \<leftarrow> core_int_list])
  )   
"

(* Exception: P [| A |> Q*)
(* Renaming *)
definition AUX_opt_stm1 where
"AUX_opt_stm1 (idd::integer) = 
  (hide 
    ( 
      (MemorySTM_opt_stm1 idd)
    )
    stm1_MachineInternalEvents
  )
"

definition D__stm1 where
"D__stm1 (idd::integer) = 
  hide (AUX_opt_stm1 idd) internal_events_stm1
"
*)

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
  D__stm0 in Haskell 
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