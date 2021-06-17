section \<open> A very basic RoboChart CSP Semantics \<close>

theory RoboChart_CSP_sem_basic
  imports "../ITree_CSP"
begin

subsection \<open> General definitions \<close>
definition "int_max = (2::integer)"
definition "int_min = (-2::integer)"

type_synonym core_int = integer

fun int2integer_list :: "int list \<Rightarrow> integer list" where
"int2integer_list Nil = Nil" |
"int2integer_list (Cons x xs) 
  = Cons (integer_of_int x) (int2integer_list xs)"

abbreviation "core_int_list \<equiv> 
  int2integer_list [(int_of_integer int_min)..(int_of_integer int_max)]"

abbreviation "core_int_set \<equiv> set core_int_list"

datatype InOut = din | dout

definition "InOut_set = {din, dout}"

definition set2list:: "'a set \<Rightarrow> 'a list" where
"set2list s = (SOME l. set l = s)"

subsection \<open> stm0 \<close>
datatype SIDS_stm0 = SID_stm0
  | SID_stm0_s0

definition "SIDS_stm0_set = {SID_stm0, SID_stm0_s0}"
definition "SIDS_stm0_list = [SID_stm0, SID_stm0_s0]"

datatype TIDS_stm0 = NULLTRANSITION_stm0
	              | TID_stm0_t0
	              | TID_stm0_t1
	              | TID_stm0_t2

definition "TIDS_stm0_set = {NULLTRANSITION_stm0, TID_stm0_t0, TID_stm0_t1, TID_stm0_t2}"
definition "TIDS_stm0_list = [NULLTRANSITION_stm0, TID_stm0_t0, TID_stm0_t1, TID_stm0_t2]"

definition "ITIDS_stm0 = {TID_stm0_t1, TID_stm0_t2}"

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

subsubsection \<open> State Machine Memory \<close>
text \<open> Memory cell processes \<close>
(* for the shared variable x *)
definition stm0_Memory_opt_x where
"stm0_Memory_opt_x = 
  loop (\<lambda> s.
  (do {outp get_x_stm0 s; Ret (s)} \<box> 
   do {x \<leftarrow> inp_in set_x_stm0 core_int_set; Ret (x)} \<box>
   do {x \<leftarrow> inp_in set_EXT_x_stm0 core_int_set; Ret (x)})
)"

(* for the local variable l *)
definition stm0_Memory_opt_l where
"stm0_Memory_opt_l = 
  loop (\<lambda> s.
  (do {outp get_l_stm0 s; Ret (s)} \<box> 
   do {l \<leftarrow> inp_in set_l_stm0 core_int_set; Ret (l)})
)"

text \<open> Memory transition processes \<close>
definition stm0_MemoryTransitions_opt_0 where
"stm0_MemoryTransitions_opt_0 = 
  loop (\<lambda> id::integer. 
    (do {outp internal_stm0 TID_stm0_t0 ; Ret (id)} \<box> deadlock)
  )
"
term "do {outp internal_stm0 TID_stm0_t0 ; Ret (id)}"
term "outp internal_stm0 TID_stm0_t0"
term "Ret (id)"

definition stm0_MemoryTransitions_opt_1 where
"stm0_MemoryTransitions_opt_1 = 
  loop (\<lambda> id::integer.
    do {x \<leftarrow> inp_in get_x_stm0 core_int_set ; 
      (
        do {inp_in e1__stm0 
              {(TID_stm0_t1, din, l) . (l \<in> core_int_set) \<and> (x = 0)}
              ; Ret (id)} \<box>
        do {guard (x \<noteq> 0); outp internal_stm0 TID_stm0_t2 ; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_x_stm0 core_int_set; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_EXT_x_stm0 core_int_set; Ret (id)}
      )
    }
  )
"

subsubsection \<open> State Machine \<close>
definition I_stm0_i0 where
"I_stm0_i0 = (\<lambda> (id::integer) . 
  do {outp internal_stm0 TID_stm0_t0 ; 
      outp set_x_stm0 0; 
      outp enter_stm0 (SID_stm0, SID_stm0_s0);
      outp entered_stm0 (SID_stm0, SID_stm0_s0)
  })
"

term "(\<lambda> s. Ret (s)) \<Zcomp> (\<lambda> s. Ret (SID_stm0_s0))"
term "do { Ret (SID_stm0_s0) ; Ret (SID_stm0_s0)}"
term "do { sd \<leftarrow> inp_in enter_stm0 {(s, SID_stm0_s0) . (s \<in> (SIDS_stm0_set-{SID_stm0_s0}))} ; Ret (snd sd) }"
term "(\<lambda> s. Ret (s)) \<Zcomp> (\<lambda> s. while (\<lambda> s. fst s) (\<lambda> s. do { Ret (s)}) (s))"

term "(\<lambda> s. do {
        sd \<leftarrow> inp_in enter_stm0 {(s, SID_stm0_s0) . (s \<in> (SIDS_stm0_set-{SID_stm0_s0}))} ; 
          Ret (True, idd::integer, fst sd)}) \<Zcomp> 
          (\<lambda> s. while (\<lambda> s. fst s) (\<lambda> s. 
            do { Ret (s)}) (s))
  "

(*
definition State_stm0_s0 where 
"State_stm0_s0 = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_stm0 {(s, SID_stm0_s0) . (s \<in> (SIDS_stm0_set-{SID_stm0_s0}))} ; 
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
(* ::"integer \<Rightarrow> SIDS_stm0 \<Rightarrow> (Chan_stm0, SIDS_stm0) itree" *)
definition State_stm0_s0 where 
"State_stm0_s0 = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_stm0 {(s, SID_stm0_s0) . (s \<in> (SIDS_stm0_set-{SID_stm0_s0}))} ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> State_stm0_s0_execute \<close>
        (while 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> condition \<close>
           (\<lambda> s.
            do {
              outp entered_stm0 (snd (snd s), SID_stm0_s0);
                \<comment> \<open> T_stm0_t1 \<close>
                do {t \<leftarrow> inp_in e1__stm0 {(TID_stm0_t1, din, l) . (l \<in> core_int_set)} ;
                      outp set_l_stm0 (snd (snd t)) ; 
                      outp exit_stm0 (SID_stm0_s0, SID_stm0_s0);
                      outp exited_stm0 (SID_stm0_s0, SID_stm0_s0);
                      l \<leftarrow> inp_in get_l_stm0 core_int_set ; 
                        outp set_x_stm0 (l);
                        outp enter_stm0 (SID_stm0_s0, SID_stm0_s0);
                        Ret(True, fst (snd s), snd (snd s))
                    } \<box>
                \<comment> \<open> T_stm0_t2 \<close>
                do {outp internal_stm0 TID_stm0_t2;
                    outp exit_stm0 (SID_stm0_s0, SID_stm0_s0);
                    outp exited_stm0 (SID_stm0_s0, SID_stm0_s0);
                      x \<leftarrow> inp_in get_x_stm0 core_int_set ; 
                        outp e3_stm0 (dout, x);
                        outp enter_stm0 (SID_stm0_s0, SID_stm0_s0);
                        Ret(True, fst (snd s), snd (snd s))
                    } \<box>
                do {
                    x \<leftarrow> inp_in internal_stm0 (TIDS_stm0_set - {NULLTRANSITION_stm0,TID_stm0_t1,TID_stm0_t2});
                    y \<leftarrow> inp_in exit_stm0 {(s, SID_stm0_s0). s \<in> (SIDS_stm0_set - {SID_stm0_s0})};
                      outp exit_stm0 (fst y, SID_stm0_s0);
                      Ret (False, fst (snd s), snd (snd s))
                    } \<box>
                do {
                    x \<leftarrow> inp_in e1__stm0 {(s, d, l) . 
                        (s \<in> (TIDS_stm0_set - {NULLTRANSITION_stm0,TID_stm0_t1,TID_stm0_t2})) \<and> 
                        (d \<in> InOut_set) \<and>
                        (l \<in> core_int_set)} ;
                    y \<leftarrow> inp_in exit_stm0 {(s, SID_stm0_s0). s \<in> (SIDS_stm0_set - {SID_stm0_s0})};
                      outp exit_stm0 (fst y, SID_stm0_s0);
                      Ret (False, fst (snd s), snd (snd s))
                    } \<box>
                do {
                    x \<leftarrow> inp_in e3__stm0 {(s, d, l) . 
                        (s \<in> (TIDS_stm0_set - {NULLTRANSITION_stm0,TID_stm0_t1,TID_stm0_t2})) \<and> 
                        (d \<in> InOut_set) \<and>
                        (l \<in> core_int_set)} ;
                    y \<leftarrow> inp_in exit_stm0 {(s, SID_stm0_s0). s \<in> (SIDS_stm0_set - {SID_stm0_s0})};
                      outp exit_stm0 (fst y, SID_stm0_s0);
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

export_code stm0_Memory_opt_l stm0_MemoryTransitions_opt_0 in Haskell 
  module_name RoboChart_basic 
  file_prefix RoboChart_basic 
  (string_classes) 

end