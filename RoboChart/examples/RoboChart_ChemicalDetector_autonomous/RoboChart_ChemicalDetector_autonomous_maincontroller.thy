section \<open> MainController \label{sec:chem_maincontroller}\<close>

theory RoboChart_ChemicalDetector_autonomous_maincontroller
  imports "RoboChart_ChemicalDetector_autonomous_general"
begin

subsection \<open> GasAnalysis \label{ssec:chem_gasanalysis}\<close>
text \<open>The state machine @{text GasAnalysis} has a constant named @{text thr} of type 
@{text Intensity}. Its value is 1 (see @{verbatim "instantiation.csp"}).\<close>
definition "const_GasAnalysis_thr \<equiv> Chemical_IntensityC (1::2)"

datatype SIDS_GasAnalysis = SID_GasAnalysis
	              | SID_GasAnalysis_NoGas
	              | SID_GasAnalysis_Analysis
	              | SID_GasAnalysis_GasDetected
	              | SID_GasAnalysis_j1
	              | SID_GasAnalysis_Reading

definition "SIDS_GasAnalysis_list = [SID_GasAnalysis, SID_GasAnalysis_NoGas,
  SID_GasAnalysis_Analysis, SID_GasAnalysis_GasDetected, SID_GasAnalysis_j1
	, SID_GasAnalysis_Reading]"
definition "SIDS_GasAnalysis_set = set SIDS_GasAnalysis_list"
definition "SIDS_GasAnalysis_nodes = (removeAll SID_GasAnalysis SIDS_GasAnalysis_list)"
definition "SIDS_GasAnalysis_no_NoGas = (removeAll SID_GasAnalysis_NoGas SIDS_GasAnalysis_list)"
definition "SIDS_GasAnalysis_no_Analysis = (removeAll SID_GasAnalysis_Analysis SIDS_GasAnalysis_list)"
definition "SIDS_GasAnalysis_no_GasDetected = (removeAll SID_GasAnalysis_GasDetected SIDS_GasAnalysis_list)"
definition "SIDS_GasAnalysis_no_Reading = (removeAll SID_GasAnalysis_Reading SIDS_GasAnalysis_list)"
definition "SIDS_GasAnalysis_no_j1 = (removeAll SID_GasAnalysis_j1 SIDS_GasAnalysis_list)"

datatype TIDS_GasAnalysis = NULLTRANSITION__GasAnalysis
	              | TID_GasAnalysis_t1
	              | TID_GasAnalysis_t2
	              | TID_GasAnalysis_t3
	              | TID_GasAnalysis_t4
	              | TID_GasAnalysis_t8
	              | TID_GasAnalysis_t9a
	              | TID_GasAnalysis_t0

definition "TIDS_GasAnalysis_list = [NULLTRANSITION__GasAnalysis, TID_GasAnalysis_t1,
  TID_GasAnalysis_t2, TID_GasAnalysis_t3, TID_GasAnalysis_t4, TID_GasAnalysis_t8,
  TID_GasAnalysis_t9a, TID_GasAnalysis_t0]"
definition "TIDS_GasAnalysis_set = set TIDS_GasAnalysis_list"

text \<open> Identifiers of transitions that can interrupt a state, excluding transitions from junctions. \<close>
definition "ITIDS_GasAnalysis_list = [TID_GasAnalysis_t0, 
  TID_GasAnalysis_t2, TID_GasAnalysis_t3,	TID_GasAnalysis_t4,	
  TID_GasAnalysis_t8,	TID_GasAnalysis_t9a
]"

definition "ITIDS_GasAnalysis = set ITIDS_GasAnalysis_list"

chantype Chan_GasAnalysis =
(* flow channels *)
  internal_GasAnalysis :: TIDS_GasAnalysis
  enter_GasAnalysis :: "SIDS_GasAnalysis \<times> SIDS_GasAnalysis"
  entered_GasAnalysis :: "SIDS_GasAnalysis \<times> SIDS_GasAnalysis"
  exit_GasAnalysis :: "SIDS_GasAnalysis \<times> SIDS_GasAnalysis"
  exited_GasAnalysis :: "SIDS_GasAnalysis \<times> SIDS_GasAnalysis"
  terminate_GasAnalysis :: unit
(* Variables *)
  get_st_GasAnalysis :: Chemical_Status
  set_st_GasAnalysis :: Chemical_Status
  get_gs_GasAnalysis :: "2 Chemical_GasSensor blist[2]"
  set_gs_GasAnalysis :: "2 Chemical_GasSensor blist[2]"
  get_i_GasAnalysis :: "2 Chemical_Intensity"
  set_i_GasAnalysis :: "2 Chemical_Intensity"
  get_a_GasAnalysis :: "Chemical_Angle"
  set_a_GasAnalysis :: "Chemical_Angle"
(* event channels *)
  gas__GasAnalysis :: "TIDS_GasAnalysis \<times> InOut \<times> 2 Chemical_GasSensor blist[2]"
  gas_GasAnalysis :: "InOut \<times> 2 Chemical_GasSensor blist[2]"
  resume__GasAnalysis :: "TIDS_GasAnalysis \<times> InOut"
  resume_GasAnalysis :: "InOut"
  turn__GasAnalysis :: "TIDS_GasAnalysis \<times> InOut \<times> Chemical_Angle"
  turn_GasAnalysis :: "InOut \<times> Chemical_Angle"
  stop__GasAnalysis :: "TIDS_GasAnalysis \<times> InOut"
  stop_GasAnalysis :: "InOut"

subsubsection \<open> Sets of events \<close>
(* How to use a list to represent all possible values of Chemical_GasSensor blist[2] *)
(*term "\<lbrace>gas__GasAnalysis (t, d, s). t \<in> set [TID_GasAnalysis_t0, TID_GasAnalysis_t2, 
     TID_GasAnalysis_t3, TID_GasAnalysis_t4, TID_GasAnalysis_t8, TID_GasAnalysis_t9a] 
  \<and> d \<in> set [din, dout] \<and> s \<in> set lseq_gassensor_enum\<rbrace> \<union> {}"
*)
definition int_int_GasAnalysis where
"int_int_GasAnalysis = set (
  (enumchans3 [gas__GasAnalysis_C] 
    [TID_GasAnalysis_t0, TID_GasAnalysis_t2, 
     TID_GasAnalysis_t3, TID_GasAnalysis_t4,
     TID_GasAnalysis_t8, TID_GasAnalysis_t9a] 
    [din, dout] 
    (lseq_gassensor_enum)) @
  (enumchans2 [resume__GasAnalysis_C] 
    [TID_GasAnalysis_t0, TID_GasAnalysis_t2, 
     TID_GasAnalysis_t3, TID_GasAnalysis_t4,
     TID_GasAnalysis_t8, TID_GasAnalysis_t9a] 
    [din, dout]) @
  (enumchans3 [turn__GasAnalysis_C] 
    [TID_GasAnalysis_t0, TID_GasAnalysis_t2, 
     TID_GasAnalysis_t3, TID_GasAnalysis_t4,
     TID_GasAnalysis_t8, TID_GasAnalysis_t9a] 
    [din, dout]
    Chemical_Angle_list
    ) @
  (enumchans2 [stop__GasAnalysis_C] 
    [TID_GasAnalysis_t0, TID_GasAnalysis_t2, 
     TID_GasAnalysis_t3, TID_GasAnalysis_t4,
     TID_GasAnalysis_t8, TID_GasAnalysis_t9a] 
    [din, dout]  
    ) @
  (enumchan1 internal_GasAnalysis_C 
    [TID_GasAnalysis_t0, TID_GasAnalysis_t2, 
     TID_GasAnalysis_t3, TID_GasAnalysis_t4,
     TID_GasAnalysis_t8, TID_GasAnalysis_t9a])
)"

abbreviation "enter_exit_channels_GasAnalysis \<equiv>
  [enter_GasAnalysis_C, entered_GasAnalysis_C, exit_GasAnalysis_C, exited_GasAnalysis_C]"

definition internal_events_GasAnalysis where
"internal_events_GasAnalysis = set (
  enumchans2 enter_exit_channels_GasAnalysis SIDS_GasAnalysis_list SIDS_GasAnalysis_list
)"


definition GasAnalysis_i_events where
"GasAnalysis_i_events = 
    set (enumchans1 [get_i_GasAnalysis_C, set_i_GasAnalysis_C] Chemical_Intensity2_list)
"
(* This is a new syntax to define a set of events.
definition GasAnalysis_i_events' where
"GasAnalysis_i_events' = 
    \<lbrace>get_i_GasAnalysis x. x \<in> set Chemical_Intensity2_list \<rbrace>
"
value "GasAnalysis_i_events'"
*)

definition GasAnalysis_st_events where
"GasAnalysis_st_events = 
    set (enumchans1 [get_st_GasAnalysis_C, set_st_GasAnalysis_C] Chemical_Status_list)
"

definition GasAnalysis_gs_events where
"GasAnalysis_gs_events = 
    set (enumchans1 [get_gs_GasAnalysis_C, set_gs_GasAnalysis_C] lseq_gassensor_enum)
"

definition GasAnalysis_a_events where
"GasAnalysis_a_events = 
    set (enumchans1 [get_a_GasAnalysis_C, set_a_GasAnalysis_C] Chemical_Angle_list)
"

definition GasAnalysis_MachineInternalEvents where
"GasAnalysis_MachineInternalEvents = 
  set (enumchan1 internal_GasAnalysis_C TIDS_GasAnalysis_list)
"

subsubsection \<open> State Machine Memory \<close>
text \<open> Memory cell processes for local variables @{text gs}, @{text a}, @{text i}, and @{text st} 
are defined below.\<close>
definition GasAnalysis_Memory_opt_gs where
"GasAnalysis_Memory_opt_gs = 
  mem_of_lvar get_gs_GasAnalysis set_gs_GasAnalysis (set (lseq_gassensor_enum))"

definition GasAnalysis_Memory_opt_a where
"GasAnalysis_Memory_opt_a = mem_of_lvar get_a_GasAnalysis set_a_GasAnalysis Chemical_Angle_set"

definition GasAnalysis_Memory_opt_i where
"GasAnalysis_Memory_opt_i = mem_of_lvar get_i_GasAnalysis set_i_GasAnalysis (Chemical_Intensity2_set)"

definition GasAnalysis_Memory_opt_st where
"GasAnalysis_Memory_opt_st = mem_of_lvar get_st_GasAnalysis set_st_GasAnalysis (Chemical_Status_set)"

text \<open> Memory transition processes are defined below.\<close>
definition GasAnalysis_MemoryTransitions_opt_0 where
"GasAnalysis_MemoryTransitions_opt_0 = 
  loop (\<lambda> id::integer. 
    (do {outp internal_GasAnalysis TID_GasAnalysis_t1 ; Ret (id)} \<box> 
     do {gs \<leftarrow> inp_in gas__GasAnalysis (set [(TID_GasAnalysis_t2, din, x). 
              x \<leftarrow> (lseq_gassensor_enum)]) ; Ret (id)}  \<box> 
     do {gs \<leftarrow> inp_in gas__GasAnalysis (set [(TID_GasAnalysis_t0, din, x). 
              x \<leftarrow> (lseq_gassensor_enum)]) ; Ret (id)})
  )
"

definition GasAnalysis_MemoryTransitions_opt_1 where
"GasAnalysis_MemoryTransitions_opt_1 = 
  loop (\<lambda> id::integer.
    do {st \<leftarrow> inp_in get_st_GasAnalysis Chemical_Status_set ; 
      (
        \<comment> \<open>The transition @{text t4} with a guard @{text \<open>[st==Status::gasD]\<close>}\<close>
        do {guard (st = Chemical_Status_gasD); outp internal_GasAnalysis TID_GasAnalysis_t4 ; Ret (id)} \<box>
        \<comment> \<open>The transition @{text t3} with a guard @{text \<open>[st==Status::noGas]\<close>}\<close>
        do {guard (st = Chemical_Status_noGas); outp internal_GasAnalysis TID_GasAnalysis_t3 ; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_st_GasAnalysis Chemical_Status_set; Ret (id)}
      )
    }
  )
"

definition GasAnalysis_MemoryTransitions_opt_2 where
"GasAnalysis_MemoryTransitions_opt_2 = 
  loop (\<lambda> id::integer.
    do {i \<leftarrow> inp_in get_i_GasAnalysis Chemical_Intensity2_set ; 
      (
        do {guard (\<not> (Chemical_goreq i const_GasAnalysis_thr)); outp internal_GasAnalysis TID_GasAnalysis_t9a ; Ret (id)} \<box>
        do {guard (Chemical_goreq i const_GasAnalysis_thr); outp internal_GasAnalysis TID_GasAnalysis_t8 ; Ret (id)} \<box>
        do {x \<leftarrow> inp_in set_i_GasAnalysis Chemical_Intensity2_set; Ret (id)}
      )
    }
  )
"

subsubsection \<open> States \<close>
(*An extra \mbox{} here is to avoid the next definition will be generated in the same line as 
this paragraph *)
paragraph \<open> Initial \<close>text\<open>\mbox{}\<close>
definition I_GasAnalysis_i1 where
"I_GasAnalysis_i1 = (\<lambda> (id::integer) . 
  do {outp internal_GasAnalysis TID_GasAnalysis_t1 ; 
      outp enter_GasAnalysis (SID_GasAnalysis, SID_GasAnalysis_NoGas);
      outp entered_GasAnalysis (SID_GasAnalysis, SID_GasAnalysis_NoGas)
  })
"

paragraph \<open> NoGas \<close>text\<open>\mbox{}\<close>
definition CS_GasAnalysis_NoGas_sync where
"CS_GasAnalysis_NoGas_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_GasAnalysis [SID_GasAnalysis_NoGas] SIDS_GasAnalysis_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_GasAnalysis SIDS_GasAnalysis_nodes [SID_GasAnalysis_NoGas])
)"

definition GasAnalysis_NoGas_triggers where
"GasAnalysis_NoGas_triggers = set (
  (enumchan1 internal_GasAnalysis_C 
    [TID_GasAnalysis_t3, TID_GasAnalysis_t4,
     TID_GasAnalysis_t8, TID_GasAnalysis_t9a]) @
  (enumchans3 [gas__GasAnalysis_C] 
    [TID_GasAnalysis_t0, TID_GasAnalysis_t2] 
    [din, dout] 
    (lseq_gassensor_enum))
)
"

definition tids_GasAnalysis_NoGas where
" tids_GasAnalysis_NoGas = 
    (filter 
        (\<lambda> s. s \<notin> {NULLTRANSITION__GasAnalysis, TID_GasAnalysis_t9a,
          TID_GasAnalysis_t8, TID_GasAnalysis_t4, TID_GasAnalysis_t3, 
          TID_GasAnalysis_t2, TID_GasAnalysis_t0}) 
        ITIDS_GasAnalysis_list)"

abbreviation Other_SIDs_to_NoGas_GasAnalysis where
"Other_SIDs_to_NoGas_GasAnalysis \<equiv>
  set [(s, SID_GasAnalysis_NoGas) . s \<leftarrow> (SIDS_GasAnalysis_no_NoGas)]"

definition 
"exit_events_GasAnalysis idd sid tids other_sids =
    (do {inp_in internal_GasAnalysis (set tids);
        y \<leftarrow> inp_in exit_GasAnalysis other_sids;
          outp exited_GasAnalysis (fst y, sid);
          Ret(False, idd, sid)
        } \<box>
    do {t \<leftarrow> inp_in gas__GasAnalysis (set [(t, d, gs). 
            t \<leftarrow> (tids), d \<leftarrow> InOut_list,
            gs \<leftarrow> (lseq_gassensor_enum)]) ;
          y \<leftarrow> inp_in exit_GasAnalysis other_sids;
            outp exited_GasAnalysis (fst y, sid);
            Ret(False, idd, sid)
        } \<box>
    do {t \<leftarrow> inp_in resume__GasAnalysis (set [(t, d). 
            t \<leftarrow> (tids), d \<leftarrow> InOut_list]) ;
          y \<leftarrow> inp_in exit_GasAnalysis other_sids;
            outp exited_GasAnalysis (fst y, sid);
            Ret(False, idd, sid)
        } \<box>
    do {t \<leftarrow> inp_in turn__GasAnalysis (set [(t, d, a). 
            t \<leftarrow> (tids), d \<leftarrow> InOut_list,
            a \<leftarrow> Chemical_Angle_list]) ;
          y \<leftarrow> inp_in exit_GasAnalysis other_sids;
            outp exited_GasAnalysis (fst y, sid);
            Ret(False, idd, sid)
        } \<box>
    do {t \<leftarrow> inp_in stop__GasAnalysis (set [(t, d). 
            t \<leftarrow> (tids), d \<leftarrow> InOut_list]) ;
          y \<leftarrow> inp_in exit_GasAnalysis other_sids;
            outp exited_GasAnalysis (fst y, sid);
            Ret(False, idd, sid)
        }
    )"

definition State_GasAnalysis_NoGas where 
"State_GasAnalysis_NoGas = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_GasAnalysis Other_SIDs_to_NoGas_GasAnalysis ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> @{verbatim State_GasAnalysis_NoGas_execute} \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_GasAnalysis (snd (snd s), SID_GasAnalysis_NoGas);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> @{verbatim T_GasAnalysis_t2} \<close>
                do {t \<leftarrow> inp_in gas__GasAnalysis (set [(TID_GasAnalysis_t2, din, gs). 
                                gs \<leftarrow> (lseq_gassensor_enum)]) ;
                      outp set_gs_GasAnalysis (snd (snd t)) ; 
                      outp exit_GasAnalysis (SID_GasAnalysis_NoGas, SID_GasAnalysis_NoGas);
                      outp exited_GasAnalysis (SID_GasAnalysis_NoGas, SID_GasAnalysis_NoGas);
                      outp enter_GasAnalysis (SID_GasAnalysis_NoGas, SID_GasAnalysis_Analysis);
                      outp entered_GasAnalysis (SID_GasAnalysis_NoGas, SID_GasAnalysis_Analysis);
                      Ret(False, fst (snd s), SID_GasAnalysis_NoGas)
                    } \<box>
                (exit_events_GasAnalysis (fst (snd s)) SID_GasAnalysis_NoGas 
                   tids_GasAnalysis_NoGas Other_SIDs_to_NoGas_GasAnalysis)
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

definition State_GasAnalysis_NoGas_R where
"State_GasAnalysis_NoGas_R (idd::integer) = 
   (discard_state (State_GasAnalysis_NoGas idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_GasAnalysis - GasAnalysis_NoGas_triggers) \<^esub> 
   skip
"

paragraph \<open> Analysis \<close>text\<open>\mbox{}\<close>
definition CS_GasAnalysis_Analysis_sync where
"CS_GasAnalysis_Analysis_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_GasAnalysis [SID_GasAnalysis_Analysis] SIDS_GasAnalysis_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_GasAnalysis SIDS_GasAnalysis_nodes [SID_GasAnalysis_Analysis])
)"

definition GasAnalysis_Analysis_triggers where
"GasAnalysis_Analysis_triggers = set (
  (enumchan1 internal_GasAnalysis_C 
    [TID_GasAnalysis_t3, TID_GasAnalysis_t4,
     TID_GasAnalysis_t8, TID_GasAnalysis_t9a]) @
  (enumchans3 [gas__GasAnalysis_C] 
    [TID_GasAnalysis_t0, TID_GasAnalysis_t2] 
    [din, dout] 
    (lseq_gassensor_enum))
)
"

definition tids_GasAnalysis_Analysis where
" tids_GasAnalysis_Analysis = 
    (filter 
        (\<lambda> s. s \<notin> {NULLTRANSITION__GasAnalysis, TID_GasAnalysis_t9a,
          TID_GasAnalysis_t8, TID_GasAnalysis_t4, TID_GasAnalysis_t3, 
          TID_GasAnalysis_t2, TID_GasAnalysis_t0}) 
        ITIDS_GasAnalysis_list)"

abbreviation Other_SIDs_to_Analysis_GasAnalysis where
"Other_SIDs_to_Analysis_GasAnalysis \<equiv> 
  set [(s, SID_GasAnalysis_Analysis) . s \<leftarrow> (SIDS_GasAnalysis_no_Analysis)]"

definition State_GasAnalysis_Analysis where 
"State_GasAnalysis_Analysis = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_GasAnalysis Other_SIDs_to_Analysis_GasAnalysis ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> @{verbatim State_GasAnalysis_Analysis_execute} \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              gs \<leftarrow> inp_in get_gs_GasAnalysis (set (lseq_gassensor_enum));
              outp set_st_GasAnalysis (Chemical_analysis gs);
              outp entered_GasAnalysis (snd (snd s), SID_GasAnalysis_Analysis);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> @{verbatim T_GasAnalysis_t3} \<close>
                do {outp internal_GasAnalysis TID_GasAnalysis_t3 ;
                    outp exit_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_Analysis);
                    outp exited_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_Analysis);
                    outp resume_GasAnalysis dout;
                    outp enter_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_NoGas);
                    outp entered_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_NoGas);
                    Ret(False, fst (snd s), SID_GasAnalysis_Analysis)
                    } \<box>
                \<comment> \<open> @{verbatim T_GasAnalysis_t4} \<close>
                do {outp internal_GasAnalysis TID_GasAnalysis_t4 ;
                    outp exit_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_Analysis);
                    outp exited_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_Analysis);
                    outp enter_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_GasDetected);
                    outp entered_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_GasDetected);
                    Ret(False, fst (snd s), SID_GasAnalysis_Analysis)
                    } \<box>
                (exit_events_GasAnalysis (fst (snd s)) SID_GasAnalysis_Analysis 
                   tids_GasAnalysis_Analysis Other_SIDs_to_Analysis_GasAnalysis)
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

definition State_GasAnalysis_Analysis_R where
"State_GasAnalysis_Analysis_R (idd::integer) = 
   (discard_state (State_GasAnalysis_Analysis idd))
    \<parallel>\<^bsub> (int_int_GasAnalysis - GasAnalysis_Analysis_triggers) \<^esub> 
   skip
"

paragraph \<open> GasDetected \<close>text\<open>\mbox{}\<close>
definition CS_GasAnalysis_GasDetected_sync where
"CS_GasAnalysis_GasDetected_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_GasAnalysis [SID_GasAnalysis_GasDetected] SIDS_GasAnalysis_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_GasAnalysis SIDS_GasAnalysis_nodes [SID_GasAnalysis_GasDetected])
)"

definition GasAnalysis_GasDetected_triggers where
"GasAnalysis_GasDetected_triggers = set (
  (enumchan1 internal_GasAnalysis_C 
    [TID_GasAnalysis_t3, TID_GasAnalysis_t4,
     TID_GasAnalysis_t8, TID_GasAnalysis_t9a]) @
  (enumchans3 [gas__GasAnalysis_C] 
    [TID_GasAnalysis_t0, TID_GasAnalysis_t2] 
    [din, dout] 
    (lseq_gassensor_enum))
)
"

definition tids_GasAnalysis_GasDetected where
" tids_GasAnalysis_GasDetected = 
    (filter 
        (\<lambda> s. s \<notin> {NULLTRANSITION__GasAnalysis, TID_GasAnalysis_t9a,
          TID_GasAnalysis_t8, TID_GasAnalysis_t4, TID_GasAnalysis_t3, 
          TID_GasAnalysis_t2, TID_GasAnalysis_t0}) 
        ITIDS_GasAnalysis_list)"

abbreviation Other_SIDs_to_GasDetected_GasAnalysis where
"Other_SIDs_to_GasDetected_GasAnalysis \<equiv>
  set [(s, SID_GasAnalysis_GasDetected) . s \<leftarrow> (SIDS_GasAnalysis_no_GasDetected)]"

definition State_GasAnalysis_GasDetected where 
"State_GasAnalysis_GasDetected = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_GasAnalysis Other_SIDs_to_GasDetected_GasAnalysis ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> @{verbatim State_GasAnalysis_GasDetected_execute} \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              gs \<leftarrow> inp_in get_gs_GasAnalysis (set (lseq_gassensor_enum));
              guard (pre_Chemical_intensity(gs));
              outp set_i_GasAnalysis (Chemical_intensity gs);
              outp entered_GasAnalysis (snd (snd s), SID_GasAnalysis_GasDetected);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> @{verbatim T_GasAnalysis_t8} \<close>
                do {outp internal_GasAnalysis TID_GasAnalysis_t8 ;
                    outp exit_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_GasDetected);
                    outp exited_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_GasDetected);
                    outp stop_GasAnalysis dout;
                    outp enter_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_j1);
                    outp entered_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_j1);
                    Ret(False, fst (snd s), SID_GasAnalysis_GasDetected)
                    } \<box>
                 \<comment> \<open> @{verbatim T_GasAnalysis_t9a} \<close>
                do {outp internal_GasAnalysis TID_GasAnalysis_t9a ;
                    outp exit_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_GasDetected);
                    outp exited_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_GasDetected);
                    gs \<leftarrow> inp_in get_gs_GasAnalysis (set (lseq_gassensor_enum));
                    guard (pre_Chemical_location(gs));
                    outp set_a_GasAnalysis (Chemical_location gs);
                    a \<leftarrow> inp_in get_a_GasAnalysis Chemical_Angle_set;
                    outp turn_GasAnalysis (dout, a);
                    outp enter_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_Reading);
                    outp entered_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_Reading);
                    Ret(False, fst (snd s), SID_GasAnalysis_GasDetected)
                    } \<box>
                (exit_events_GasAnalysis (fst (snd s)) SID_GasAnalysis_GasDetected 
                   tids_GasAnalysis_GasDetected Other_SIDs_to_GasDetected_GasAnalysis)
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

definition State_GasAnalysis_GasDetected_R where
"State_GasAnalysis_GasDetected_R (idd::integer) = 
   (discard_state (State_GasAnalysis_GasDetected idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_GasAnalysis - GasAnalysis_GasDetected_triggers) \<^esub> 
   skip
"

paragraph \<open> Final \<close>text\<open>\mbox{}\<close>
definition CS_GasAnalysis_j1_sync where
"CS_GasAnalysis_j1_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_GasAnalysis [SID_GasAnalysis_j1] SIDS_GasAnalysis_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_GasAnalysis SIDS_GasAnalysis_nodes [SID_GasAnalysis_j1])
)"

definition GasAnalysis_j1_triggers where
"GasAnalysis_j1_triggers = set ([])
"

definition tids_GasAnalysis_j1 where
" tids_GasAnalysis_j1 = 
    (filter 
        (\<lambda> s. s \<notin> {NULLTRANSITION__GasAnalysis, TID_GasAnalysis_t9a,
          TID_GasAnalysis_t8, TID_GasAnalysis_t4, TID_GasAnalysis_t3, 
          TID_GasAnalysis_t2, TID_GasAnalysis_t0}) 
        ITIDS_GasAnalysis_list)"

abbreviation Other_SIDs_to_j1_GasAnalysis where
"Other_SIDs_to_j1_GasAnalysis \<equiv>
  set [(s, SID_GasAnalysis_j1) . s \<leftarrow> (SIDS_GasAnalysis_no_j1)]"

definition State_GasAnalysis_j1 where 
"State_GasAnalysis_j1 = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_GasAnalysis Other_SIDs_to_j1_GasAnalysis ; 
        outp terminate_GasAnalysis ();
        Ret (id)
    }
)
"

definition State_GasAnalysis_j1_R where
"State_GasAnalysis_j1_R (idd::integer) = 
   (discard_state (State_GasAnalysis_j1 idd))
    \<parallel>\<^bsub> (int_int_GasAnalysis - GasAnalysis_j1_triggers) \<^esub> 
   skip
"

paragraph \<open> Reading \<close>text\<open>\mbox{}\<close>
definition CS_GasAnalysis_Reading_sync where
"CS_GasAnalysis_Reading_sync = 
  set (
      \<comment> \<open> enter from x to y \<close>
      (enumchans2 enter_exit_channels_GasAnalysis [SID_GasAnalysis_Reading] SIDS_GasAnalysis_nodes)@
      \<comment> \<open> enter from y to x \<close>
      (enumchans2 enter_exit_channels_GasAnalysis SIDS_GasAnalysis_nodes [SID_GasAnalysis_Reading])
)"

definition GasAnalysis_Reading_triggers where
"GasAnalysis_Reading_triggers = set (
  (enumchan1 internal_GasAnalysis_C 
    [TID_GasAnalysis_t3, TID_GasAnalysis_t4,
     TID_GasAnalysis_t8, TID_GasAnalysis_t9a]) @
  (enumchans3 [gas__GasAnalysis_C] 
    [TID_GasAnalysis_t0, TID_GasAnalysis_t2] 
    [din, dout] 
    (lseq_gassensor_enum))
)
"

definition tids_GasAnalysis_Reading where
" tids_GasAnalysis_Reading = 
    (filter 
        (\<lambda> s. s \<notin> {NULLTRANSITION__GasAnalysis, TID_GasAnalysis_t9a,
          TID_GasAnalysis_t8, TID_GasAnalysis_t4, TID_GasAnalysis_t3, 
          TID_GasAnalysis_t2, TID_GasAnalysis_t0}) 
        ITIDS_GasAnalysis_list)"

abbreviation Other_SIDs_to_Reading_GasAnalysis where
"Other_SIDs_to_Reading_GasAnalysis \<equiv>
  set [(s, SID_GasAnalysis_Reading) . s \<leftarrow> (SIDS_GasAnalysis_no_Reading)]"

definition State_GasAnalysis_Reading where 
"State_GasAnalysis_Reading = 
  loop (\<lambda> (id::integer).
    do {sd \<leftarrow> inp_in enter_GasAnalysis Other_SIDs_to_Reading_GasAnalysis ; 
        \<comment> \<open> State passed to next loop, including a condition initially True. \<close>
        ret \<leftarrow> Ret (True, id, fst sd) ; 
        \<comment> \<open> @{verbatim State_GasAnalysis_Reading_execute} \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_GasAnalysis (snd (snd s), SID_GasAnalysis_Reading);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> @{verbatim T_GasAnalysis_t0} \<close>
                do {gs \<leftarrow> inp_in gas__GasAnalysis (set [(TID_GasAnalysis_t0, din, x). 
                        x \<leftarrow> (lseq_gassensor_enum)]) ;
                    outp set_gs_GasAnalysis (snd (snd gs));
                    outp exit_GasAnalysis (SID_GasAnalysis_Reading, SID_GasAnalysis_Reading);
                    outp exited_GasAnalysis (SID_GasAnalysis_Reading, SID_GasAnalysis_Reading);
                    outp enter_GasAnalysis (SID_GasAnalysis_Reading, SID_GasAnalysis_Analysis);
                    outp entered_GasAnalysis (SID_GasAnalysis_Reading, SID_GasAnalysis_Analysis);
                    Ret(False, fst (snd s), SID_GasAnalysis_Reading)
                    } \<box>
                (exit_events_GasAnalysis (fst (snd s)) SID_GasAnalysis_Reading 
                   tids_GasAnalysis_Reading Other_SIDs_to_Reading_GasAnalysis)
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

definition State_GasAnalysis_Reading_R where
"State_GasAnalysis_Reading_R (idd::integer) = 
   (discard_state (State_GasAnalysis_Reading idd))
    \<parallel>\<^bsub> (int_int_GasAnalysis - GasAnalysis_Reading_triggers) \<^esub> 
   skip
"

subsubsection \<open> State machine \<close>
definition flow_events_GasAnalysis_stm_to_nodes where
"flow_events_GasAnalysis_stm_to_nodes = (
 let nodes = [SID_GasAnalysis_NoGas,SID_GasAnalysis_Analysis,SID_GasAnalysis_GasDetected,
              SID_GasAnalysis_j1,SID_GasAnalysis_Reading]
 in set (
      enumchans2 [enter_GasAnalysis_C, entered_GasAnalysis_C,exit_GasAnalysis_C,exited_GasAnalysis_C] 
          (filter (\<lambda> s. s \<notin> set nodes) SIDS_GasAnalysis_list) nodes
  )
)"

definition STM_GasAnalysis where
"STM_GasAnalysis (idd::integer) = 
   (I_GasAnalysis_i1(idd))
    \<parallel>\<^bsub> flow_events_GasAnalysis_stm_to_nodes \<^esub> 
   (State_GasAnalysis_NoGas_R(idd)
      \<parallel>\<^bsub> CS_GasAnalysis_NoGas_sync \<inter> (CS_GasAnalysis_Analysis_sync \<union> 
          (CS_GasAnalysis_GasDetected_sync \<union> (CS_GasAnalysis_j1_sync \<union> CS_GasAnalysis_Reading_sync))) \<^esub>
      (State_GasAnalysis_Analysis_R(idd)
        \<parallel>\<^bsub> CS_GasAnalysis_Analysis_sync \<inter> (CS_GasAnalysis_GasDetected_sync \<union> 
            (CS_GasAnalysis_j1_sync \<union> CS_GasAnalysis_Reading_sync)) \<^esub> 
        ( State_GasAnalysis_GasDetected_R(idd)
          \<parallel>\<^bsub> CS_GasAnalysis_GasDetected_sync \<inter> (CS_GasAnalysis_j1_sync \<union> CS_GasAnalysis_Reading_sync) \<^esub> 
          (State_GasAnalysis_j1_R(idd)  
            \<parallel>\<^bsub> CS_GasAnalysis_j1_sync \<inter> CS_GasAnalysis_Reading_sync \<^esub> 
          State_GasAnalysis_Reading_R(idd))
        )
      )
   )
"

definition GasAnalysis_opt_0_internal_set where
"GasAnalysis_opt_0_internal_set = 
  set (([internal_GasAnalysis_C TID_GasAnalysis_t1]) @ 
       (enumchans3 [gas__GasAnalysis_C] 
          [TID_GasAnalysis_t0, TID_GasAnalysis_t2] 
          [din, dout] 
          (lseq_gassensor_enum))
)"

definition GasAnalysis_opt_1_internal_set where
"GasAnalysis_opt_1_internal_set = 
  set ((enumchans1 [internal_GasAnalysis_C] [TID_GasAnalysis_t4, TID_GasAnalysis_t3]) @
       (enumchans1 [set_st_GasAnalysis_C] Chemical_Status_list)
)"

definition GasAnalysis_opt_2_internal_set where
"GasAnalysis_opt_2_internal_set = 
  set ((enumchans1 [internal_GasAnalysis_C] [TID_GasAnalysis_t8, TID_GasAnalysis_t9a] @
      (enumchans1 [set_i_GasAnalysis_C] Chemical_Intensity2_list))
)"

definition MemorySTM_opt_GasAnalysis where
"MemorySTM_opt_GasAnalysis (idd::integer) = 
  (par_hide
    (discard_state (GasAnalysis_Memory_opt_i (Chemical_IntensityC (0::2))))
    GasAnalysis_i_events
    ( 
      (
        (par_hide
          (discard_state (GasAnalysis_Memory_opt_st (Chemical_Status_noGas)))
          GasAnalysis_st_events
          ( 
            (
              (
                (
                  (par_hide
                    (discard_state (GasAnalysis_Memory_opt_gs (bmake TYPE(2) [])))
                    GasAnalysis_gs_events
                    (par_hide 
                      (discard_state (GasAnalysis_Memory_opt_a Chemical_Angle_Left)) 
                      GasAnalysis_a_events 
                      (STM_GasAnalysis idd)
                    )
                  )
                  \<parallel>\<^bsub> GasAnalysis_opt_0_internal_set \<^esub>
                  (discard_state (GasAnalysis_MemoryTransitions_opt_0 idd))
                ) \<setminus> ({internal_GasAnalysis_C TID_GasAnalysis_t1})
              )
              \<parallel>\<^bsub> GasAnalysis_opt_1_internal_set \<^esub> 
              (discard_state (GasAnalysis_MemoryTransitions_opt_1 idd))
            ) \<setminus> (set (enumchans1 [internal_GasAnalysis_C] [TID_GasAnalysis_t4, TID_GasAnalysis_t3]))
          )
        )
        \<parallel>\<^bsub> GasAnalysis_opt_2_internal_set \<^esub>
        (discard_state (GasAnalysis_MemoryTransitions_opt_2 idd))
      ) \<setminus> (set (enumchans1 [internal_GasAnalysis_C] [TID_GasAnalysis_t8, TID_GasAnalysis_t9a]))
    )
  )   
"

definition rename_GasAnalysis_events where
"rename_GasAnalysis_events = 
  concat (
    (enumchan2 (forget_first2 gas__GasAnalysis_C gas_GasAnalysis_C TIDS_GasAnalysis_list) 
            InOut_list lseq_gassensor_enum) @
    (enumchan2 (forget_first2 turn__GasAnalysis_C turn_GasAnalysis_C TIDS_GasAnalysis_list) 
            InOut_list Chemical_Angle_list) @
    (enumchan1 (forget_first resume__GasAnalysis_C resume_GasAnalysis_C TIDS_GasAnalysis_list) 
            InOut_list) @
    (enumchan1 (forget_first stop__GasAnalysis_C stop_GasAnalysis_C TIDS_GasAnalysis_list) 
            InOut_list)
  )
"

term "\<lbrace>resume__GasAnalysis (t, x) \<mapsto> resume_GasAnalysis x | (x, t). x \<in> InOut_set\<rbrace>"
term "\<lbrace>terminate_GasAnalysis () \<mapsto> terminate_GasAnalysis () | _. True\<rbrace>"

definition rename_GasAnalysis_events_others where
"rename_GasAnalysis_events_others = 
  (enumchanp1 terminate_GasAnalysis_C [()]) @
  (enumchansp1 [get_i_GasAnalysis_C, set_i_GasAnalysis_C] Chemical_Intensity2_list) @
  (enumchansp1 [get_a_GasAnalysis_C, set_a_GasAnalysis_C] Chemical_Angle_list) @
  (enumchansp1 [get_st_GasAnalysis_C, set_st_GasAnalysis_C] Chemical_Status_list) @
  (enumchansp1 [get_gs_GasAnalysis_C, set_gs_GasAnalysis_C] lseq_gassensor_enum) @
  (enumchansp2 [gas_GasAnalysis_C] InOut_list lseq_gassensor_enum) @
  (enumchansp2 [turn_GasAnalysis_C] InOut_list Chemical_Angle_list) @
  (enumchansp1 [resume_GasAnalysis_C, stop_GasAnalysis_C] InOut_list) @
  (enumchansp2 [enter_GasAnalysis_C, entered_GasAnalysis_C, exit_GasAnalysis_C, exited_GasAnalysis_C] 
    SIDS_GasAnalysis_list SIDS_GasAnalysis_list) @
  (enumchansp1 [internal_GasAnalysis_C] TIDS_GasAnalysis_list)
"

definition rename_MemorySTM_opt_GasAnalysis where
"rename_MemorySTM_opt_GasAnalysis idd = 
  ( (MemorySTM_opt_GasAnalysis idd) \<lbrakk>
      (set (rename_GasAnalysis_events @ rename_GasAnalysis_events_others))
    \<rbrakk>)
"

definition AUX_opt_GasAnalysis where
"AUX_opt_GasAnalysis (idd::integer) = 
  ( 
    ( 
      (rename_MemorySTM_opt_GasAnalysis idd) \<lbrakk> set [terminate_GasAnalysis_C ()] \<Zrres> skip
    ) \<setminus> GasAnalysis_MachineInternalEvents
  )
"

definition D__GasAnalysis where
"D__GasAnalysis (idd::integer) = 
  (AUX_opt_GasAnalysis idd) \<setminus> internal_events_GasAnalysis
"

subsection \<open> MainController \label{ssec:chem_maincontroller}\<close>
chantype Chan_MainController =
  terminate_MainController :: unit
  gas_MainController :: "InOut \<times> 2 Chemical_GasSensor blist[2]"
  resume_MainController :: "InOut"
  turn_MainController :: "InOut \<times> Chemical_Angle"
  stop_MainController :: "InOut"

subsubsection \<open> Memory \<close>
definition Memory_MainController where
"Memory_MainController (idd::integer) = skip"

subsubsection \<open> Controller \<close>

definition rename_MainController_GasAnalysis_events where
"rename_MainController_GasAnalysis_events = 
  (enumchanp2_1 (terminate_GasAnalysis_C,terminate_MainController_C) [()]) @
  (enumchansp2_2 [(gas_GasAnalysis_C, gas_MainController_C)] InOut_list lseq_gassensor_enum) @
  (enumchansp2_1 [(resume_GasAnalysis_C, resume_MainController_C)] InOut_list) @
  (enumchansp2_2 [(turn_GasAnalysis_C, turn_MainController_C)] InOut_list Chemical_Angle_list) @
  (enumchansp2_1 [(stop_GasAnalysis_C, stop_MainController_C)] InOut_list)
"

definition rename_D__GasAnalysis where
"rename_D__GasAnalysis idd = (
    (D__GasAnalysis idd) \<lbrakk> (set rename_MainController_GasAnalysis_events)\<rbrakk>
)"

definition D__MainController where
"D__MainController (idd::integer) = 
  (par_hide
    (rename_D__GasAnalysis idd)
    {}
    (discard_state (Memory_MainController idd))
  ) \<lbrakk> set [terminate_MainController_C ()] \<Zrres> skip
"
(*
definition "D__MainController_sim = D__MainController 0"
text \<open>Uncomment the line below to animate @{term AUX_opt_Movement}.\<close>
animate1 D__MainController_sim
*)
subsubsection \<open> Export code \<close>
export_code
  GasAnalysis_Memory_opt_gs
  GasAnalysis_MemoryTransitions_opt_0
  GasAnalysis_MemoryTransitions_opt_1
  GasAnalysis_MemoryTransitions_opt_2
  I_GasAnalysis_i1
  State_GasAnalysis_NoGas
  State_GasAnalysis_NoGas_R
  State_GasAnalysis_Analysis_R
  State_GasAnalysis_GasDetected_R
  State_GasAnalysis_j1_R
  State_GasAnalysis_Reading_R
  STM_GasAnalysis
  MemorySTM_opt_GasAnalysis
  rename_MemorySTM_opt_GasAnalysis
  AUX_opt_GasAnalysis
  D__GasAnalysis
  D__MainController
in Haskell 
  module_name GasAnalysis
  file_prefix RoboChart_ChemicalDetector 
  (string_classes) 

generate_file \<open>code/RoboChart_ChemicalDetector/Simulate.hs\<close> = 
\<open>module Simulate (simulate) where
import qualified Interaction_Trees;
import qualified Partial_Fun;
import qualified Bounded_List;
import qualified Data.List.Split;
import qualified Data.List;

isPrefixOf              :: (Eq a) => [a] -> [a] -> Bool;
isPrefixOf [] _         =  True;
isPrefixOf _  []        =  False;
isPrefixOf (x:xs) (y:ys)=  x == y && isPrefixOf xs ys;

removeSubstr :: String -> String -> String;
removeSubstr w "" = "";
removeSubstr w s@(c:cs) = (if w `isPrefixOf` s then Prelude.drop (Prelude.length w) s else c : removeSubstr w cs);

replace :: String -> String -> String -> String;
replace old new = Data.List.intercalate new . Data.List.Split.splitOn old;

renameGasEvent :: String -> String;
renameGasEvent gas = 
  (
  replace " ()]" "]" (
    replace " ()," "," (
      removeSubstr "Chemical_GasSensor_ext " (
        replace "(Chemical_IntensityC 1)" "1)" (
          replace "(Chemical_IntensityC 0)" "0)" (
            replace "(Chemical_ChemC 1)" "(1," (
              replace "(Chemical_ChemC 0)" "(0," (
                replace "(Abs_bit0 (Pos One))" "1" (
                  replace "(Abs_bit0 Zero_int)" "0" (
                    removeSubstr "Chemical_GasSensor_ext " (
                      removeSubstr "Bmake Type" (
                        removeSubstr "_C" gas)))
                  )
                )
              )
            )
          )
        )
      )
    )
  );
{-  (removeSubstr "_C" gas) >>=
  (\e -> removeSubstr "Bmake Type" e) >>=
  (\e -> removeSubstr "Chemical_GasSensor_ext" e);
-}

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
  do { Prelude.putStrLn ("Events:" ++ Prelude.concat (map (\(n, e) -> " (" ++ Prelude.show n ++ ") " ++ renameGasEvent e ++ ";") (zip [1..] (map (Prelude.show . fst) m))));
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
import qualified RoboChart_ChemicalDetector_autonomous_maincontroller;

main :: IO ()
main =
  do
    Simulate.simulate (RoboChart_ChemicalDetector_autonomous_maincontroller.d_MainController 0);
\<close>

export_generated_files 
  \<open>code/RoboChart_ChemicalDetector/Simulate.hs\<close>
  \<open>code/RoboChart_ChemicalDetector/Main.hs\<close>

end
