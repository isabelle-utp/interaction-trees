section \<open> Simulation of a very basic RoboChart model \<close>
text \<open> This theory aims for simulation of a trivial RoboChart model based on its CSP
 semantics. We use the @{term "rename"} operator for renaming.
\<close>
theory RoboChart_ChemicalDetector_autonomous
  imports "../../ITree_RoboChart" "../../RC_Channel_Type" "../../Bounded_List" "../../Nat_Of"
begin

declare [[show_types]]

subsection \<open> General definitions \<close>
interpretation rc: robochart_confs "-2" "2" "2" "-2" "2".

subsubsection \<open> Constants \<close>

subsubsection \<open> Types \<close>

(* PrimitiveType in RoboChart like given types in Z, and instantiated in CSP *)

datatype ('a::finite) Chemical_Chem = Chemical_ChemC 'a

abbreviation "Chemical_Chem2_list \<equiv> [Chemical_ChemC (0::2), Chemical_ChemC (1::2)]"
abbreviation "Chemical_Chem2_set \<equiv> set Chemical_Chem2_list"

definition Chemical_Chem_is_zero::"(2 Chemical_Chem) \<Rightarrow> bool" where
"Chemical_Chem_is_zero x = (if x = (Chemical_ChemC (0::2)) then True else False)"

value "Chemical_Chem_is_zero (Chemical_ChemC (3::2))"

datatype ('a::finite) Chemical_Intensity = Chemical_IntensityC 'a

abbreviation "Chemical_Intensity2_list \<equiv> [Chemical_IntensityC (0::2), Chemical_IntensityC 1]"
abbreviation "Chemical_Intensity2_set \<equiv> set Chemical_Intensity2_list"

definition Chemical_Intensity_is_zero::"(2 Chemical_Intensity) \<Rightarrow> bool" where
"Chemical_Intensity_is_zero x = (if x = (Chemical_IntensityC (0::2)) then True else False)"

fun Chemical_goreq :: "2 Chemical_Intensity \<Rightarrow> 2 Chemical_Intensity \<Rightarrow> bool" where
"Chemical_goreq (Chemical_IntensityC x) (Chemical_IntensityC y) = (x \<ge> y) "

text \<open> In CSP, LSeq(T,n) from core_defs.csp can be used as a type or an expression. In this 
RoboChart model, it is used as a type, parametrised by n. We use bounded_list to implement it, 
such as @{typ "int[2]blist"} for LSeq(int, 2).
\<close>

fun lseq where
"lseq s 0 = [[]]" |
"lseq s (Suc 0) = [[q]. q \<leftarrow> s]" |
"lseq s (Suc n) = [q # qs. q \<leftarrow> s, qs \<leftarrow> (lseq s n)]"

fun lseqn where
"lseqn s 0 = lseq s 0" |
"lseqn s (Suc n) = lseqn s n @ (lseq s (Suc n))"

text \<open> Make a bounded list from the supplied list, a set of all possible elements. \<close>
definition mk_blist :: "'n itself \<Rightarrow> 'a list \<Rightarrow> ('a['n::finite]blist) list" where
"mk_blist _ xs = map (bmake TYPE('n)) (lseqn xs CARD('n))"

subsection \<open> Chemical package \<close>
enumtype Chemical_Status = 
  Chemical_Status_noGas | Chemical_Status_gasD

abbreviation "Chemical_Status_list \<equiv> enum_Chemical_Status_inst.enum_Chemical_Status"
abbreviation "Chemical_Status_set \<equiv> set Chemical_Status_list"

enumtype Chemical_Angle = 
  Chemical_Angle_Left | Chemical_Angle_Right | 
  Chemical_Angle_Back | Chemical_Angle_Front

abbreviation "Chemical_Angle_list \<equiv> enum_Chemical_Angle_inst.enum_Chemical_Angle"
abbreviation "Chemical_Angle_set \<equiv> set Chemical_Angle_list"

text \<open> The angle function \<close>
definition Chemical_angle :: "nat \<Rightarrow> Chemical_Angle" where
"Chemical_angle x = (if x > 0 then Chemical_Angle_Right else Chemical_Angle_Front)"

record 'a Chemical_GasSensor = 
  c :: "'a Chemical_Chem"
  i :: "'a Chemical_Intensity"

type_synonym Chemical_GasSensor2 = "2 Chemical_GasSensor"

definition Chemical_GasSensor2_list :: "Chemical_GasSensor2 list" where 
"Chemical_GasSensor2_list \<equiv> 
  [\<lparr>c = cc, i = ii\<rparr>. cc \<leftarrow> Chemical_Chem2_list, ii \<leftarrow> Chemical_Intensity2_list]"

abbreviation "lseq_gassensor_enum \<equiv> mk_blist TYPE(2) Chemical_GasSensor2_list"

(*
function Chemical_analysis :: "2 Chemical_GasSensor[2]blist \<Rightarrow> Chemical_Status" where
"Chemical_analysis (bmake TYPE(2) []) =  Chemical_Status_noGas" |
"Chemical_analysis (bmake TYPE(2) (p#ps)) = 
  (if Chemical_Chem_is_zero (c p) \<and> (Chemical_analysis (bmake TYPE(2) ps) = Chemical_Status_noGas) 
   then Chemical_Status_noGas else Chemical_Status_gasD)"
     apply (auto)
*)

function Chemical_analysis :: "2 Chemical_GasSensor[2]blist \<Rightarrow> Chemical_Status" where
"Chemical_analysis (gs) = 
  (case list_of_blist gs of
    []      \<Rightarrow> Chemical_Status_noGas |
    (p#ps)  \<Rightarrow> (if Chemical_Chem_is_zero (c p) \<and> 
                  (Chemical_analysis (bmake TYPE(2) ps) = Chemical_Status_noGas) 
                then Chemical_Status_noGas
                else Chemical_Status_gasD)
  )"
  by auto

termination Chemical_analysis 
  apply (relation "measure (\<lambda> gs. blength gs)")
  apply (auto)
proof -
  fix gs::"2 Chemical_GasSensor [2]blist" and 
      x21::"2 Chemical_GasSensor" and 
      x22::"2 Chemical_GasSensor list"
  assume a1: "list_of_blist gs = x21 # x22"
  from a1 have f1: "blength gs > 0"
    by (simp add: blength_def)
  show "blength (bmake TYPE(2) x22) < blength gs"
    by (metis a1 blist_remove_head f1 list.sel(3))
qed

value "Chemical_analysis (bmake TYPE(2) [])"
value "Chemical_analysis (bmake TYPE(2) [\<lparr>c = Chemical_ChemC (0::2), i = Chemical_IntensityC (0::2)\<rparr>])"

text \<open> The intensity function \<close>
definition pre_Chemical_intensity :: "2 Chemical_GasSensor[2]blist \<Rightarrow> bool" where
"pre_Chemical_intensity gs = (blength gs > 0)"

function Chemical_intensity :: "2 Chemical_GasSensor[2]blist \<Rightarrow> (2 Chemical_Intensity)" where
"Chemical_intensity (gs) = 
  (case list_of_blist gs of
    []      \<Rightarrow> Chemical_IntensityC (0::2) |
    (p#ps)  \<Rightarrow> (if Chemical_goreq (i p) (Chemical_intensity (bmake TYPE(2) ps)) 
                then i p
                else Chemical_intensity (bmake TYPE(2) ps))
  )"
  by auto

termination Chemical_intensity 
  apply (relation "measure (\<lambda> gs. blength gs)")
  apply (auto)
  by (metis add_Suc_right blength.rep_eq blist_remove_head less_nat_zero_code linorder_cases 
      list.sel(3) list.size(4) nat.simps(3))+

value "Chemical_intensity (bmake TYPE(2) [])"
value "Chemical_intensity (bmake TYPE(2) 
  [\<lparr>c = Chemical_ChemC (0::2), i = Chemical_IntensityC (1::2)\<rparr>,
   \<lparr>c = Chemical_ChemC (1::2), i = Chemical_IntensityC (0::2)\<rparr>])"

text \<open> The location function \<close>
definition pre_Chemical_location :: "2 Chemical_GasSensor[2]blist \<Rightarrow> bool" where
"pre_Chemical_location gs = (blength gs > 0)"

function Chemical_location' :: "2 Chemical_GasSensor[2]blist \<Rightarrow> nat \<Rightarrow> (Chemical_Angle)" where
"Chemical_location' (gs) x = 
  (case list_of_blist gs of
    []      \<Rightarrow> Chemical_angle(x) |
    (p#ps)  \<Rightarrow> (if (i p) = (Chemical_intensity (gs))
                then Chemical_angle(x)
                else Chemical_location' (bmake TYPE(2) ps) (x+1)
               )
  )"
  by auto

termination Chemical_location'
  apply (relation "measure (\<lambda> (gs, n). blength gs)")
  apply (auto)
  by (metis add_Suc_right blength.rep_eq blist_remove_head less_nat_zero_code linorder_cases 
      list.sel(3) list.size(4) nat.simps(3))+

abbreviation "Chemical_location gs \<equiv> Chemical_location' gs 0"

value "Chemical_location (bmake TYPE(2) [])"
value "Chemical_location (bmake TYPE(2) 
  [\<lparr>c = Chemical_ChemC (0::2), i = Chemical_IntensityC (0::2)\<rparr>,
   \<lparr>c = Chemical_ChemC (1::2), i = Chemical_IntensityC (1::2)\<rparr>])"

subsection \<open> Location package \<close>
enumtype Location_Loc = 
  Location_Loc_left | Location_Loc_right | Location_Loc_front

subsection \<open> GasAnalysis \<close>
definition "const_GasAnalysis_thr \<equiv> Chemical_IntensityC (1::2)"

enumtype SIDS_GasAnalysis = SID_GasAnalysis
	              | SID_GasAnalysis_NoGas
	              | SID_GasAnalysis_Analysis
	              | SID_GasAnalysis_GasDetected
	              | SID_GasAnalysis_j1
	              | SID_GasAnalysis_Reading

definition "SIDS_GasAnalysis_list = enum_SIDS_GasAnalysis_inst.enum_SIDS_GasAnalysis"
definition "SIDS_GasAnalysis_set = set SIDS_GasAnalysis_list"
definition "SIDS_GasAnalysis_nodes = (removeAll SID_GasAnalysis SIDS_GasAnalysis_list)"
definition "SIDS_GasAnalysis_no_NoGas = (removeAll SID_GasAnalysis_NoGas SIDS_GasAnalysis_list)"
definition "SIDS_GasAnalysis_no_Analysis = (removeAll SID_GasAnalysis_Analysis SIDS_GasAnalysis_list)"
definition "SIDS_GasAnalysis_no_GasDetected = (removeAll SID_GasAnalysis_GasDetected SIDS_GasAnalysis_list)"
definition "SIDS_GasAnalysis_no_Reading = (removeAll SID_GasAnalysis_Reading SIDS_GasAnalysis_list)"
definition "SIDS_GasAnalysis_no_j1 = (removeAll SID_GasAnalysis_j1 SIDS_GasAnalysis_list)"

enumtype TIDS_GasAnalysis = NULLTRANSITION__GasAnalysis
	              | TID_GasAnalysis_t1
	              | TID_GasAnalysis_t2
	              | TID_GasAnalysis_t3
	              | TID_GasAnalysis_t4
	              | TID_GasAnalysis_t8
	              | TID_GasAnalysis_t9a
	              | TID_GasAnalysis_t0

definition "TIDS_GasAnalysis_list = enum_TIDS_GasAnalysis_inst.enum_TIDS_GasAnalysis"
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
  get_gs_GasAnalysis :: "2 Chemical_GasSensor[2]blist" (* "Chemical_GasSensor LSeq"*)
  set_gs_GasAnalysis :: "2 Chemical_GasSensor[2]blist"
  get_i_GasAnalysis :: "2 Chemical_Intensity"
  set_i_GasAnalysis :: "2 Chemical_Intensity"
  get_a_GasAnalysis :: "Chemical_Angle"
  set_a_GasAnalysis :: "Chemical_Angle"

(* event channels *)
  gas__GasAnalysis :: "TIDS_GasAnalysis \<times> InOut \<times> 2 Chemical_GasSensor[2]blist"
  gas_GasAnalysis :: "InOut \<times> 2 Chemical_GasSensor[2]blist"
  resume__GasAnalysis :: "TIDS_GasAnalysis \<times> InOut"
  resume_GasAnalysis :: "InOut"
  turn__GasAnalysis :: "TIDS_GasAnalysis \<times> InOut \<times> Chemical_Angle"
  turn_GasAnalysis :: "InOut \<times> Chemical_Angle"
  stop__GasAnalysis :: "TIDS_GasAnalysis \<times> InOut"
  stop_GasAnalysis :: "InOut"

subsubsection \<open> Sets of events \<close>
(* How to use a list to represent all possible values of Chemical_GasSensor[2]blist *)
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
text \<open> Memory cell processes \<close>

(* for the local variable x *)
definition GasAnalysis_Memory_opt_gs where
"GasAnalysis_Memory_opt_gs = 
  mem_of_lvar get_gs_GasAnalysis set_gs_GasAnalysis 
    (set (lseq_gassensor_enum))"

definition GasAnalysis_Memory_opt_a where
"GasAnalysis_Memory_opt_a = mem_of_lvar get_a_GasAnalysis set_a_GasAnalysis Chemical_Angle_set"

definition GasAnalysis_Memory_opt_i where
"GasAnalysis_Memory_opt_i = mem_of_lvar get_i_GasAnalysis set_i_GasAnalysis (Chemical_Intensity2_set)"

definition GasAnalysis_Memory_opt_st where
"GasAnalysis_Memory_opt_st = mem_of_lvar get_st_GasAnalysis set_st_GasAnalysis (Chemical_Status_set)"

text \<open> Memory transition processes \<close>
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
        do {guard (st = Chemical_Status_gasD); outp internal_GasAnalysis TID_GasAnalysis_t4 ; Ret (id)} \<box>
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
paragraph \<open> Initial \<close>
definition I_GasAnalysis_i1 where
"I_GasAnalysis_i1 = (\<lambda> (id::integer) . 
  do {outp internal_GasAnalysis TID_GasAnalysis_t1 ; 
      outp enter_GasAnalysis (SID_GasAnalysis, SID_GasAnalysis_NoGas);
      outp entered_GasAnalysis (SID_GasAnalysis, SID_GasAnalysis_NoGas)
  })
"

paragraph \<open> NoGas \<close>
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
        \<comment> \<open> State_GasAnalysis_NoGas_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_GasAnalysis (snd (snd s), SID_GasAnalysis_NoGas);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_GasAnalysis_t2 \<close>
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

paragraph \<open> Analysis \<close>
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
        \<comment> \<open> State_GasAnalysis_Analysis_execute \<close>
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
                \<comment> \<open> T_GasAnalysis_t3 \<close>
                do {outp internal_GasAnalysis TID_GasAnalysis_t3 ;
                    outp exit_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_Analysis);
                    outp exited_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_Analysis);
                    outp resume_GasAnalysis dout;
                    outp enter_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_NoGas);
                    outp entered_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_NoGas);
                    Ret(False, fst (snd s), SID_GasAnalysis_Analysis)
                    } \<box>
                \<comment> \<open> T_GasAnalysis_t4 \<close>
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
   (discard_state (State_GasAnalysis_Analysis idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_GasAnalysis - GasAnalysis_Analysis_triggers) \<^esub> 
   skip
"

paragraph \<open> GasDetected \<close>
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
        \<comment> \<open> State_GasAnalysis_GasDetected_execute \<close>
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
                \<comment> \<open> T_GasAnalysis_t8 \<close>
                do {outp internal_GasAnalysis TID_GasAnalysis_t8 ;
                    outp exit_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_GasDetected);
                    outp exited_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_GasDetected);
                    outp stop_GasAnalysis dout;
                    outp enter_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_j1);
                    outp entered_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_j1);
                    Ret(False, fst (snd s), SID_GasAnalysis_GasDetected)
                    } \<box>
                 \<comment> \<open> T_GasAnalysis_t9a \<close>
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

paragraph \<open> Final \<close>
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
   (discard_state (State_GasAnalysis_j1 idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_GasAnalysis - GasAnalysis_j1_triggers) \<^esub> 
   skip
"

paragraph \<open> Reading \<close>
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
        \<comment> \<open> State_GasAnalysis_Reading_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_GasAnalysis (snd (snd s), SID_GasAnalysis_Reading);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_GasAnalysis_t0 \<close>
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
   (discard_state (State_GasAnalysis_Reading idd)) \<comment> \<open> discard state to match with skip on the right\<close>
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
      \<parallel>\<^bsub> CS_GasAnalysis_Analysis_sync \<inter> (CS_GasAnalysis_Analysis_sync \<union> 
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
  set ((enumchans1 [internal_GasAnalysis_C] [TID_GasAnalysis_t8, TID_GasAnalysis_t9a])
)"

definition MemorySTM_opt_GasAnalysis where
"MemorySTM_opt_GasAnalysis (idd::integer) = 
  (par_hide
    (discard_state (GasAnalysis_Memory_opt_i (Chemical_IntensityC (0::2))))
    GasAnalysis_i_events
    (par_hide 
      (par_hide
        (discard_state (GasAnalysis_Memory_opt_st (Chemical_Status_noGas)))
        GasAnalysis_st_events
        (hide 
          (
            (hide
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
              )
              ({internal_GasAnalysis_C TID_GasAnalysis_t1})
            )
            \<parallel>\<^bsub> GasAnalysis_opt_1_internal_set \<^esub> 
            (discard_state (GasAnalysis_MemoryTransitions_opt_1 idd))
          )
          (set (enumchans1 [internal_GasAnalysis_C] [TID_GasAnalysis_t4, TID_GasAnalysis_t3]))
        )
      )
      GasAnalysis_opt_2_internal_set
      (discard_state (GasAnalysis_MemoryTransitions_opt_2 idd))
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

term "\<lbrace>resume__GasAnalysis (t, x) \<mapsto> resume_GasAnalysis x | x. x \<in> InOut_set\<rbrace>"
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
  rename (set (rename_GasAnalysis_events @ rename_GasAnalysis_events_others)) 
    (MemorySTM_opt_GasAnalysis idd)
"

definition AUX_opt_GasAnalysis where
"AUX_opt_GasAnalysis (idd::integer) = 
  (hide 
    ( 
      (rename_MemorySTM_opt_GasAnalysis idd) \<lbrakk> set [terminate_GasAnalysis_C ()] \<Zrres> skip
    )
    GasAnalysis_MachineInternalEvents
  )
"

definition D__GasAnalysis where
"D__GasAnalysis (idd::integer) = 
  hide (AUX_opt_GasAnalysis idd) internal_events_GasAnalysis
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

definition rename_MainCtrl_GasAnalysis_events where
"rename_MainCtrl_GasAnalysis_events = 
  (enumchanp2_1 (terminate_GasAnalysis_C,terminate_MainCtrl_C) [()]) @
  (enumchansp2_2 [(gas_GasAnalysis_C, gas_MainCtrl_C)] InOut_list lseq_gassensor_enum) @
  (enumchansp2_1 [(resume_GasAnalysis_C, resume_MainCtrl_C)] InOut_list) @
  (enumchansp2_2 [(turn_GasAnalysis_C, turn_MainCtrl_C)] InOut_list Chemical_Angle_list) @
  (enumchansp2_1 [(stop_GasAnalysis_C, stop_MainCtrl_C)] InOut_list)
"

definition rename_D__GasAnalysis where
  "rename_D__GasAnalysis idd = rename (set rename_MainCtrl_GasAnalysis_events) (D__GasAnalysis idd)"

definition D__MainCtrl where
"D__MainCtrl (idd::integer) = 
  (par_hide
    (rename_D__GasAnalysis idd)
    {}
    (discard_state (Memory_MainCtrl idd))
  )  \<lbrakk> set [terminate_MainCtrl_C ()] \<Zrres> skip
"

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

enumtype TIDS_Movement = NULLTRANSITION__Movement
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

definition "TIDS_Movement_list = enum_TIDS_Movement_inst.enum_TIDS_Movement"
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
  gas__Movement :: "TIDS_Movement \<times> InOut \<times> 2 Chemical_GasSensor[2]blist"
  gas_Movement :: "InOut \<times> 2 Chemical_GasSensor[2]blist"
  resume__Movement :: "TIDS_Movement \<times> InOut"
  resume_Movement :: "InOut"
  turn__Movement :: "TIDS_Movement \<times> InOut \<times> Chemical_Angle"
  turn_Movement :: "InOut \<times> Chemical_Angle"
  stop__Movement :: "TIDS_Movement \<times> InOut"
  stop_Movement :: "InOut"

subsubsection \<open> Sets of events \<close>
(* How to use a list to represent all possible values of Chemical_GasSensor[2]blist *)
definition int_int_Movement where
"int_int_Movement = set (
  (enumchans3 [gas__Movement_C] 
    [TID_Movement_t0, TID_Movement_t2, 
     TID_Movement_t3, TID_Movement_t4,
     TID_Movement_t8, TID_Movement_t9a] 
    [din, dout] 
    (lseq_gassensor_enum)) @
  (enumchans2 [resume__Movement_C] 
    [TID_Movement_t0, TID_Movement_t2, 
     TID_Movement_t3, TID_Movement_t4,
     TID_Movement_t8, TID_Movement_t9a] 
    [din, dout]) @
  (enumchans3 [turn__Movement_C] 
    [TID_Movement_t0, TID_Movement_t2, 
     TID_Movement_t3, TID_Movement_t4,
     TID_Movement_t8, TID_Movement_t9a] 
    [din, dout]
    Chemical_Angle_list
    ) @
  (enumchans2 [stop__Movement_C] 
    [TID_Movement_t0, TID_Movement_t2, 
     TID_Movement_t3, TID_Movement_t4,
     TID_Movement_t8, TID_Movement_t9a] 
    [din, dout]  
    ) @
  (enumchan1 internal_Movement_C 
    [TID_Movement_t0, TID_Movement_t2, 
     TID_Movement_t3, TID_Movement_t4,
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
text \<open> Memory cell processes \<close>

(* for the local variable x *)
definition GasAnalysis_Memory_opt_gs where
"GasAnalysis_Memory_opt_gs = 
  mem_of_lvar get_gs_GasAnalysis set_gs_GasAnalysis 
    (set (lseq_gassensor_enum))"

definition GasAnalysis_Memory_opt_a where
"GasAnalysis_Memory_opt_a = mem_of_lvar get_a_GasAnalysis set_a_GasAnalysis Chemical_Angle_set"

definition GasAnalysis_Memory_opt_i where
"GasAnalysis_Memory_opt_i = mem_of_lvar get_i_GasAnalysis set_i_GasAnalysis (Chemical_Intensity2_set)"

definition GasAnalysis_Memory_opt_st where
"GasAnalysis_Memory_opt_st = mem_of_lvar get_st_GasAnalysis set_st_GasAnalysis (Chemical_Status_set)"

text \<open> Memory transition processes \<close>
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
        do {guard (st = Chemical_Status_gasD); outp internal_GasAnalysis TID_GasAnalysis_t4 ; Ret (id)} \<box>
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
paragraph \<open> Initial \<close>
definition I_GasAnalysis_i1 where
"I_GasAnalysis_i1 = (\<lambda> (id::integer) . 
  do {outp internal_GasAnalysis TID_GasAnalysis_t1 ; 
      outp enter_GasAnalysis (SID_GasAnalysis, SID_GasAnalysis_NoGas);
      outp entered_GasAnalysis (SID_GasAnalysis, SID_GasAnalysis_NoGas)
  })
"

paragraph \<open> NoGas \<close>
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
        \<comment> \<open> State_GasAnalysis_NoGas_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_GasAnalysis (snd (snd s), SID_GasAnalysis_NoGas);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_GasAnalysis_t2 \<close>
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

paragraph \<open> Analysis \<close>
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
        \<comment> \<open> State_GasAnalysis_Analysis_execute \<close>
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
                \<comment> \<open> T_GasAnalysis_t3 \<close>
                do {outp internal_GasAnalysis TID_GasAnalysis_t3 ;
                    outp exit_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_Analysis);
                    outp exited_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_Analysis);
                    outp resume_GasAnalysis dout;
                    outp enter_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_NoGas);
                    outp entered_GasAnalysis (SID_GasAnalysis_Analysis, SID_GasAnalysis_NoGas);
                    Ret(False, fst (snd s), SID_GasAnalysis_Analysis)
                    } \<box>
                \<comment> \<open> T_GasAnalysis_t4 \<close>
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
   (discard_state (State_GasAnalysis_Analysis idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_GasAnalysis - GasAnalysis_Analysis_triggers) \<^esub> 
   skip
"

paragraph \<open> GasDetected \<close>
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
        \<comment> \<open> State_GasAnalysis_GasDetected_execute \<close>
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
                \<comment> \<open> T_GasAnalysis_t8 \<close>
                do {outp internal_GasAnalysis TID_GasAnalysis_t8 ;
                    outp exit_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_GasDetected);
                    outp exited_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_GasDetected);
                    outp stop_GasAnalysis dout;
                    outp enter_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_j1);
                    outp entered_GasAnalysis (SID_GasAnalysis_GasDetected, SID_GasAnalysis_j1);
                    Ret(False, fst (snd s), SID_GasAnalysis_GasDetected)
                    } \<box>
                 \<comment> \<open> T_GasAnalysis_t9a \<close>
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

paragraph \<open> Final \<close>
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
   (discard_state (State_GasAnalysis_j1 idd)) \<comment> \<open> discard state to match with skip on the right\<close>
    \<parallel>\<^bsub> (int_int_GasAnalysis - GasAnalysis_j1_triggers) \<^esub> 
   skip
"

paragraph \<open> Reading \<close>
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
        \<comment> \<open> State_GasAnalysis_Reading_execute \<close>
        (iterate 
           \<comment> \<open> condition \<close>
           (\<lambda> s. fst s) 
           \<comment> \<open> P \<close>
           (\<lambda> s.
            do {
              outp entered_GasAnalysis (snd (snd s), SID_GasAnalysis_Reading);
              (do {skip ; stop} \<triangle>
                (
                \<comment> \<open> T_GasAnalysis_t0 \<close>
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
   (discard_state (State_GasAnalysis_Reading idd)) \<comment> \<open> discard state to match with skip on the right\<close>
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
      \<parallel>\<^bsub> CS_GasAnalysis_Analysis_sync \<inter> (CS_GasAnalysis_Analysis_sync \<union> 
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
  set ((enumchans1 [internal_GasAnalysis_C] [TID_GasAnalysis_t8, TID_GasAnalysis_t9a])
)"

definition MemorySTM_opt_GasAnalysis where
"MemorySTM_opt_GasAnalysis (idd::integer) = 
  (par_hide
    (discard_state (GasAnalysis_Memory_opt_i (Chemical_IntensityC (0::2))))
    GasAnalysis_i_events
    (par_hide 
      (par_hide
        (discard_state (GasAnalysis_Memory_opt_st (Chemical_Status_noGas)))
        GasAnalysis_st_events
        (hide 
          (
            (hide
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
              )
              ({internal_GasAnalysis_C TID_GasAnalysis_t1})
            )
            \<parallel>\<^bsub> GasAnalysis_opt_1_internal_set \<^esub> 
            (discard_state (GasAnalysis_MemoryTransitions_opt_1 idd))
          )
          (set (enumchans1 [internal_GasAnalysis_C] [TID_GasAnalysis_t4, TID_GasAnalysis_t3]))
        )
      )
      GasAnalysis_opt_2_internal_set
      (discard_state (GasAnalysis_MemoryTransitions_opt_2 idd))
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

term "\<lbrace>resume__GasAnalysis (t, x) \<mapsto> resume_GasAnalysis x | x. x \<in> InOut_set\<rbrace>"
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
  rename (set (rename_GasAnalysis_events @ rename_GasAnalysis_events_others)) 
    (MemorySTM_opt_GasAnalysis idd)
"

definition AUX_opt_GasAnalysis where
"AUX_opt_GasAnalysis (idd::integer) = 
  (hide 
    ( 
      (rename_MemorySTM_opt_GasAnalysis idd) \<lbrakk> set [terminate_GasAnalysis_C ()] \<Zrres> skip
    )
    GasAnalysis_MachineInternalEvents
  )
"

definition D__GasAnalysis where
"D__GasAnalysis (idd::integer) = 
  hide (AUX_opt_GasAnalysis idd) internal_events_GasAnalysis
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

definition rename_MainCtrl_GasAnalysis_events where
"rename_MainCtrl_GasAnalysis_events = 
  (enumchanp2_1 (terminate_GasAnalysis_C,terminate_MainCtrl_C) [()]) @
  (enumchansp2_2 [(gas_GasAnalysis_C, gas_MainCtrl_C)] InOut_list lseq_gassensor_enum) @
  (enumchansp2_1 [(resume_GasAnalysis_C, resume_MainCtrl_C)] InOut_list) @
  (enumchansp2_2 [(turn_GasAnalysis_C, turn_MainCtrl_C)] InOut_list Chemical_Angle_list) @
  (enumchansp2_1 [(stop_GasAnalysis_C, stop_MainCtrl_C)] InOut_list)
"

definition rename_D__GasAnalysis where
  "rename_D__GasAnalysis idd = rename (set rename_MainCtrl_GasAnalysis_events) (D__GasAnalysis idd)"

definition D__MainCtrl where
"D__MainCtrl (idd::integer) = 
  (par_hide
    (rename_D__GasAnalysis idd)
    {}
    (discard_state (Memory_MainCtrl idd))
  )  \<lbrakk> set [terminate_MainCtrl_C ()] \<Zrres> skip
"

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
  MemorySTM_opt_GasAnalysis
  AUX_opt_GasAnalysis
  D__GasAnalysis
in Haskell 
  (* module_name GasAnalysis *)
  file_prefix RoboChart_ChemicalDetector 
  (string_classes) 




subsection \<open> Module \<close>
chantype Chan_mod0 =
(* terminates of MainCtrl are mapped to it *)
  terminate_mod0 :: unit 
(* variable channels: set_x and get_x of GasAnalysis and stm1 are mapped to these channels *)
  set_x_mod0 :: core_int
  get_x_mod0 :: core_int
(* shared variable channels *)
  set_EXT_x_mod0_MainCtrl :: core_int
(* e1 of GasAnalysis is mapped to it *)
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
  GasAnalysis_Memory_opt_x
  GasAnalysis_Memory_opt_l
  GasAnalysis_MemoryTransitions_opt_0
  GasAnalysis_MemoryTransitions_opt_1
  I_GasAnalysis_i0
  State_GasAnalysis_s0
  State_GasAnalysis_s0_R
  STM_GasAnalysis
  MemorySTM_opt_GasAnalysis 
  rename_MemorySTM_opt_GasAnalysis
  D__GasAnalysis 
  stm1_Memory_opt_x
  stm1_MemoryTransitions_opt_0
  I_stm1_i0
  State_stm1_s0
  State_stm1_s0_R
  STM_stm1
  MemorySTM_opt_stm1
  D__stm1
  rename_D__GasAnalysis
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
