
theory RoboChart_ChemicalDetector_autonomous_general
  imports "../../../ITree_RoboChart" 
          "../../../Bounded_List"
begin

subsection \<open> General definitions \<close>
interpretation rc: robochart_confs "-2" "2" "2" "0" "1".

declare pfun_entries_alist [code]

subsubsection \<open> Constants \<close>

subsubsection \<open> Types \<close>

(* PrimitiveType in RoboChart like given types in Z, and instantiated in CSP *)

datatype ('a::finite) Chemical_Chem = Chemical_ChemC 'a

abbreviation "Chemical_Chem2_list \<equiv> [Chemical_ChemC (0::2), Chemical_ChemC (1::2)]"
\<comment> \<open> Use abbreviation (instead of definition) here, otherwise it cannot pattern match a list based 
set\<close>
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
datatype Chemical_Status = 
  Chemical_Status_noGas | Chemical_Status_gasD

abbreviation "Chemical_Status_list \<equiv> [Chemical_Status_noGas, Chemical_Status_gasD]"
abbreviation "Chemical_Status_set \<equiv> set Chemical_Status_list"

datatype Chemical_Angle = 
  Chemical_Angle_Left | Chemical_Angle_Right | 
  Chemical_Angle_Back | Chemical_Angle_Front

abbreviation "Chemical_Angle_list \<equiv> [Chemical_Angle_Left, Chemical_Angle_Right,
  Chemical_Angle_Back, Chemical_Angle_Front]"
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
datatype Location_Loc = 
  Location_Loc_left | Location_Loc_right | Location_Loc_front

abbreviation "Location_Loc_list \<equiv> [Location_Loc_left, Location_Loc_right, Location_Loc_front]"
abbreviation "Location_Loc_set \<equiv> set Location_Loc_list"

end
