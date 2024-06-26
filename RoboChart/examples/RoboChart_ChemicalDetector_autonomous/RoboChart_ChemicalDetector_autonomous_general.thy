section \<open> Introduction \<close>
text \<open> This theory aims for animation of the autonomous chemical detector RoboChart model 
(Version 3.0)
\footnote{
@{url "https://robostar.cs.york.ac.uk/case_studies/autonomous-chemical-detector/autonomous-chemical-detector.html#version3"}
}
based on its CSP semantics. This model is obsolete and cannot be supported in the current 
RoboTool v2.0, and so we have updated it. The update includes 
\begin{itemize}
  \item a correction (@{verbatim "result==gs[x].gs_i"} to @{verbatim "result==gs[y].gs_i"}) of an error 
    in the definition of the @{text intensity} function, 
  \item a removal of the unnecessary transition (with trigger @{text "resume"}) from 
    @{text Avoiding} to @{text Going} in the @{text Movement} state machine, and 
  \item other changes are minor.
\end{itemize}
\<close>

text \<open> 
The complete model is displayed in Figs.~\ref{fig:robochart_autonomous_module}-
\ref{fig:robochart_autonomous_movement}.
﻿\begin{figure}
	\centering
  \includegraphics[scale=0.75]{images/Module.pdf}
  \caption{The RoboChart model of an autonomous chemical detector example}
  \label{fig:robochart_autonomous_module}
\end{figure}

\begin{figure}
	\centering
  \includegraphics[scale=0.80]{images/Chemical.pdf}
  \caption{The Chemical package}
  \label{fig:robochart_autonomous_chemical}
\end{figure}

\begin{figure}
	\centering
  \includegraphics[scale=1.0]{images/Location.pdf}
  \caption{The Location package}
  \label{fig:robochart_autonomous_location}
\end{figure}

\begin{figure}
	\centering
  \includegraphics[scale=1.0]{images/MainController.pdf}
  \caption{The MainController package}
  \label{fig:robochart_autonomous_maincontroller}
\end{figure}

\begin{figure}
	\centering
  \includegraphics[scale=0.8]{images/GasAnalysis.pdf}
  \caption{The GasAnalysis state machine}
  \label{fig:robochart_autonomous_gasanalysis}
\end{figure}

\begin{figure}
	\centering
  \includegraphics[scale=0.9]{images/MicroController.pdf}
  \caption{The MicroController package}
  \label{fig:robochart_autonomous_microcontroller}
\end{figure}

\begin{figure}
	\centering
  \includegraphics[scale=0.45]{images/Movement.pdf}
  \caption{The Movement state machine}
  \label{fig:robochart_autonomous_movement}
\end{figure}
\<close>

text \<open>We structure the theory as follows. In Sect.~\ref{sec:chem_general}, we give the general 
definitions. Sects.~\ref{ssec:chem_chemical} and~\ref{ssec:chem_location} define types and 
functions in the @{text Chemical} and @{text Location} packages of the model. 
Two controllers are defined in Sects.~\ref{sec:chem_maincontroller} and 
\ref{sec:chem_microcontroller}.
The @{text GasAnalysis} state machine and the @{text MainController} controller are defined in 
Sects.~\ref{ssec:chem_gasanalysis} and~\ref{ssec:chem_maincontroller}. Then we give an overview of 
the @{text MicroController} in Sect.~\ref{ssec:chem_movement_overview}, present general 
definitions of the @{text Movement} state machine, including the state machine defined operation 
@{text changeDirection}, in Sect.~\ref{ssec:chem_movement_general}. 
Afterwards, the operation and @{text Movement} are defined in 
Sects.~\ref{ssec:chem_changedirection_op} and~\ref{ssec:chem_movement}, and @{text MicroController} 
is defined in Sect.~\ref{ssec:chem_microcontroller}. Finally, the module @{text mod0} is defined in 
Sect.~\ref{sec:chem_module}.
\<close>

section \<open> General definitions \label{sec:chem_general}\<close>

theory RoboChart_ChemicalDetector_autonomous_general
  imports "ITree_RoboChart.ITree_RoboChart" 
          "ITree_Simulation.ITree_Simulation"
          "ITree_RoboChart.RoboChart_Simulation"
          "Z_Toolkit.Bounded_List"
begin

text \<open>The values below for the instantiation of @{term robochart_confs} come from the 
@{verbatim "instantiation.csp"}.
\<close>
interpretation rc: robochart_confs "-2" "2" "2" "0" "1".

subsection \<open> Chemical package \label{ssec:chem_chemical}\<close>
text \<open> @{text Chem} from the @{text Chemical} package in the model is a @{text PrimitiveType}, 
similar to a given type in Z. 
In CSP, it is @{verbatim "nametype Chem = {0,1}"}. A named type in CSP simply associates a type 
name with a set of values. Therefore, a set of two integer numbers is chosen as a type for @{text Chem} 
in CSP. 
If we translate primitive types from the CSP code, we need to deal with set expressions, which is 
more complex, and also lose the information that @{text Chem} is a primitive type. For this reason,
the translation (no matter manual or automatic) should not be directly from the generated CSP code, 
and should start from RoboChart models.

Here, we introduce a generic way to define finite primitive types (as for model checking of CSP 
semantics). The type variable @{typ 'a} is finite, and such one example is the numeral type @{typ 2}
 (@{text "2 Chemical_Chem"}) which contains two elements: @{text "0::2"} and @{text "1::2"}. 
And @{text "2::2"} is just equal to @{text "0::2"}.

Similar to the CSP representation of named types, the use of a numeral type for @{typ 'a} also 
enables the elements of this type can be compared.
\<close>
(*
datatype ('a::finite) Chemical_Chem = Chemical_ChemC 'a
*)
typedef Chemical_ChemT = "{()}" by auto
type_synonym ('a) Chemical_Chem = "(Chemical_ChemT, 'a) PrimType"
abbreviation Chemical_ChemC::"('a::finite \<Rightarrow> 'a Chemical_Chem)"
  where "Chemical_ChemC \<equiv> PrimTypeC"

text \<open>@{term Chemical_Chem2_set} corresponds to the named type @{verbatim Chem} in CSP. It is also a 
set contains two elements: 0 and 1, through an implementation of sets by lists 
(@{term Chemical_Chem2_list}). 
\<close>
(* abbreviation "Chemical_Chem2_list \<equiv> [Chemical_ChemC (0::2), Chemical_ChemC (1::2)]"*)
abbreviation "Chemical_Chem2_list \<equiv> enum_class.enum:: (2 Chemical_Chem) list"
\<comment> \<open> Use abbreviation (instead of definition) here, otherwise it cannot pattern match a list based 
set\<close>
abbreviation "Chemical_Chem2_set \<equiv> set Chemical_Chem2_list"

text \<open>For @{text Chem}, a value (@{text "0::2"}) denotes no gas detected. Otherwise, a gas is 
detected. 
\<close>
definition Chemical_Chem_is_zero::"(2 Chemical_Chem) \<Rightarrow> bool" where
"Chemical_Chem_is_zero x = (if x = (Chemical_ChemC (0::2)) then True else False)"

value "Chemical_Chem_is_zero (Chemical_ChemC (3::2))"

text \<open>The definition of the @{text Intensity} type is similar to that of @{text Chem}. \<close>
(* datatype ('a::finite) Chemical_Intensity = Chemical_IntensityC (un_intensity:'a) *)

typedef Chemical_IntensityT = "{()}" by auto
type_synonym ('a) Chemical_Intensity = "(Chemical_IntensityT, 'a) PrimType"
abbreviation Chemical_IntensityC::"('a::finite \<Rightarrow> 'a Chemical_Intensity)" 
  where "Chemical_IntensityC \<equiv> PrimTypeC"

(*abbreviation "Chemical_Intensity2_list \<equiv> [Chemical_IntensityC (0::2), Chemical_IntensityC 1]"*)
abbreviation "Chemical_Intensity2_list \<equiv> enum_class.enum::(2 Chemical_Intensity) list"
abbreviation "Chemical_Intensity2_set \<equiv> set Chemical_Intensity2_list"

definition Chemical_Intensity_is_zero::"(2 Chemical_Intensity) \<Rightarrow> bool" where
"Chemical_Intensity_is_zero x = (if x = (Chemical_IntensityC (0::2)) then True else False)"

text \<open>The use of a numeral type for a finite type in the definition of @{term Chemical_Intensity}, 
for example @{typ 2} here, makes the values in this type is comparable. \<close>
fun Chemical_goreq :: "2 Chemical_Intensity \<Rightarrow> 2 Chemical_Intensity \<Rightarrow> bool" where
"Chemical_goreq (Chemical_IntensityC x) (Chemical_IntensityC y) = (x \<ge> y) "

text \<open> In CSP, @{verbatim "LSeq(T,n)"} from @{verbatim "core_defs.csp"} can be used as a type or 
an expression. In this RoboChart model, it is used as a type, parametrised by $n$. We use 
@{theory Z_Toolkit.Bounded_List} to implement it, such as @{text "int blist[2]"} for 
@{verbatim "LSeq(int, 2)"}. 

The @{term "lseq s n"} function below gives a list of the all bounded lists of which each contains 
elements from the list @{term s} only and has its length equal to @{term n}. 
\<close>
fun lseq where
"lseq s 0 = [[]]" |
"lseq s (Suc 0) = [[q]. q \<leftarrow> s]" |
"lseq s (Suc n) = [q # qs. q \<leftarrow> s, qs \<leftarrow> (lseq s n)]"

text \<open>The @{term "lseqn s n"} function gives a list of the all bounded lists of which each contains 
elements from the list @{term s} only and has its length less than or equal to @{term n}. 
\<close>
fun lseqn where
"lseqn s 0 = lseq s 0" |
"lseqn s (Suc n) = lseqn s n @ (lseq s (Suc n))"

text \<open> The @{term "mk_blist n s"} defines a list of the all bounded lists from the supplied list 
@{text s}, a set of all possible elements, and the length of each bounded list is less than or equal 
to @{text n}.\<close>
definition mk_blist :: "'n itself \<Rightarrow> 'a list \<Rightarrow> ('a blist['n::finite]) list" where
"mk_blist _ xs = map (bmake TYPE('n)) (lseqn xs CARD('n))"

datatype Chemical_Status = 
  Chemical_Status_noGas | Chemical_Status_gasD

instantiation Chemical_Status :: enum
begin
definition enum_Chemical_Status :: "Chemical_Status list" where
"enum_Chemical_Status = [Chemical_Status_noGas, Chemical_Status_gasD]"

definition enum_all_Chemical_Status :: "(Chemical_Status \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_Chemical_Status P = (\<forall>b :: Chemical_Status \<in> set enum_class.enum. P b)"

definition enum_ex_Chemical_Status :: "(Chemical_Status \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_Chemical_Status P = (\<exists>b ::  Chemical_Status \<in> set enum_class.enum. P b)"

instance
proof (intro_classes)
  show "distinct (enum_class.enum :: Chemical_Status list)"
    by (simp add: enum_Chemical_Status_def)

  show univ_eq: "UNIV = set (enum_class.enum:: Chemical_Status list)"
    apply (simp add: enum_Chemical_Status_def)
    apply (auto simp add: enum_UNIV)
    by (meson Chemical_Status.exhaust)

  fix P :: "Chemical_Status \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P" 
    by (simp_all add: univ_eq enum_all_Chemical_Status_def enum_ex_Chemical_Status_def)
qed
end

(*abbreviation "Chemical_Status_list \<equiv> [Chemical_Status_noGas, Chemical_Status_gasD]"*)
abbreviation "Chemical_Status_list \<equiv> enum_class.enum :: Chemical_Status list"
abbreviation "Chemical_Status_set \<equiv> set Chemical_Status_list"

datatype Chemical_Angle = 
  Chemical_Angle_Left | Chemical_Angle_Right | 
  Chemical_Angle_Back | Chemical_Angle_Front

instantiation Chemical_Angle :: enum
begin
definition enum_Chemical_Angle :: "Chemical_Angle list" where
"enum_Chemical_Angle = [Chemical_Angle_Left, Chemical_Angle_Right,  Chemical_Angle_Back, 
  Chemical_Angle_Front]"

definition enum_all_Chemical_Angle :: "(Chemical_Angle \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_Chemical_Angle P = (\<forall>b :: Chemical_Angle \<in> set enum_class.enum. P b)"

definition enum_ex_Chemical_Angle :: "(Chemical_Angle \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_Chemical_Angle P = (\<exists>b ::  Chemical_Angle \<in> set enum_class.enum. P b)"

instance
proof (intro_classes)
  show "distinct (enum_class.enum :: Chemical_Angle list)"
    by (simp add: enum_Chemical_Angle_def)

  show univ_eq: "UNIV = set (enum_class.enum:: Chemical_Angle list)"
    apply (simp add: enum_Chemical_Angle_def)
    apply (auto simp add: enum_UNIV)
    by (meson Chemical_Angle.exhaust)

  fix P :: "Chemical_Angle \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P" 
    by (simp_all add: univ_eq enum_all_Chemical_Angle_def enum_ex_Chemical_Angle_def)
qed
end

(*abbreviation "Chemical_Angle_list \<equiv> [Chemical_Angle_Left, Chemical_Angle_Right,
  Chemical_Angle_Back, Chemical_Angle_Front]"*)
abbreviation "Chemical_Angle_list \<equiv> enum_class.enum :: Chemical_Angle list"
abbreviation "Chemical_Angle_set \<equiv> set Chemical_Angle_list"

definition Chemical_angle :: "nat \<Rightarrow> Chemical_Angle" where
"Chemical_angle x = (if x > 0 then Chemical_Angle_Right else Chemical_Angle_Front)"

record 'a Chemical_GasSensor = 
  gs_c :: "'a Chemical_Chem"
  gs_i :: "'a Chemical_Intensity"

type_synonym Chemical_GasSensor2 = "2 Chemical_GasSensor"

definition Chemical_GasSensor2_list :: "Chemical_GasSensor2 list" where 
"Chemical_GasSensor2_list \<equiv> 
  [\<lparr>gs_c = cc, gs_i = ii\<rparr>. cc \<leftarrow> Chemical_Chem2_list, ii \<leftarrow> Chemical_Intensity2_list]"

text \<open>The @{term lseq_gassensor_enum} defines a list of the all bounded lists of which each contains 
up to 2 records of type @{term Chemical_GasSensor2}.\<close>
abbreviation "lseq_gassensor_enum \<equiv> mk_blist TYPE(2) Chemical_GasSensor2_list"

text \<open>The function @{text analysis} is not specified in the original model, but an implemented is defined in 
the CSP semantics.
We give a specification for the function in the model and define below.\<close>
definition Chemical_analysis :: "2 Chemical_GasSensor blist[2] \<Rightarrow> Chemical_Status" where
"Chemical_analysis gs = (if blength gs > 0 
then (if (\<exists>x::nat < blength (gs). \<not> (Chemical_Chem_is_zero (gs_c (bnth gs x))))
      then Chemical_Status_gasD
      else Chemical_Status_noGas)
else Chemical_Status_noGas)"

(*
text \<open>An alternative definition of @{term Chemical_analysis} is based on the implementation. Since
it is defined as a general recursive function, we need to prove its termination. \<close>

function Chemical_analysis :: "2 Chemical_GasSensor blist[2] \<Rightarrow> Chemical_Status" where
"Chemical_analysis (gs) = 
  (case list_of_blist gs of
    []      \<Rightarrow> Chemical_Status_noGas |
    (p#ps)  \<Rightarrow> (if Chemical_Chem_is_zero (gs_c p) \<and> 
                  (Chemical_analysis (bmake TYPE(2) ps) = Chemical_Status_noGas) 
                then Chemical_Status_noGas
                else Chemical_Status_gasD)
  )"
  by auto

termination Chemical_analysis 
  apply (relation "measure (\<lambda> gs. blength gs)")
  apply (auto)
proof -
  fix gs::"2 Chemical_GasSensor blist[2]" and 
      x21::"2 Chemical_GasSensor" and 
      x22::"2 Chemical_GasSensor list"
  assume a1: "list_of_blist gs = x21 # x22"
  from a1 have f1: "blength gs > 0"
    by (simp add: blength_def)
  show "blength (bmake TYPE(2) x22) < blength gs"
    by (metis a1 blist_remove_head f1 list.sel(3))
qed
*)

(* We can also use pre- and post-conditions to define the analysis function. *)
(*
fun Chemical_analysis' :: "2 Chemical_GasSensor blist[2] \<Rightarrow> Chemical_Status" where
"Chemical_analysis' gs = "
*)

value "Chemical_analysis (bmake TYPE(2) [])"
value "Chemical_analysis (bmake TYPE(2) [\<lparr>gs_c = Chemical_ChemC (0::2), gs_i = Chemical_IntensityC (0::2)\<rparr>])"
value "Chemical_analysis (bmake TYPE(2) [\<lparr>gs_c = Chemical_ChemC (1::2), gs_i = Chemical_IntensityC (0::2)\<rparr>])"
value "Chemical_analysis (bmake TYPE(2) [
  \<lparr>gs_c = Chemical_ChemC (0::2), gs_i = Chemical_IntensityC (0::2)\<rparr>,
  \<lparr>gs_c = Chemical_ChemC (1::2), gs_i = Chemical_IntensityC (1::2)\<rparr>
])"

text \<open> The @{text intensity} function in the model is defined using precondition and postconditions. 
The precondition is evaluated by @{text pre_Chemical_intensity} and its postconditions are 
established by the function @{term Chemical_intensity} defined below. For this kind of function, 
the CSP semantics is 
@{verbatim "(pre_Chemical_intensity gs) & (a process with the expression (Chemical_intensity gs))"}. 
So if the preconditions is not satisfied, it deadlocks.
\<close>
definition pre_Chemical_intensity :: "2 Chemical_GasSensor blist[2] \<Rightarrow> bool" where
"pre_Chemical_intensity gs = (blength gs > 0)"

text \<open>The original model has a problem: @{text "x \<le> size(gs)"} is incorrect and it should be 
@{text "x < size(gs)"}. Following the model, the definition of this function will cause a problem 
when this function is called: @{verbatim "exception Match raised (line 595 of 'generated code')"}
\<close>
definition Chemical_intensity :: "2 Chemical_GasSensor blist[2] \<Rightarrow> (2 Chemical_Intensity)" where
"Chemical_intensity (gs) = (THE result. 
  (\<forall>x::nat < blength gs. Chemical_goreq result (gs_i (bnth gs x))) \<and>
  (\<exists>x::nat < blength gs. result = (gs_i (bnth gs x))))"

(* Error: gs must be not empty, otherwise bnth 
value "Chemical_intensity (bmake TYPE(2) [])"*)
value "Chemical_intensity (bmake TYPE(2) 
  [\<lparr>gs_c = Chemical_ChemC (0::2), gs_i = Chemical_IntensityC (1::2)\<rparr>,
   \<lparr>gs_c = Chemical_ChemC (1::2), gs_i = Chemical_IntensityC (0::2)\<rparr>])"

(*
text \<open>Alternative definition of the intensity function as a recursive function, and this is consistent 
with the implementation in RoboTool.\<close>
function Chemical_intensity' :: "2 Chemical_GasSensor blist[2] \<Rightarrow> (2 Chemical_Intensity)" where
"Chemical_intensity' (gs) = 
  (case list_of_blist gs of
    []      \<Rightarrow> Chemical_IntensityC (0::2) |
    (p#ps)  \<Rightarrow> (if Chemical_goreq (gs_i p) (Chemical_intensity' (bmake TYPE(2) ps)) 
                then gs_i p
                else Chemical_intensity' (bmake TYPE(2) ps))
  )"
  by auto

termination Chemical_intensity'
  apply (relation "measure (\<lambda> gs. blength gs)")
  apply (auto)
  by (metis add_Suc_right blength.rep_eq blist_remove_head less_nat_zero_code linorder_cases 
      list.sel(3) list.size(4) nat.simps(3))+

value "Chemical_intensity' (bmake TYPE(2) [])"
value "Chemical_intensity' (bmake TYPE(2) 
  [\<lparr>gs_c = Chemical_ChemC (0::2), gs_i = Chemical_IntensityC (1::2)\<rparr>,
   \<lparr>gs_c = Chemical_ChemC (1::2), gs_i = Chemical_IntensityC (0::2)\<rparr>])"
*)

text \<open> The definition of the @{text location} function in the model is similar to that of the 
@{text intensity} function.\<close>
definition pre_Chemical_location :: "2 Chemical_GasSensor blist[2] \<Rightarrow> bool" where
"pre_Chemical_location gs = (blength gs > 0)"

definition Chemical_location:: "2 Chemical_GasSensor blist[2] \<Rightarrow> Chemical_Angle" where
"Chemical_location gs = (THE result. \<exists>x::nat < blength gs. (
    Chemical_intensity(gs) = (gs_i (bnth gs x)) \<and>  
    (\<not> (\<exists>y::nat < x. Chemical_intensity(gs) = (gs_i (bnth gs y)))) \<and>
    (result = Chemical_angle(x)))
)"

(*
text \<open>An alternative definition of the function @{text "location"} \<close>
function Chemical_location' :: "2 Chemical_GasSensor blist[2] \<Rightarrow> nat \<Rightarrow> (Chemical_Angle)" where
"Chemical_location' (gs) x = 
  (case list_of_blist gs of
    []      \<Rightarrow> Chemical_angle(x) |
    (p#ps)  \<Rightarrow> (if (gs_i p) = (Chemical_intensity (gs))
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
*)
(* value "Chemical_location (bmake TYPE(2) [])" *)
value "Chemical_location (bmake TYPE(2) 
  [\<lparr>gs_c = Chemical_ChemC (0::2), gs_i = Chemical_IntensityC (1::2)\<rparr>,
   \<lparr>gs_c = Chemical_ChemC (1::2), gs_i = Chemical_IntensityC (1::2)\<rparr>])"
value "Chemical_location (bmake TYPE(2) 
  [\<lparr>gs_c = Chemical_ChemC (0::2), gs_i = Chemical_IntensityC (0::2)\<rparr>,
   \<lparr>gs_c = Chemical_ChemC (1::2), gs_i = Chemical_IntensityC (1::2)\<rparr>])"

subsection \<open> Location package \label{ssec:chem_location}\<close>
datatype Location_Loc = 
  Location_Loc_left | Location_Loc_right | Location_Loc_front

abbreviation "Location_Loc_list \<equiv> [Location_Loc_left, Location_Loc_right, Location_Loc_front]"
abbreviation "Location_Loc_set \<equiv> set Location_Loc_list"

end
