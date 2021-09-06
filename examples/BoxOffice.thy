theory BoxOffice
  imports "Interaction_Trees.ITree_Simulation"
begin lit_vars

unbundle Circus_Syntax

type_synonym SEAT = integer
type_synonym CUSTOMER = String.literal

consts initalloc :: "SEAT set"

consts SEAT :: "SEAT set"

consts CUSTOMER :: "CUSTOMER set"

schema BoxOffice = 
  seating :: "SEAT set"
  sold :: "SEAT \<Zpfun> CUSTOMER"
  where "pdom(sold) \<subseteq> seating"

record_default BoxOffice

definition BoxOfficeInit :: "BoxOffice subst" where
"BoxOfficeInit = [seating \<leadsto> initalloc, sold \<leadsto> {}\<^sub>p]"

chantype chan =
  purchase :: "SEAT \<times> CUSTOMER"
  ret :: "SEAT \<times> CUSTOMER"

definition Purchase0 :: "(chan, BoxOffice) action" where
"Purchase0 = 
  purchase?(s, c):((SEAT - pdom(sold)) \<times> CUSTOMER) \<rightarrow> sold := sold \<oplus> {s \<mapsto> c}\<^sub>p"

definition Return0 :: "(chan, BoxOffice) action" where
"Return0 =
  ret?(s, c):pfun_graph(sold) \<rightarrow> sold := {s} \<Zndres> sold"

definition "BoxOfficeProc
  = process 
      BoxOfficeInit
      (loop (Purchase0 \<box> Return0 ))"

def_const initalloc "SEAT"
def_const SEAT "set [0,1,2,3]"
def_const CUSTOMER "set [STR ''Simon'', STR ''Jim'', STR ''Christian'']"

simulate BoxOfficeProc

export_code BoxOfficeProc in Haskell module_name BoxOffice (string_classes)


end