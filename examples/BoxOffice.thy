theory BoxOffice
  imports "Interaction_Trees.ITree_Simulation"
begin lit_vars

type_synonym SEAT = integer
type_synonym CUSTOMER = String.literal

schema BoxOffice = 
  seating :: "SEAT set"
  sold :: "SEAT \<Zpfun> CUSTOMER"
  where "pdom(sold) \<subseteq> seating"

record_default BoxOffice

definition BoxOfficeInit :: "integer set \<Rightarrow> BoxOffice subst" where
"BoxOfficeInit initalloc = [seating \<leadsto> initalloc, sold \<leadsto> {}\<^sub>p]"

chantype chan =
  purchase :: "SEAT \<times> CUSTOMER"
  ret :: "SEAT \<times> CUSTOMER"

definition Purchase0 :: "_ \<Rightarrow> _ \<Rightarrow> (chan, BoxOffice) action" where
"Purchase0 SEAT CUSTOMER = 
  purchase?(s, c):({s \<in> SEAT. s \<notin> pdom(sold)} \<times> CUSTOMER) \<rightarrow> sold := sold + {s \<mapsto> c}\<^sub>p"

definition Return0 :: "_ \<Rightarrow> _ \<Rightarrow> (chan, BoxOffice) action" where
"Return0 SEAT CUSTOMER =
  ret?(s, c):pfun_graph(sold) \<rightarrow> sold := {s} \<Zndres> sold"

definition "BoxOfficeProc initalloc SEAT CUSTOMER
  = process 
      (BoxOfficeInit (set initalloc))
      (loop (Purchase0 (set SEAT) (set CUSTOMER) \<box> Return0 (set SEAT) (set CUSTOMER)))"

simulate BoxOfficeProc

export_code BoxOfficeProc in Haskell module_name BoxOffice (string_classes)


end