theory BoxOffice
  imports "../ITree_Circus"
begin lit_vars

type_synonym SEAT = integer
type_synonym CUSTOMER = String.literal

alphabet BoxOffice = 
  seating :: "SEAT set"
  sold :: "SEAT \<Zpfun> CUSTOMER"

instantiation BoxOffice_ext :: (default) default
begin
  definition default_BoxOffice_ext :: "'a BoxOffice_scheme" where
    "default_BoxOffice_ext = BoxOffice.extend (BoxOffice.make {} {}\<^sub>p) default"

instance ..
end

definition BoxOfficeInit :: "integer set \<Rightarrow> BoxOffice subst" where
"BoxOfficeInit initalloc = [seating \<leadsto> initalloc, sold \<leadsto> {}\<^sub>p]"

chantype chan =
  purchase :: "SEAT \<times> CUSTOMER"
  return :: "SEAT \<times> CUSTOMER"

definition Purchase0 :: "_ \<Rightarrow> _ \<Rightarrow> (chan, BoxOffice) action" where
"Purchase0 SEAT CUSTOMER = 
  purchase?(s, c):({s \<in> SEAT. s \<notin> pdom(sold)} \<times> CUSTOMER) \<rightarrow> sold := (sold + {s \<mapsto> c}\<^sub>p)"

definition Return0 :: "_ \<Rightarrow> _ \<Rightarrow> (chan, BoxOffice) action" where
"Return0 SEAT CUSTOMER =
  return?(s, c):pfun_graph(sold) \<rightarrow> sold := ({s} \<Zndres> sold)"

definition "BoxOffice initalloc SEAT CUSTOMER
  = proc 
      (BoxOfficeInit initalloc)
      (loop (Purchase0 SEAT CUSTOMER \<box> Return0 SEAT CUSTOMER))"

export_code BoxOffice in Haskell module_name BoxOffice (string_classes)


end