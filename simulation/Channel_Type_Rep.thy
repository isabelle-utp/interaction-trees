theory Channel_Type_Rep
  imports Executable_Universe
begin

text \<open> There follows a class for representing channel types \<close>

class pre_uchantyperep = equal +
  \<comment> \<open> A mapping from channel names to types \<close>
  fixes uchans :: "'a itself \<Rightarrow> (uname \<Zpfun> utyp)"
  and   unamelist :: "'a itself \<Rightarrow> uname list"
  assumes uchans_namelist: "pdom (uchans a) = set (unamelist a)"
  and nonempty_namelist: "length (unamelist a) > 0"
begin

definition unames :: "'a itself \<Rightarrow> uname set" where
"unames a = pdom (uchans a)"

lemma finite_chans: "finite (pdom (uchans a))"
  by (simp add: local.uchans_namelist)

lemma finite_names: "finite (unames a)"
  by (simp add: local.finite_chans unames_def)

lemma nonempty_chans: "\<exists> x. x \<in> pdom (uchans a)"
  by (metis list.size(3) local.nonempty_namelist local.uchans_namelist order_less_irrefl set_empty some_in_eq)

lemma names_nonempty: "unames a \<noteq> {}"
  using local.nonempty_namelist local.uchans_namelist unames_def by fastforce

definition default_name :: "'a itself \<Rightarrow> uname" where
"default_name a = hd (unamelist a)"

text \<open> The value carried over the channel \<close>
  
end

syntax 
  "_unames" :: "type \<Rightarrow> logic" ("UNAMES'(_')")
  "_uchantype" :: "type \<Rightarrow> logic \<Rightarrow> logic" ("UCHANTYPE'(_, _')")
translations 
  "UNAMES('a)" == "CONST unames TYPE('a)"
  "UCHANTYPE('a, n)" == "CONST pfun_app (CONST uchans TYPE('a)) n"

lemma default_name [simp]: "default_name TYPE('c::pre_uchantyperep) \<in> UNAMES('c)"
  using hd_in_set nonempty_namelist by (auto simp add: default_name_def unames_def uchans_namelist)

typedef (overloaded) 'c::pre_uchantyperep name = 
  "{(n, t). n \<in> unames TYPE('c) \<and> t = UCHANTYPE('c, n)}"
  morphisms of_name name_of
  by (simp add: nonempty_chans unames_def)

setup_lifting type_definition_name

lift_definition label_of :: "'c::pre_uchantyperep name \<Rightarrow> uname" is "fst" .
lift_definition of_label :: "uname \<Rightarrow> 'c::pre_uchantyperep name"
  is "\<lambda> n. if n \<in> UNAMES('c) 
           then (n, (uchans TYPE('c))(n)\<^sub>p) 
           else (default_name TYPE('c), (uchans TYPE('c))(default_name TYPE('c))\<^sub>p)"
  by auto

instance name :: (pre_uchantyperep) finite
proof
  have "(UNIV :: 'a name set) = of_label ` {n. n \<in> unames TYPE('a)}"
    by (auto, transfer, auto)
  thus "finite (UNIV :: 'a name set)"
    by (metis finite_imageI finite_names mem_Collect_eq subsetI subset_antisym)
qed

instantiation name :: (pre_uchantyperep) equal
begin

definition equal_name :: "'a name \<Rightarrow> 'a name \<Rightarrow> bool" where
"equal_name x y = (label_of x = label_of y)"
  
instance 
  by (intro_classes, simp add: equal_name_def, transfer, auto)

end

definition mk_name :: "'c itself \<Rightarrow> uname \<Rightarrow> 'c::pre_uchantyperep name"
  where "mk_name c n = of_label n"


lemma label_of_in_names [simp]: "label_of (n::'c name) \<in> UNAMES('c::pre_uchantyperep)"
  by (transfer, auto)

lemma label_of_label [simp]:
  "n \<in> UNAMES('c :: pre_uchantyperep) \<Longrightarrow> label_of (of_label n :: 'c name) = n"
  by (transfer, simp)
  
lemma label_of_mk_name [simp]: "n \<in> UNAMES('c::pre_uchantyperep) \<Longrightarrow> label_of (mk_name c n :: 'c name) = n"
  unfolding mk_name_def by simp

lift_definition name_type :: "'c::pre_uchantyperep name \<Rightarrow> utyp"
  is snd .

syntax  
  "_mk_name" :: "type \<Rightarrow> logic \<Rightarrow> logic" ("mkname[_]")

translations
  "mkname['a]" == "CONST mk_name TYPE('a)"

lemma name_type_chantype [simp]: "name_type (n :: 'c name) = UCHANTYPE('c::pre_uchantyperep, label_of n)"
  by (transfer, transfer, auto simp add: prod.case_eq_if)

lemma name_type_make_name:
  "n \<in> UNAMES('c) \<Longrightarrow> name_type (mkname['c::pre_uchantyperep] n) = UCHANTYPE('c, n)"
  by simp

lemma mk_name_eq_iff [simp]:
  assumes "n\<^sub>1 \<in> UNAMES('c::pre_uchantyperep)" "n\<^sub>2 \<in> UNAMES('c)"
  shows "mkname['c] n\<^sub>1 = mkname['c] n\<^sub>2 \<longleftrightarrow> n\<^sub>1 = n\<^sub>2"
  using assms unfolding mk_name_def by (transfer, auto)

(* The following type should be isomorphic to 'c, but conveys more structure *)

typedef (overloaded) 'c::pre_uchantyperep event =
  "{(n, v). n \<in> unames TYPE('c) \<and> utyp_of v = Some ((uchans TYPE('c))(n)\<^sub>p)}"
  morphisms of_event event_of
  using nonempty_chans unames_def utyp_of_default_uval by blast

setup_lifting type_definition_event

lift_definition ev_name :: "'c::pre_uchantyperep event \<Rightarrow> 'c name" 
  is "\<lambda> (n, v). (n, the (utyp_of v))" by auto
definition ev_type :: "'c::pre_uchantyperep event \<Rightarrow> utyp"
  where "ev_type e = name_type (ev_name e)"
lift_definition ev_uval :: "'c::pre_uchantyperep event \<Rightarrow> uval" is "snd" .
lift_definition ev_val :: "'c::pre_uchantyperep event \<Rightarrow> 'a::uvals" is "from_uval \<circ> snd" .
lift_definition mk_event :: "'c name \<Rightarrow> 'a::uvals \<Rightarrow> 'c::pre_uchantyperep event"
  is "\<lambda> (n, t) v. (n, if UCHANTYPE('c, n) = UTYPE('a) then to_uval v else default_uval ((uchans TYPE('c))(n)\<^sub>p))"
  using utyp_of_default_uval by force

lemma ev_name_UNAMES: "ev_name (e :: 'c event) \<in> mkname['c] ` UNAMES('c::pre_uchantyperep)"
  unfolding mk_name_def by (transfer, auto)

lemma ev_name_mkevent [simp]:
  "ev_name (mk_event n (v :: 'a :: uvals)) = n"
  by (transfer, auto simp add: utyp_of_default_uval)

lemma ev_type_mkevent [simp]: 
  "ev_type (mk_event n v) = name_type n"
  unfolding ev_type_def by (transfer, auto)

lemma ev_val_mkevent [simp]:
  "\<lbrakk> name_type n = UTYPE('a) \<rbrakk> \<Longrightarrow> ev_val (mk_event n (v :: 'a :: uvals)) = v"
  by (transfer, auto)

lemma mkevent_surj:
  assumes "UTYPE('a) = ev_type x"
  shows "mk_event (ev_name x) (ev_val x :: 'a::uvals) = x"
  using assms
  apply (simp add: ev_val_def ev_type_def)
  apply (transfer)
  apply (auto simp add: from_uval_inv)
  done

lemma mkevent_eq_iff:
  fixes v\<^sub>1 v\<^sub>2 :: "'a::uvals"
  assumes "name_type n\<^sub>1 = UTYPE('a)" "name_type n\<^sub>2 = UTYPE('a)" 
  shows "mk_event n\<^sub>1 v\<^sub>1 = mk_event n\<^sub>2 v\<^sub>2 \<longleftrightarrow> n\<^sub>1 = n\<^sub>2 \<and> v\<^sub>1 = v\<^sub>2"
  using assms by transfer (auto, metis to_uval_inv)

lemma mkevent_eq_ev_iff:
  fixes v :: "'a::uvals"
  assumes  "name_type n = UTYPE('a)"
  shows "mk_event n v = e \<longleftrightarrow> ev_name e = n \<and> ev_val e = v"
  by (metis assms ev_name_mkevent ev_type_def ev_val_mkevent mkevent_surj)

lemma event_eq_iff:
  assumes "ev_type e = UTYPE('a::uvals)"
  shows "e = f \<longleftrightarrow> ev_name e = ev_name f \<and> (ev_val e :: 'a) = ev_val f"
  by (metis assms ev_type_def mkevent_surj)

lemma ev_name_labelled_event:
  "v :\<^sub>u UCHANTYPE('c::pre_uchantyperep, label_of n) \<Longrightarrow> ev_name (event_of (label_of n, v) :: 'c event) = (n :: 'c::pre_uchantyperep name)"
  by (simp add: ev_name_def prod.case_eq_if event_of_inverse[simplified])
     (metis label_of.rep_eq name_type.rep_eq name_type_chantype of_name_inverse prod.collapse)

lemma mk_event_event_of_def:
  "mk_event (n :: 'c name) (v::'a) 
    = event_of (label_of n, if UCHANTYPE('c::pre_uchantyperep, label_of n) = UTYPE('a::uvals) 
                            then to_uval v 
                            else default_uval ((uchans TYPE('c))(label_of n)\<^sub>p))"
  by (auto simp add: mk_event_def fun_eq_iff prod.case_eq_if label_of.rep_eq)


(*
type_synonym 'c chan = unit

definition mk_chan :: "'c name \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'c) \<Rightarrow> 'c chan" where
"mk_chan = undefined"
*)

(* I want to achieve a type something like "forall 'a\<in>unames. (('a, 'c) name, 'a \<Longrightarrow>\<^sub>\<triangle> 'c) *)


text \<open> Declare an isomorphism between @{typ 'c} and @{typ "'c event"}}\<close>

class uchantyperep = pre_uchantyperep +
  fixes uchan_mk :: "'a event \<Rightarrow> 'a"
  and uchan_dest :: "'a \<Rightarrow> 'a event"
  assumes uchan_mk_inv [simp]: "uchan_dest (uchan_mk x) = x"
  and uchan_dest_inv [simp]: "uchan_mk (uchan_dest y) = y"
begin

definition uchan_lens :: "'a event \<Longrightarrow> 'a" where
"uchan_lens = \<lparr> lens_get = uchan_dest, lens_put = (\<lambda> s. uchan_mk) \<rparr>"

lemma bij_uchan_lens: "bij_lens uchan_lens"
  by (unfold_locales, simp_all add: uchan_lens_def)

end

definition events_of :: "'e::uchantyperep name \<Rightarrow> 'e set" where
"events_of n = {e. \<exists> v. uchan_dest e = event_of (label_of n, v) \<and> utyp_of v = Some ((uchans TYPE('e))(label_of n)\<^sub>p)}"

typedef (overloaded) ('a, 'c) channel = "UNIV :: 'c name set" 
  morphisms channel_name mk_channel
  by auto

setup_lifting type_definition_channel

definition wf_channel :: "('a::uvals, 'c::pre_uchantyperep) channel \<Rightarrow> bool" where
"wf_channel c \<longleftrightarrow> name_type (channel_name c) = UTYPE('a)"

lift_definition channel_match :: "('a::uvals, 'c::uchantyperep) channel \<Rightarrow> 'c \<Rightarrow> 'a option"
  is "\<lambda> n e. if (name_type n = UTYPE('a) \<and> ev_name (uchan_dest e) = n) then Some (ev_val (uchan_dest e)) else None" .

lift_definition channel_build :: "('a::uvals, 'c::uchantyperep) channel \<Rightarrow> 'a \<Rightarrow> 'c"
  is "\<lambda> n v. if (name_type n = UTYPE('a)) then uchan_mk (mk_event n v) else undefined" .

lemma channel_name [simp, code]: "channel_name (mk_channel n) = n"
  by (simp add: mk_channel_inverse)

definition channel_prism :: "('a::uvals, 'c::uchantyperep) channel \<Rightarrow> 'a \<Longrightarrow>\<^sub>\<triangle> 'c" where
"channel_prism c = \<lparr> prism_match = channel_match c, prism_build = channel_build c \<rparr>"

text \<open> Instantiation for the unit type \<close>

instantiation unit :: pre_uchantyperep
begin

definition unamelist_unit :: "unit itself \<Rightarrow> uname list"
  where "unamelist_unit a = [STR ''unit'']"

definition uchans_unit :: "unit itself \<Rightarrow> String.literal \<Zpfun> utyp"
  where "uchans_unit a = {STR ''unit'' \<mapsto> UnitT}"

instance
  by (intro_classes, simp_all add: unamelist_unit_def uchans_unit_def)

end

lemma UNAMES_unit [simp]: "UNAMES(unit) = {STR ''unit''}"
  by (simp add: uchans_unit_def unames_def)

lemma ev_name_unit [simp]: "ev_name (e :: unit event) = (mkname[unit] STR ''unit'')"
  using ev_name_UNAMES[of e] by simp

instantiation unit :: uchantyperep
begin

definition uchan_mk_unit :: "unit event \<Rightarrow> unit" where
"uchan_mk_unit e = ()"

definition uchan_dest_unit :: "unit \<Rightarrow> unit event" where
"uchan_dest_unit x = mk_event (mkname[unit] STR ''unit'') ()"

instance 
  by (intro_classes)
     (simp_all add: uchan_mk_unit_def uchan_dest_unit_def mkevent_eq_ev_iff uchans_unit_def utyp_unit_def)

end

end