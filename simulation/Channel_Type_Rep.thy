theory Channel_Type_Rep
  imports Executable_Universe
begin

text \<open> There follows a class for representing channel types \<close>

class pre_uchantyperep =
  \<comment> \<open> A mapping from channel names to types \<close>
  fixes uchans :: "'a itself \<Rightarrow> (uname \<Zpfun> utyp)"

  assumes finite_chans: "finite (pdom (uchans a))"
  and nonempty_chans: "\<exists> n. n \<in> pdom (uchans a)"
begin

definition unames :: "'a itself \<Rightarrow> uname set" where
"unames a = pdom (uchans a)"

lemma finite_names: "finite (unames a)"
  by (simp add: local.finite_chans unames_def)

lemma names_nonempty: "unames a \<noteq> {}"
  using local.nonempty_chans unames_def by auto

text \<open> The value carried over the channel \<close>
  
end

syntax 
  "_unames" :: "type \<Rightarrow> logic" ("UNAMES'(_')")
  "_uchantype" :: "type \<Rightarrow> logic \<Rightarrow> logic" ("UCHANTYPE'(_, _')")
translations 
  "UNAMES('a)" == "CONST unames TYPE('a)"
  "UCHANTYPE('a, n)" == "CONST pfun_app (CONST uchans TYPE('a)) n"

typedef (overloaded) 'c::pre_uchantyperep name = 
  "{n. n \<in> unames TYPE('c)}"
  by (simp add: nonempty_chans unames_def)

setup_lifting type_definition_name

instance name :: (pre_uchantyperep) finite
proof
  have "(UNIV :: 'a name set) = Abs_name ` {n. n \<in> unames TYPE('a)}"
    by (auto, metis Abs_name_cases Collect_mem_eq image_iff)
  thus "finite (UNIV :: 'a name set)"
    by (metis finite_imageI finite_names mem_Collect_eq subsetI subset_antisym)
qed

lift_definition mk_name :: "'c itself \<Rightarrow> uname \<Rightarrow> 'c::pre_uchantyperep name"
  is "\<lambda> c n. if n \<in> UNAMES('c) then n else SOME n. n \<in> UNAMES('c)"
  using names_nonempty some_in_eq by auto

lift_definition name_type :: "'c::pre_uchantyperep name \<Rightarrow> utyp"
  is "\<lambda> n. UCHANTYPE('c, n)" .

syntax  
  "_mk_name" :: "type \<Rightarrow> logic \<Rightarrow> logic" ("mkname[_]")

translations
  "mkname['a]" == "CONST mk_name TYPE('a)"

lemma name_type_make_name [simp]:
  "n \<in> UNAMES('c) \<Longrightarrow> name_type (mkname['c::pre_uchantyperep] n) = UCHANTYPE('c, n)"
  by (transfer, simp)

lemma mk_name_eq_iff [simp]:
  assumes "n\<^sub>1 \<in> UNAMES('c::pre_uchantyperep)" "n\<^sub>2 \<in> UNAMES('c)"
  shows "mkname['c] n\<^sub>1 = mkname['c] n\<^sub>2 \<longleftrightarrow> n\<^sub>1 = n\<^sub>2"
  using assms by (transfer, simp)

(* The following type should be isomorphic to 'c, but conveys more structure *)

typedef (overloaded) 'c::pre_uchantyperep event =
  "{(n, v). n \<in> unames TYPE('c) \<and> utyp_of v = Some ((uchans TYPE('c))(n)\<^sub>p)}"
  morphisms of_event event_of
  using nonempty_chans unames_def utyp_of_default_uval by blast

setup_lifting type_definition_event

lift_definition ev_name :: "'c::pre_uchantyperep event \<Rightarrow> 'c name" is fst by auto
definition ev_type :: "'c::pre_uchantyperep event \<Rightarrow> utyp"
  where "ev_type e = name_type (ev_name e)"
lift_definition ev_val :: "'c::pre_uchantyperep event \<Rightarrow> 'a::uvals" is "from_uval \<circ> snd" .
lift_definition mk_event :: "'c name \<Rightarrow> 'a::uvals \<Rightarrow> 'c::pre_uchantyperep event"
  is "\<lambda> n v. (n, if UCHANTYPE('c, n) = UTYPE('a) then to_uval v else default_uval ((uchans TYPE('c))(n)\<^sub>p))"
  using utyp_of_default_uval by force

lemma ev_name_UNAMES: "ev_name (e :: 'c event) \<in> mkname['c] ` UNAMES('c::pre_uchantyperep)"
  by (transfer, auto)

lemma ev_name_mkevent [simp]:
  "ev_name (mk_event n (v :: 'a :: uvals)) = n"
  by (transfer, auto)

lemma ev_type_mkevent [simp]: 
  "ev_type (mk_event n v) = name_type n"
  unfolding ev_type_def by (transfer, auto)

lemma ev_val_mkevent [simp]:
  "\<lbrakk> name_type n = UTYPE('a) \<rbrakk> \<Longrightarrow> ev_val (mk_event n (v :: 'a :: uvals)) = v"
  by (transfer, simp)

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
  using assms by transfer (simp, metis to_uval_inv)

lemma mkevent_eq_ev_iff:
  fixes v :: "'a::uvals"
  assumes  "name_type n = UTYPE('a)"
  shows "mk_event n v = e \<longleftrightarrow> ev_name e = n \<and> ev_val e = v"
  by (metis assms ev_name_mkevent ev_type_def ev_val_mkevent mkevent_surj)

lemma event_eq_iff:
  assumes "ev_type e = UTYPE('a::uvals)"
  shows "e = f \<longleftrightarrow> ev_name e = ev_name f \<and> (ev_val e :: 'a) = ev_val f"
  by (metis assms ev_type_def mkevent_surj)

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

typedef (overloaded) ('a, 'c) channel = "UNIV :: 'c name set" by auto

setup_lifting type_definition_channel

lift_definition wb_channel :: "('a::uvals, 'c::pre_uchantyperep) channel \<Rightarrow> bool"
  is "\<lambda> n. name_type n = UTYPE('a)" .

lift_definition channel_match :: "('a::uvals, 'c::uchantyperep) channel \<Rightarrow> 'c \<Rightarrow> 'a option"
  is "\<lambda> n e. if (name_type n = UTYPE('a) \<and> ev_name (uchan_dest e) = n) then Some (ev_val (uchan_dest e)) else None" .

lift_definition channel_build :: "('a::uvals, 'c::uchantyperep) channel \<Rightarrow> 'a \<Rightarrow> 'c"
  is "\<lambda> n v. if (name_type n = UTYPE('a)) then uchan_mk (mk_event n v) else undefined" .

definition channel_prism :: "('a::uvals, 'c::uchantyperep) channel \<Rightarrow> 'a \<Longrightarrow>\<^sub>\<triangle> 'c" where
"channel_prism c = \<lparr> prism_match = channel_match c, prism_build = channel_build c \<rparr>"

end