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

(* The following type should be isomorphic to 'c, but conveys more structure *)

typedef (overloaded) 'c::pre_uchantyperep event =
  "{(n, v). n \<in> unames TYPE('c) \<and> utyp_of v = Some ((uchans TYPE('c))(n)\<^sub>p)}"
  morphisms of_event event_of
  using nonempty_chans unames_def utyp_of_default_uval by blast

setup_lifting type_definition_event

lift_definition ev_name :: "'c::pre_uchantyperep event \<Rightarrow> uname" is fst .
definition ev_type :: "'c::pre_uchantyperep event \<Rightarrow> utyp"
  where "ev_type e = UCHANTYPE('c, ev_name e)"
lift_definition ev_val :: "'c::pre_uchantyperep event \<Rightarrow> 'a::uvals" is "from_uval \<circ> snd" .
lift_definition mk_event :: "'c itself \<Rightarrow> uname \<Rightarrow> 'a::uvals \<Rightarrow> 'c::pre_uchantyperep event"
  is "\<lambda> c n v. if n \<in> UNAMES('c)
               then (n, if UCHANTYPE('c, n) = UTYPE('a) then to_uval v else default_uval ((uchans TYPE('c))(n)\<^sub>p))
               else (let sn = SOME n. n \<in> unames TYPE('c) in (sn, default_uval ((uchans TYPE('c))(sn)\<^sub>p)))"
  apply auto
  apply (metis nonempty_chans old.prod.inject someI unames_def)
  apply (metis fst_conv snd_conv utyp_of_default_uval)
  using utyp_of_default_uval apply blast
  apply (metis nonempty_chans prod.inject someI unames_def)
  apply (metis fst_conv snd_conv utyp_of_default_uval)
  done

syntax "_mk_event" :: "type \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("mkevent[_]")

translations "mkevent['a] n v" == "CONST mk_event TYPE('a) n v"

lemma ev_name_UNAMES: "ev_name (e :: 'c event) \<in> UNAMES('c::pre_uchantyperep)"
  by (transfer, auto)

lemma ev_name_mkevent:
  "n \<in> UNAMES('a) \<Longrightarrow> ev_name (mkevent['a::pre_uchantyperep] n (v :: 'b :: uvals)) = n"
  by (transfer, auto)

lemma ev_type_mkevent: "n \<in> UNAMES('c) \<Longrightarrow> ev_type (mkevent['c::pre_uchantyperep] n v) = UCHANTYPE('c, n)"
  unfolding ev_type_def by (transfer, auto)

lemma mkevent_surj:
  assumes "UTYPE('a) = ev_type x"
  shows "mkevent['c::pre_uchantyperep] (ev_name x) (ev_val x :: 'a::uvals) = x"
  using assms
  apply (simp add: ev_val_def ev_type_def)
  apply (transfer)
  apply (auto simp add: from_uval_inv)
  done

lemma mkevent_eq_iff:
  fixes v\<^sub>1 v\<^sub>2 :: "'a::uvals"
  assumes 
    "n\<^sub>1 \<in> UNAMES('c)" 
    "n\<^sub>2 \<in> UNAMES('c)" 
    "UCHANTYPE('c, n\<^sub>1) = UTYPE('a)" "UCHANTYPE('c, n\<^sub>2) = UTYPE('a)" 
  shows "mkevent['c::pre_uchantyperep] n\<^sub>1 v\<^sub>1 = mkevent['c::pre_uchantyperep] n\<^sub>2 v\<^sub>2 \<longleftrightarrow> n\<^sub>1 = n\<^sub>2 \<and> v\<^sub>1 = v\<^sub>2"
  using assms by transfer (simp, metis to_uval_inv)

lemma mkevent_eq_ev_iff:
  fixes v :: "'a::uvals"
  assumes "n \<in> UNAMES('c)" "UCHANTYPE('c, n) = UTYPE('a)"
  shows "mkevent['c::pre_uchantyperep] n v = e \<longleftrightarrow> ev_name e = n \<and> ev_val e = v"
  by (metis assms(1) assms(2) ev_name_mkevent ev_type_def mkevent_eq_iff mkevent_surj)

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


class uchantyperep = pre_uchantyperep +
  fixes uchan_mk :: "'a event \<Rightarrow> 'a"
  and uchan_dest :: "'a \<Rightarrow> 'a event"
  assumes "uchan_dest (uchan_mk x) = x"

chantype chan = 
  Input :: unit
  Output :: integer

instantiation chan :: pre_uchantyperep
begin

definition uchans_chan :: "chan itself \<Rightarrow> String.literal \<Zpfun> utyp"
  where "uchans_chan x = {STR ''Input'' \<mapsto> UnitT, STR ''Output'' \<mapsto> IntT}"

instance
  by (intro_classes, auto simp add: uchans_chan_def)

end

lemma UNAMES_chan [simp]: "UNAMES(chan) = {STR ''Input'', STR ''Output''}"
  by (auto simp add: unames_def uchans_chan_def)

lemma UTYPES_chan [simp]: 
  "UCHANTYPE(chan, STR ''Input'') = UTYPE(unit)"
  "UCHANTYPE(chan, STR ''Output'') = UTYPE(integer)"
  by (simp_all add: uchans_chan_def utyp_unit_def utyp_integer_def)

instantiation chan :: uchantyperep
begin

definition uchan_mk_chan :: "chan event \<Rightarrow> chan"
  where "uchan_mk_chan e = (if (ev_name e = STR ''Input'') then Input_C (ev_val e)
                            else Output_C (ev_val e))"

fun uchan_dest_chan :: "chan \<Rightarrow> chan event" where
"uchan_dest (Input_C v) = mkevent[chan] (STR ''Input'') v" |
"uchan_dest (Output_C v) = mkevent[chan] (STR ''Output'') v" 

instance
  apply (intro_classes)
  apply (auto simp add: uchan_mk_chan_def mkevent_eq_ev_iff)
  using UNAMES_chan ev_name_UNAMES apply blast
  done

end

record uevent =
  uev_name :: uname
  uev_outp :: uval
  uev_inp  :: uval

datatype ('e, 'b) chf =
  ChanF (chf_chn: "(uevent \<Longrightarrow>\<^sub>\<triangle> 'e)") \<comment> \<open> The channel, including a name, output value, and input value \<close>
        (chf_out: "uname \<times> uval") \<comment> \<open> The value output by the process (displayed in the animator) \<close>
        (chf_typ: "utyp") \<comment> \<open> The type of data requested by the animator \<close>
        (chf_cont: "uval \<Rightarrow> 'b") \<comment> \<open> The continuation for each kind of value received \<close>

definition pfun_of_chfun :: 
  "('e, 'b) chf \<Rightarrow> 'e \<Zpfun> 'b" where
"pfun_of_chfun chf = 
    (\<lambda> e\<in>{build\<^bsub>chf_chn chf\<^esub> \<lparr> uev_name = fst (chf_out chf), uev_outp = snd (chf_out chf), uev_inp = v \<rparr> 
          | v. v \<in> uvals (chf_typ chf)} 
    \<bullet> (chf_cont chf) (uev_inp (the (match\<^bsub>chf_chn chf\<^esub> e))))"

definition
  "map_chfun f chf = ChanF (chf_chn chf) (chf_out chf) (chf_typ chf) (f \<circ> chf_cont chf)"

lemma map_pfun_pfun_of_chfun: 
  "map_pfun f (pfun_of_chfun chf) = pfun_of_chfun (map_chfun f chf)"
  by (simp add: map_chfun_def pfun_of_chfun_def pfun_eq_iff)

lemma "pfun_app (pfun_of_chfun chf) e = undefined"
  apply (simp add: pfun_of_chfun_def)
  apply (subst pabs_apply)
    apply simp_all
  oops

definition pfun_of_chfuns ::
  "('e, 'b) chf list \<Rightarrow> 'e \<Zpfun> 'b" where
"pfun_of_chfuns chfs = foldr (\<lambda> c f. pfun_of_chfun c \<oplus> f) chfs {}\<^sub>p"

lemma map_pfun_pfun_of_chfuns [code]:
  "map_pfun f (pfun_of_chfuns chfs) = pfun_of_chfuns (map (map_chfun f) chfs)"
  by (induct chfs, simp_all add: pfun_of_chfuns_def map_pfun_pfun_of_chfun)

lemma pfun_of_chfuns_Nil [simp]: "pfun_of_chfuns [] = {}\<^sub>p"
  by (simp add: pfun_of_chfuns_def)

lemma pfun_of_chfuns_Cons [simp]: "pfun_of_chfuns (chf # chfs) = pfun_of_chfun chf \<oplus> pfun_of_chfuns chfs"
  by (simp add: pfun_of_chfuns_def)

lemma pfun_of_chfuns_override [code]: 
  "pfun_of_chfuns chfs1 \<oplus> pfun_of_chfuns chfs2 = pfun_of_chfuns (chfs1 @ chfs2)"
  by (induct chfs1 arbitrary: chfs2; simp add: override_assoc; metis override_assoc)


end