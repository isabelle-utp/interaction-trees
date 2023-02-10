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
  where "ev_type e = (uchans TYPE('c))(ev_name e)\<^sub>p"
lift_definition ev_val :: "'c::pre_uchantyperep event \<Rightarrow> 'a::uvals" is "from_uval \<circ> snd" .
lift_definition mk_event :: "uname \<Rightarrow> 'a::uvals \<Rightarrow> 'c::pre_uchantyperep event"
  is "\<lambda> n v. if (n \<in> unames TYPE('c) \<and> (uchans TYPE('c))(n)\<^sub>p = UTYPE('a))
             then (n, to_uval v) 
             else (let sn = SOME n. n \<in> unames TYPE('c) in (sn, default_uval ((uchans TYPE('c))(sn)\<^sub>p)))"
  apply auto
  apply (metis nonempty_chans old.prod.inject someI unames_def)
  apply (metis fst_conv snd_conv utyp_of_default_uval)
  apply (metis nonempty_chans prod.inject someI unames_def)
  apply (metis fst_conv snd_conv utyp_of_default_uval)
  done

lemma 
  assumes "UTYPE('a) = ev_type x"
  shows "mk_event (ev_name x) (ev_val x :: 'a::uvals) = x"
  using assms
  apply (simp add: ev_val_def ev_type_def)
  apply (transfer)
  apply auto
  oops

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

(*
instantiation chan :: uchantyperep
begin

definition uchan_mk_chan :: "chan event \<Rightarrow> chan"
  where "uchan_mk_chan e = (if (ev_name e = STR ''Input'') then Input_C (ev_val e)
                            else Output_C (ev_val e))"

fun uchan_dest_chan :: "chan \<Rightarrow> chan event" where
"uchan_dest (Input_C v) = mk_event (STR ''Input'', to_uval v)" |
"uchan_dest (Output_C v) = mk_event (STR ''Output'', to_uval v)" 

instance
  apply (intro_classes)
  apply (auto simp add: uchan_mk_chan_def)
*)

datatype ('e, 'b) chf =
  ChanF (chf_chn: "(uname \<times> uval \<times> uval \<Longrightarrow>\<^sub>\<triangle> 'e)") \<comment> \<open> The channel, including a name, output value, and input value \<close>
        (chf_out: "uname \<times> uval") \<comment> \<open> The value output by the process (displayed in the animator) \<close>
        (chf_typ: "utyp") \<comment> \<open> The type of data requested by the animator \<close>
        (chf_cont: "uval \<Rightarrow> 'b") \<comment> \<open> The continuation for each kind of value received \<close>

definition pfun_of_chfun :: 
  "('e, 'b) chf \<Rightarrow> 'e \<Zpfun> 'b" where
"pfun_of_chfun chf = 
    (\<lambda> e\<in>{build\<^bsub>chf_chn chf\<^esub> (fst (chf_out chf), snd (chf_out chf), v) | v. v \<in> uvals (chf_typ chf)} 
    \<bullet> (chf_cont chf) (snd (snd (the (match\<^bsub>chf_chn chf\<^esub> e)))))"

definition
  "map_chfun f chf = ChanF (chf_chn chf) (chf_out chf) (chf_typ chf) (f \<circ> chf_cont chf)"

lemma map_pfun_pfun_of_chfun: 
  "map_pfun f (pfun_of_chfun chf) = pfun_of_chfun (map_chfun f chf)"
  by (simp add: map_chfun_def pfun_of_chfun_def pfun_eq_iff)

lemma "pfun_app (pfun_of_chfun chf) e = undefined"
  apply (simp add: pfun_of_chfun_def)
  apply (subst pabs_apply)
    apply simp
  oops

definition pfun_of_chfuns ::
  "('e, 'b) chf list \<Rightarrow> 'e \<Zpfun> 'b" where
"pfun_of_chfuns chfs = foldr (\<lambda> c f. pfun_of_chfun c \<oplus> f) chfs {}\<^sub>p"

lemma map_pfun_pfun_of_chfuns [code]:
  "map_pfun f (pfun_of_chfuns chfs) = pfun_of_chfuns (map (map_chfun f) chfs)"
  by (induct chfs, simp_all add: pfun_of_chfuns_def map_pfun_pfun_of_chfun)

end