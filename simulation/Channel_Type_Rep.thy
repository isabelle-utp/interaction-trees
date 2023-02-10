theory Channel_Type_Rep
  imports Executable_Universe
begin

text \<open> There follows a class for representing channel types \<close>

class pre_uchantyperep =
  \<comment> \<open> A mapping from channel names to types \<close>
  fixes uchans :: "'a itself \<Rightarrow> (uname \<Zpfun> utyp)"
  \<comment> \<open> Make an instance of the channel type \<close>
  and uchan_mk :: "uname \<times> uval \<Rightarrow> 'a" 
  \<comment> \<open> Deconstruct an instance of the channel type \<close>
  and uchan_dest :: "'a \<Rightarrow> uname \<times> uval"

  assumes finite_chans: "finite (pdom (uchans a))"
  and nonempty_chans: "\<exists> n. n \<in> pdom (uchans a)"
begin

definition unames :: "'a itself \<Rightarrow> uname set" where
"unames a = pdom (uchans a)"

text \<open> The name of a channel used by an event in @{typ 'a} \<close>
definition "uchan_name x = fst (uchan_dest x)"

lemma finite_names: "finite (unames a)"
  by (simp add: local.finite_chans unames_def)

lemma names_nonempty: "unames a \<noteq> {}"
  using local.nonempty_chans unames_def by auto

text \<open> The value carried over the channel \<close>
  
definition "uchan_val x = snd (uchan_dest x)"

end

typedef (overloaded) 'c::pre_uchantyperep name = 
  "{n. n \<in> unames TYPE('c)}"
  by (simp add: nonempty_chans unames_def)

(* The following type should be isomorphic to 'c, but conveys more structure *)

typedef (overloaded) 'c::pre_uchantyperep event =
  "{(n, v). n \<in> unames TYPE('c) \<and> utyp_of v = Some ((uchans TYPE('c))(n)\<^sub>p)}"
  using nonempty_chans unames_def utyp_of_default_uval by blast

setup_lifting type_definition_name

type_synonym 'c chan = unit

definition mk_chan :: "'c name \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'c) \<Rightarrow> 'c chan" where
"mk_chan = undefined"

(* I want to achieve a type something like "forall 'a\<in>unames. (('a, 'c) name, 'a \<Longrightarrow>\<^sub>\<triangle> 'c) *)


class uchantyperep = pre_uchantyperep +
  \<comment> \<open> Every name used in an event is a prescribed channel \<close>
  assumes uchan_names: "uchan_name x \<in> unames a"
  \<comment> \<open> Every value conveyed by a channel has the prescribed type \<close>
  and uchan_types: "utyp_of (uchan_val x) = Some(uchans a(uchan_name x)\<^sub>p)"
  and "\<lbrakk> n \<in> unames a; utyp_of v = Some(uchans a(n)\<^sub>p) \<rbrakk> \<Longrightarrow> uchan_dest (uchan_mk (n, v)) = (n, v)"

end