section \<open> Pseudo Random Number Generation \<close>

theory ITree_Random
  imports "ITree_Countable_Nondeterminism"
  keywords "gen_random_seed" :: "thy_decl_block"
begin

subsection \<open> Preliminaries \<close>

instantiation natural :: default
begin

definition default_natural :: "natural" where "default_natural = 0"

instance ..

end

subsection \<open> Generating Seeds \<close>

text \<open> Command @{command gen_random_seed} populates a previously created polymorphic constant with
  a randomly chosen seed. Each time the Isabelle document refreshes, a different seed is produced. \<close>

ML \<open>
structure Gen_Random_Seed =
struct

fun gen_random_seed n thy =
  let open HOLogic; open Code_Numeral
      val (s1, s2) = Random_Engine.next_seed()
      val pt = mk_prod (mk_number @{typ natural} (integer_of_natural s1), mk_number @{typ natural} (integer_of_natural s2)) 
      val Const (pn, typ) = Proof_Context.read_const {proper = false, strict = false} (Named_Target.theory_init thy) n
      val ctx = Overloading.overloading [(n, (pn, dummyT), false)] thy
  in (Local_Theory.exit_global o snd o Local_Theory.define (((Binding.name n), NoSyn), ((Binding.name (n ^ "_def"), [Attrib.check_src @{context} (Token.make_src ("code", Position.none) [])]), pt))) ctx 
  end ;
end;

Outer_Syntax.command @{command_keyword gen_random_seed} "populate a polymorphic constant with a random seed"
  (Parse.name >> (Toplevel.theory o Gen_Random_Seed.gen_random_seed))
\<close>

subsection \<open> Seed States and Generation \<close>

definition gen :: "natural \<Rightarrow> Random.seed \<Rightarrow> 'a::random \<times> Random.seed" where
"gen n s = (let x = Quickcheck_Random.random n s in (fst (fst x), snd x))" 

class seed_state =
  fixes rseed :: "Random.seed \<Longrightarrow> 'a"
  assumes rseed_vwb: "vwb_lens rseed"

text \<open> We define the procedure @{text uniform} to generate a random value, when in a state that
  has a seed state component. We could alternatively provide these values with events. \<close>

definition uniform :: "natural \<Rightarrow> 's::seed_state \<Rightarrow> ('e, 'a::random \<times> 's) itree" where
"uniform n = (\<lambda> s. let (n, sd') = gen n (get\<^bsub>rseed\<^esub> s) in Ret (n, put\<^bsub>rseed\<^esub> s sd'))"

subsection \<open> Store with Random Seed \<close>

zstore rangen =
  ranseed :: "Random.seed"

instantiation rangen_ext :: (type) seed_state
begin

definition rseed_rangen_ext :: "Random.seed \<Longrightarrow> 'a rangen_ext" where 
"rseed_rangen_ext = ranseed" 

instance 
  by (intro_classes, simp add: rseed_rangen_ext_def)

end

consts INITIAL_SEED :: "Random.seed"

end