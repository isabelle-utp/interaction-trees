section \<open> Execute Terminating ITrees \<close>

theory ITree_Exec
  imports ITree_Eval
  keywords "execute" :: "diag"
begin

definition rem_Sils :: "('e, 's) itree \<Rightarrow> ('e, 's) itree" where
"rem_Sils P = un_Sils_n MAX_SIL_STEPS P"

datatype 'r execres = TermEx 'r  | Abort | Visible | TimeoutEx nat 

notation (output) TermEx ("Terminates: _") and Abort ("Aborted") and Visible ("Visible event") and TimeoutEx ("Timed out '(_ steps')")

fun exec_res :: "('e, 'r) itree \<Rightarrow> 'r execres" where
"exec_res (Ret x) = TermEx x" |
"exec_res (Vis F) = (if F = {\<mapsto>} then Abort else Visible)" |
"exec_res _ = TimeoutEx MAX_SIL_STEPS"

definition itree_exec :: "('b::default \<Rightarrow> ('e, 's) itree) \<Rightarrow> 's execres" where
"itree_exec P = exec_res (rem_Sils (P default))"

ML \<open> 
let fun execute_cmd t ctx =
  let val tm = Syntax.check_term ctx (Syntax.const @{const_name itree_exec} $ Syntax.parse_term ctx t)
      val _ = Pretty.writeln (Syntax.pretty_term ctx (Value_Command.value ctx tm))
  in ctx end;
in
Outer_Syntax.command @{command_keyword execute} "execute an ITree procedure"
  (Parse.term >> (Toplevel.local_theory NONE NONE o execute_cmd))
end
\<close>
 
end