signature LENS_REL_UTILS =
sig
  val rename_rel_alpha_vars : tactic
end;

structure Lens_Rel_Utils : LENS_REL_UTILS =
struct

val lens_suffix = "\<^sub>v"

(* This function is nearly the same as Lens_Utils.rename_alpha_vars, but it also handles primed 
   variables. Probably this should be merged into Optics at some point. *)

fun remove_rel_lens_suffixes i st =
  let
    val (_, _, Bi, _) = Thm.dest_state (st, i);
    val params = (map #1 (Logic.strip_params Bi))
    val params' = 
      map (fn x => if (String.isSuffix lens_suffix x) 
                   then String.substring (x, 0, (String.size x - String.size lens_suffix)) 
                   else if (String.isSuffix (lens_suffix ^ "'") x)
                   then String.substring (x, 0, (String.size x - (String.size (lens_suffix ^ "'")))) ^ "'"
                   else x) params ;
  in if params = params' then Seq.empty else Seq.single (Thm.rename_params_rule (params', i) st)
  end;

val rename_rel_alpha_vars = ALLGOALS (fn i => PRIMSEQ (remove_rel_lens_suffixes i));

end
