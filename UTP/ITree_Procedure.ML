structure ITree_Procedure =
struct

fun mk_procedure (((n, p), st), body) ctx =
  let val ty = Syntax.check_typ ctx (Type (@{type_abbrev htree}, [HOLogic.unitT, Syntax.read_typ ctx st]))
      val pat = Syntax.read_term ctx p
      val vs = map (fst o dest_Free) (HOLogic.strip_tuple pat)
      val pat' = HOLogic.mk_tuple (map Syntax.free vs)
      val pty = (HOLogic.mk_tupleT (map (snd o dest_Free) (HOLogic.strip_tuple pat)))
      val def = Syntax.check_term ctx (Type.constraint (pty --> dummyT) (HOLogic.tupled_lambda pat' ((Type.constraint ty (Syntax.parse_term ctx body)))))
      val code_unfold = Attrib.check_src @{context} (Token.make_src ("code_unfold", Position.none) [])
      val prog_defs = Attrib.check_src @{context} (Token.make_src ("prog_defs", Position.none) [])
  in snd (Local_Theory.define ((Binding.name n, NoSyn), ((Binding.name (n ^ "_def"), [code_unfold, prog_defs]), def)) ctx) end;

val parse_procedure =
  let open Scan; open Parse in
  ((name -- term) -- 
   (Scan.optional (@{keyword "over"} |-- typ) "_") --
   (@{keyword "="} |-- term))
   end;  

end;

Outer_Syntax.command @{command_keyword procedure} "define an ITree procedure"
  (ITree_Procedure.parse_procedure >> (Toplevel.local_theory NONE NONE o ITree_Procedure.mk_procedure));
