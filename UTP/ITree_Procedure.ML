structure ITree_Procedure =
struct

fun mk_procedure evT ((((n, p), ot), st), body) ctx =
  let val ty = (Syntax.check_typ ctx (Type (@{type_abbrev htree}, [evT, Syntax.read_typ ctx st])))
      val pat = Syntax.read_term ctx p
      val vs = map (fst o dest_Free) (HOLogic.strip_tuple pat)
      val pat' = HOLogic.mk_tuple (map Syntax.free vs)
      val pty = (HOLogic.mk_tupleT (map (snd o dest_Free) (HOLogic.strip_tuple pat)))
      val pbody = Type.constraint ty (Syntax.parse_term ctx body)
      val def = HOLogic.tupled_lambda pat' pbody
      val code_unfold = Attrib.check_src @{context} (Token.make_src ("code_unfold", Position.none) [])
      val prog_defs = Attrib.check_src @{context} (Token.make_src ("prog_defs", Position.none) [])
      fun mk_def ty x v = Syntax.check_term ctx (Const ("Pure.eq", ty --> ty --> Term.propT) $ Free (x, ty) $ v);
      val def_ty = pty --> ty        
  in snd (Specification.definition (SOME (Binding.name n, SOME def_ty, NoSyn)) [] [] ((Binding.name (n ^ "_def"), [code_unfold, prog_defs]), mk_def def_ty n def) ctx) 
  end;

val parse_procedure =
  let open Scan; open Parse in
  ((name -- (Scan.optional term "()")) -- 
   (Scan.optional (@{keyword "::"} |-- typ) "()") -- 
   (Scan.optional (@{keyword "over"} |-- typ) "_") --
   (@{keyword "="} |-- term))
   end;  

end;