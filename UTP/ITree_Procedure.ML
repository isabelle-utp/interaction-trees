(* Commands for programs and procedures *)

structure ITree_Procedure =
struct

fun mk_program evT (((n, p), st), body) ctx =
  let open Syntax
      val ty = (check_typ ctx (Type (@{type_abbrev htree}, [evT, read_typ ctx st])))
      val pat = read_term ctx p
      val vs = map (fst o dest_Free) (HOLogic.strip_tuple pat)
      val pat' = HOLogic.mk_tuple (map free vs)
      val pty = HOLogic.mk_tupleT (map (snd o dest_Free) (HOLogic.strip_tuple pat))
      val pbody = Type.constraint ty (parse_term ctx body)
      val def = HOLogic.tupled_lambda pat' pbody
      val attrs = @{attributes [code_unfold, prog_defs]};
      fun mk_def ty x v = check_term ctx (Const ("Pure.eq", ty --> ty --> Term.propT) $ Free (x, ty) $ v);
      val def_ty = pty --> ty        
  in snd (Specification.definition (SOME (Binding.name n, SOME def_ty, NoSyn)) [] [] ((Binding.name (n ^ "_def"), attrs), mk_def def_ty n def) ctx) 
  end;

val parse_program =
  let open Scan; open Parse in
  ((name -- (Scan.optional term "()")) -- 
   (Scan.optional (@{keyword "over"} |-- typ) "_") --
   (@{keyword "="} |-- term))
   end;  

fun mk_procedure evT ((((n, p), ot), st), body) ctx =
  let open Syntax
      val stT = read_typ ctx st
      val retT = read_typ ctx ot
      (* Determine whether has a procedure has a return or not, and if not add a void return *)
      val outT = (case snd (dest_funT (fastype_of (read_term ctx body)))
                  of Type (@{type_name itree}, [_, t]) => t | _ => error "Not an ITree type")
      val has_ret = (case outT of Type ("Product_Type.prod", _) => true | _ => false)
      fun add_ret t = (if has_ret then t else const @{const_name seq_itree} $ t $ (const @{const_abbrev proc_ret_empty}))  
      val pat = read_term ctx p
      val vs = map (fst o dest_Free) (HOLogic.strip_tuple pat)
      val pat' = HOLogic.mk_tuple (map free vs)
      val pty = HOLogic.mk_tupleT (map (snd o dest_Free) (HOLogic.strip_tuple pat))
      val ty = check_typ ctx (stT --> Type (@{type_name itree}, [evT, HOLogic.mk_prodT (retT, dummyT)])) 
      val pbody = Type.constraint ty (add_ret (parse_term ctx body))
      val def = HOLogic.tupled_lambda pat' pbody
      val attrs = @{attributes [code_unfold, prog_defs]};
      fun mk_def ty x v = check_term ctx (Const ("Pure.eq", ty --> ty --> Term.propT) $ Free (x, ty) $ v);
      val def_ty = pty --> ty        
  in snd (Specification.definition (SOME (Binding.name n, SOME def_ty, NoSyn)) [] [] ((Binding.name (n ^ "_def"), attrs), mk_def def_ty n def) ctx) 
  end;

val parse_procedure =
  let open Scan; open Parse in
  ((name -- (Scan.optional term "()")) -- 
   (Scan.optional (@{keyword "::"} |-- typ) "unit") -- 
   (Scan.optional (@{keyword "over"} |-- typ) "unit") --
   (@{keyword "="} |-- term))
   end;  

end;
