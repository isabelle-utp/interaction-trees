(* ML code for processing Z machine semantics *)

structure Z_Machine = struct

type param = string * string
datatype operation = Operation of {name: string, state: string, params: param list, guard: string, update: string, post: string}
datatype zmachine = ZMachine of {name: string, state: string, init: string, operations: string list}

(* Calculate the types (i.e. maximal sets) of each parameter from the given sets *)

fun params_set pss =
  let 
    open Syntax; open Library
  in if pss = [] 
       then @{term "UNIV :: unit set"} 
       else foldr1 (fn (x, y) => const @{const_abbrev "Product_Type.Times"} $ x $ y) pss
  end

fun firstLower s =
  case String.explode s of [] => "" | c :: cs => String.implode (Char.toLower c :: cs);

fun zop_type n = n ^ "_type"

val SEXP = Const (@{const_name SEXP}, dummyT --> dummyT)

fun mk_zop (Operation {name = n, state = s, params = ps, guard = g, update = upd, post = post}) ctx =
  let open Syntax; open Library; open HOLogic;
      val pss = map (fn (p, t) => (p, read_term ctx t)) ps
      val set = params_set (map snd pss)
      val parm = dest_setT (Term.type_of (check_term ctx set))
      val st = read_typ ctx s
      val ppat = mk_tuple (map (free o fst) pss)
  in snd (Local_Theory.define 
           ((Binding.name (zop_type n), NoSyn)
         , ((Binding.name (zop_type n ^ "_def")
           , [Attrib.check_src @{context} (Token.make_src ("code_unfold", Position.none) [])])
           , check_term ctx set)) ctx) |>
     snd o Local_Theory.define 
           ((Binding.name n, NoSyn)
         , ((Binding.name (n ^ "_def")
           (* It would be better if we could mark these as "code" rather than "code_unfold" to retain
              the structure in the language target. For now, code_unfold is required to ensure that
              the semantics of enumerated inputs is correctly calculated *)
           , [Attrib.check_src @{context} (Token.make_src ("code_unfold", Position.none) [])])
           , check_term ctx ( 
              (Const (@{const_name "mk_zop"}, (parm --> st --> dummyT) --> dummyT)
                $ tupled_lambda ppat (SEXP $ Lift_Expr.mk_lift_expr ctx (parse_term ctx g)))
                $ tupled_lambda ppat (Type.constraint (st --> st) (parse_term ctx upd))
                $ tupled_lambda ppat (SEXP $ Lift_Expr.mk_lift_expr ctx (parse_term ctx post))
                )))
  end;

fun get_zop_ptype n ctx =
  case Proof_Context.read_const {proper = false, strict = false} ctx n of
    Const (_, Type (@{type_name fun}, [a, _])) => a |
    _ => raise Match;
      
fun mk_zmachine_chantype ops ctx =
  let val cs = map (fn n => (firstLower n, YXML.content_of (Syntax.string_of_typ ctx (get_zop_ptype n ctx)))) ops
  in Channel_Type.compile_chantype ("chan", cs) ctx
  end

fun read_const_name ctx n =
  case Proof_Context.read_const {proper = false, strict = false} ctx n of
    Const (n', _) => n' |
    Free (n', _) => n' |
    _ => raise Match;

fun zmachine_body_sem n st init ops ctx =
  let open Syntax; open HOLogic; open Proof_Context
      val oplist = 
            mk_list dummyT 
              (map (fn n => const @{const_name zop_event} $ free (firstLower n) $ const (read_const_name ctx (zop_type n)) $ const (read_const_name ctx n)) ops)
  in snd (Local_Theory.define 
           ((Binding.name n, NoSyn)
         , ((Binding.name (n ^ "_def")
           , [Attrib.check_src @{context} (Token.make_src ("code", Position.none) [])])
           , check_term ctx 
              (const @{const_name "machine"} $ Type.constraint (st --> st) init $ oplist))) ctx) end

fun zmachine_sem (ZMachine {name = n, state = s, init = i, operations = ops}) ctx =
  let open Syntax; open HOLogic
    val cs = map (fn n => (firstLower n, YXML.content_of (string_of_typ ctx (get_zop_ptype n ctx)))) ops
    val st = read_typ ctx s
    val init = parse_term ctx i
  in Channel_Type.compile_chantype ("chan", cs) ctx |>
     zmachine_body_sem n st init ops end

val parse_param = 
  let open Parse in
    name -- (@{keyword "\<in>"} |-- term)
  end;

val parse_operation =
  let open Scan; open Parse in
  ((name --| @{keyword "="}) --
  (Scan.optional (@{keyword "over"} |-- typ) "_") --
  (Scan.optional (@{keyword "params"} |-- repeat1 parse_param) []) --
  (Scan.optional (@{keyword "pre"} |-- term) "True") --
  (Scan.optional (@{keyword "update"} |-- term) "[\<leadsto>]") --
  (Scan.optional (@{keyword "post"} |-- term) "True"))
  >> (fn (((((n, st), ps), g), upd), post) => Operation {name = n, state = st, params = ps, guard = g, update = upd, post = post})
   end;

val parse_zmachine = 
  let open Scan; open Parse in
  (name --| @{keyword "="}) --
  (Scan.optional (@{keyword "over"} |-- typ) "_") --
  (@{keyword "init"} |-- term) --
  (@{keyword "operations"} |-- repeat1 name)
  >> (fn (((n, st), init), ops) => ZMachine {name = n, state = st, init = init, operations = ops})
  end;
 

end  