(* ML code for processing Z machine semantics *)

structure Z_Machine = struct

type param = string * string
datatype operation = Operation of {name: string, params: param list, guard: string, update: string, post: string}
datatype zmachine = ZMachine of {name: string, state: string, init: string, operations: operation list}

(* Calculate the types (i.e. maximals sets) of each parameter from the given sets *)

fun params_set ctx ps =
  let 
    open Syntax; open Library
    val pss = map (read_term ctx o snd) ps
  in if pss = [] 
       then @{term "UNIV :: unit set"} 
       else foldr1 (fn (x, y) => const @{const_abbrev "Product_Type.Times"} $ x $ y) pss
  end

fun params_typ ctx ps =
  case Term.type_of (Syntax.check_term ctx (params_set ctx ps)) of
                Type (@{type_name set}, [t]) => t | _ => raise Match;

fun firstLower s =
  case String.explode s of [] => "" | c :: cs => String.implode (Char.toLower c :: cs);

fun operation_sem' (Operation {name = n, params = ps, guard = g, update = upd, post = post}) ctx =
  let open Syntax; open Library; open HOLogic;
      val set = params_set ctx ps
      val ppat = mk_tuple (map (free o fst) ps)
  in snd (Local_Theory.define 
           ((Binding.name n, NoSyn)
         , ((Binding.name (n ^ "_def")
           , [Attrib.check_src @{context} (Token.make_src ("code", Position.none) [])])
           , check_term ctx 
              (const @{const_name "zop.make"} 
                $ set
                $ tupled_lambda ppat (Lift_Expr.mk_lift_expr ctx (Syntax.parse_term ctx g))
                $ tupled_lambda ppat (Syntax.parse_term ctx upd)
                $ tupled_lambda ppat (Lift_Expr.mk_lift_expr ctx (Syntax.parse_term ctx post))
                ))) ctx)
  end;


(* For each operation, we assign a channel in the overall channel type. The type of each channel
  is given by a Z set, which allows us to bound the number of transitions for simulation. *)

fun operation_sem st (Operation {name = n, params = ps, guard = g, update = upd, post = post}) ctx =
  let open Syntax; open Library; open HOLogic;
      val opc = Proof_Context.read_const {proper = false, strict = false} ctx (firstLower n)
      val set = params_set ctx ps
      val ppat = mk_tuple (map (free o fst) ps)
  in snd (Local_Theory.define 
           ((Binding.name n, NoSyn)
         , ((Binding.name (n ^ "_def")
           , [Attrib.check_src @{context} (Token.make_src ("code", Position.none) [])])
           , check_term ctx 
              (const @{const_name moperation} 
                $ opc 
                $ set
                $ tupled_lambda ppat (Lift_Expr.mk_lift_expr ctx (Syntax.parse_term ctx g))
                $ tupled_lambda ppat (Lift_Expr.mk_lift_expr ctx (Syntax.parse_term ctx post))
                $ tupled_lambda ppat (Type.constraint (st --> st) (Syntax.parse_term ctx upd))))) ctx)
  end;

(* The Z machine body declares the type it is operating over, an initialisation, and a set
  of operations. *)

fun zmachine_body_sem st n init onames ctx =
  let open Syntax; open HOLogic;
      val cs = map (fn on => case Proof_Context.read_const {proper = false, strict = false} ctx on
                    of Free (n, t) => free n) onames
      val ops = Syntax.check_term ctx (mk_list dummyT cs)
  in snd (Local_Theory.define 
           ((Binding.name n, NoSyn)
         , ((Binding.name (n ^ "_def")
           , [Attrib.check_src @{context} (Token.make_src ("code", Position.none) [])])
           , check_term ctx 
              (const @{const_name "machine"} $ Type.constraint (st --> st) init $ ops))) ctx) end

fun zmachine_sem (ZMachine {name = n, state = s, init = init, operations = ops}) ctx =
  let open Syntax
    val oparms = map (fn (Operation {params = p, ...}) => p) ops
    val onames = map (fn (Operation {name = n, ...}) => firstLower n) ops
    val opts = map (params_typ ctx) oparms
    val st = Syntax.read_typ ctx s
   in Channel_Type.compile_chantype ("chan", map2 (fn pn => fn pt => (pn, YXML.content_of (string_of_typ ctx pt))) onames opts) ctx
      |> fold (operation_sem st) ops
      |> zmachine_body_sem st n (Syntax.parse_term ctx init) (map (fn (Operation {name = n, ...}) => n) ops)
   end

val parse_param = 
  let open Parse in
    name -- (@{keyword "\<in>"} |-- term)
  end;
  

val parse_operation =
  let open Scan; open Parse in
  ((name --| @{keyword "="}) --
  (Scan.optional (@{keyword "params"} |-- repeat1 parse_param) []) --
  (Scan.optional (@{keyword "guard"} |-- term) "True") --
  (Scan.optional (@{keyword "update"} |-- term) "[\<leadsto>]") --
  (Scan.optional (@{keyword "post"} |-- term) "True"))
  >> (fn ((((n, ps), g), upd), post) => Operation {name = n, params = ps, guard = g, update = upd, post = post})
   end;

val parse_zmachine = 
  let open Scan; open Parse in
  (name --| @{keyword "="}) --
  (@{keyword "over"} |-- typ) --
  (@{keyword "init"} |-- term) --
  (@{keyword "operations"} |-- repeat1 parse_operation)
  >> (fn (((n, st), init), ops) => ZMachine {name = n, state = st, init = init, operations = ops})
  end;
 
end  