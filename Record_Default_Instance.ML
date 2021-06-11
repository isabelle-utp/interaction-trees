(* Create instance of the type class default for records where every field has a default instance. *)

signature RECORD_DEFAULT_INSTANCE =
sig
  val mk_rec_default_instance: string -> theory -> theory
end

structure Record_Default_Instance : RECORD_DEFAULT_INSTANCE =
struct

open Syntax
open Term

fun mk_rec_default_instance tname thy = 
let
  fun mk_def ty x v = Const ("Pure.eq", ty --> ty --> Term.propT) $ Free (x, ty) $ v;
  val ctx0 = Class.instantiation_cmd ([tname ^ "_ext"], ["default"], "default") thy;
  val Const (make, t) = read_term ctx0 (tname ^ ".make");
  val args = length (Term.binder_types t);
  val Const (extend, _) = read_term ctx0 (tname ^ ".extend");
  val default = @{const_name "default"};
  val def_tm = Syntax.const extend $ (foldl1 (op $) ((const make) :: (replicate args (const default)))) $ const default;
  val def_ty = Syntax.read_typ ctx0 ("'a " ^ tname ^ "_scheme");
  val (_, ctx1) = Specification.definition (SOME (Binding.name ("default_" ^ tname ^ "_ext"), NONE, NoSyn)) [] [] ((Binding.empty, []), mk_def def_ty ("default_" ^ tname ^ "_ext") def_tm) ctx0
in Class.prove_instantiation_exit (fn _ => Class.intro_classes_tac ctx1 []) ctx1 end

end