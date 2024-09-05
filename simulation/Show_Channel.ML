structure Show_Channel = struct

fun get_chan ctx typ n =
  Const ( 
  fst (dest_Const (
  Proof_Context.read_const 
    {proper = true, strict = false} 
    ctx 
    (n ^ Channel_Type.ctor_suffix)))
  , typ);

fun mk_chan_show_eq n typ ctx = 
  let open Syntax; open HOLogic; val show = const @{const_name show} in
    (Syntax.check_term ctx (
      mk_Trueprop (eq_const dummyT $ (show $ (get_chan ctx (dummyT --> typ) n $ free "x"))
                                   $ (const @{const_name show_channel} $ mk_literal (Long_Name.base_name n) $ (free "x")))
    ))
  end; 

fun mk_chan_show_fun tname typ chans ctx =
  Function_Fun.add_fun 
    [(Binding.name ("show_" ^ tname), SOME (typ --> @{typ "String.literal"}), NoSyn)]
    (map (fn n => ((Binding.empty_atts, mk_chan_show_eq n typ ctx), [], [])) chans)
    (Function_Fun.fun_config) ctx

fun mk_chan_show_inst tvn tname chans thy =
  let val tvars = map (fn n => ("'" ^ Char.toString (Char.chr n), @{sort "{show,typerep}"})) (97 upto (96 + tvn));
      val ty = Proof_Context.read_type_name {proper = true, strict = false} (Named_Target.theory_init thy) tname;
      val tyco = fst (dest_Type ty);
      val ctx0 = Class.instantiation ([tyco], tvars, \<^sort>\<open>show\<close>) thy;
      val ctx1 = mk_chan_show_fun tname (Type (tyco, map TFree tvars)) chans ctx0;
  in Class.prove_instantiation_exit (fn _ => Class.intro_classes_tac ctx1 []) ctx1
  end

end