structure Show_Channel = struct

fun get_chan ctx n = 
  Proof_Context.read_const 
    {proper = true, strict = false} 
    ctx 
    (n ^ Channel_Type.ctor_suffix);

fun mk_chan_show_eq n ctx = 
  let open Syntax; open HOLogic; val show = const @{const_name show} in
    Syntax.check_term ctx (
      mk_Trueprop (eq_const dummyT $ (show $ (get_chan ctx n $ free "x"))
                                   $ (const @{const_name show_channel} $ mk_literal (Long_Name.base_name n) $ (free "x")))
    )
  end; 

fun mk_chan_show_fun tname chans ctx =
  let val typ = Syntax.read_typ ctx tname in
  Function_Fun.add_fun 
    [(Binding.name ("show_" ^ tname), SOME (typ --> @{typ "String.literal"}), NoSyn)]
    (map (fn n => ((Binding.empty_atts, mk_chan_show_eq n ctx), [], [])) chans)
    (Function_Fun.fun_config) ctx
  end

fun mk_chan_show_inst tname chans thy =
  let val ctx0 = Class.instantiation_cmd ([tname], [], "show") thy;
      val ctx1 = mk_chan_show_fun tname chans ctx0;
  in Class.prove_instantiation_exit (fn _ => Class.intro_classes_tac ctx1 []) ctx1
  end

end