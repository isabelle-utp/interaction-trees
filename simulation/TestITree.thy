theory TestITree
  imports "Interaction_Trees.ITrees" "ITree_Simulation.ITree_Simulation" "ITree_UTP.ITree_CSP"
begin

chantype chan = 
(*  UV :: uval  *)
  Input :: integer
  Output :: integer
  State :: "integer list"

instantiation chan :: pre_uchantyperep
begin

definition uchans_chan :: "chan itself \<Rightarrow> String.literal \<Zpfun> utyp"
  where "uchans_chan x = {STR ''Input'' \<mapsto> IntT, STR ''Output'' \<mapsto> IntT, STR ''State'' \<mapsto> ListT IntT}"

definition unamelist_chan :: "chan itself \<Rightarrow> uname list" where
"unamelist_chan x = [STR ''Input'', STR ''Output'', STR ''State'']"

instance
  by (intro_classes, auto simp add: uchans_chan_def unamelist_chan_def)

end

lemma UNAMES_chan [simp]: "UNAMES(chan) = {STR ''Input'', STR ''Output'', STR ''State''}"
  by (auto simp add: unames_def uchans_chan_def)

lemma UTYPES_chan [simp]: 
  "UCHANTYPE(chan, STR ''Input'') = UTYPE(integer)"
  "UCHANTYPE(chan, STR ''Output'') = UTYPE(integer)"
  "UCHANTYPE(chan, STR ''State'') = UTYPE(integer list)"
  by (simp_all add: uchans_chan_def utyp_unit_def utyp_integer_def utyp_list_def)

abbreviation "n_Input \<equiv> mkname[chan] STR ''Input''"
abbreviation "n_Output \<equiv> mkname[chan] STR ''Output''"
abbreviation "n_State \<equiv> mkname[chan] STR ''State''"

lemma names: "ev_name x \<in> {n_Input, n_Output, n_State}"
  using ev_name_UNAMES[of x] by auto

instantiation chan :: uchantyperep
begin

definition uchan_mk_chan :: "chan event \<Rightarrow> chan"
  where "uchan_mk_chan e = (if (ev_name e = n_Input) then Input_C (ev_val e)
                            else if (ev_name e = n_Output) then Output_C (ev_val e)
                            else State_C (ev_val e))"

fun uchan_dest_chan :: "chan \<Rightarrow> chan event" where
"uchan_dest (Input_C v) = mk_event n_Input v" |
"uchan_dest (Output_C v) = mk_event n_Output v" |
"uchan_dest (State_C v) = mk_event n_State v"

instance
  apply (intro_classes)
   apply (auto simp add: uchan_mk_chan_def mkevent_eq_ev_iff)
  using names apply fastforce
  apply (case_tac y; simp)+
  done

end

lift_definition c_Input :: "(integer, chan) channel" is "n_Input" .
lift_definition c_State :: "(integer list, chan) channel" is "n_State" .
lift_definition c_Output :: "(integer, chan) channel" is "n_Output" .

lemma Input_channel_prism [code_unfold]: "Input = channel_prism (c_Input)"
  apply (simp add: channel_prism_def Input_def ctor_prism_def, transfer)
  apply auto
  apply (auto simp add: fun_eq_iff)
  apply (metis chan.sel(1) uchan_dest_inv uchan_mk_chan_def)
    apply (metis chan.collapse(1) ev_name_mkevent uchan_dest_chan.simps(1))
   apply (case_tac x; simp)
  apply (case_tac x; simp)
  apply (metis uchan_dest_chan.simps(1) uchan_dest_inv)
  done

lemma Output_channel_prism [code_unfold]: "Output = channel_prism (c_Output)"
  apply (simp add: channel_prism_def Output_def ctor_prism_def, transfer)
  apply auto
  apply (auto simp add: fun_eq_iff)
  apply (metis chan.disc(4) chan.sel(2) uchan_dest_inv uchan_mk_chan_def)
  using is_Output_C_def apply force
   apply (metis chan.discI(2) uchan_dest_chan.simps(1) uchan_dest_chan.simps(2) uchan_dest_inv uchan_mk_chan_def)
  apply (metis uchan_dest_chan.simps(2) uchan_dest_inv)
  done

definition inp_prism :: "('a \<Longrightarrow>\<^sub>\<triangle> 'c) \<Rightarrow> ('a \<times> unit \<Longrightarrow>\<^sub>\<triangle> 'c)" where
"inp_prism e = \<lparr> prism_match = (\<lambda> x. do { v \<leftarrow> match\<^bsub>e\<^esub> x; Some (v, ()) })
               , prism_build = (\<lambda> (x, _). build\<^bsub>e\<^esub> x) \<rparr>"

instantiation chan :: "show"
begin

fun show_chan :: "chan \<Rightarrow> String.literal" where
(* "show_chan (UV_C x) = STR ''<UVal>''" | *)
"show_chan (Input_C x) = STR ''Input'' + show x" |
"show_chan (Output_C x) = STR ''Output '' + show x" |
"show_chan (State_C xs) = STR ''State '' + show xs"

instance ..

end

term prism_create

term option.map_option

term prism_build

definition uval_lens :: "'a::uvals \<Longrightarrow> uval" ("uval\<^sub>L") where
"uval_lens = \<lparr> lens_get = from_uval, lens_put = (\<lambda> s. to_uval) \<rparr>"

lemma "mwb_lens uval\<^sub>L"
  by (unfold_locales; simp add: uval_lens_def)

definition mk_eq_ITree :: "('e::{equal,show}, 's) itree \<Rightarrow> ('e,'s) itree" where
"mk_eq_ITree x = x"

find_theorems inp_in_where

declare inp_in_where_map_code [code_unfold del]

lemma wf_c_Input [simp, code_unfold]: "wf_channel c_Input"
  by (simp add: wf_channel_def c_Input.rep_eq)

lemma wf_c_Output [simp, code_unfold]: "wf_channel c_Output"
  by (simp add: c_Output.rep_eq wf_channel_def)


lemma inp_as_animev [code_unfold]:
  "wf_channel c \<Longrightarrow> inp_in_where (channel_prism c) A P = animevs [anim_inp c True (\<lambda> v. v \<in> A \<and> P v) Ret]"
  apply (simp add: animevs_def channel_prism_def inp_in_where_def pfun_eq_iff pfun_of_animevs_def)
  using to_uval_typ apply (auto simp add: animevs_def pfun_of_animevs_def anim_inp_def inp_in_where_def pfun_eq_iff wf_channel_def channel_prism_def channel_build_def channel_match_def mk_event_event_of_def ev_name_labelled_event ev_uval.rep_eq ev_val.rep_eq)
  apply (metis (mono_tags, lifting) Product_Type.Collect_case_prodD case_prodI event_of_inverse label_of.rep_eq mem_Collect_eq of_name snd_conv to_uval_inv to_uval_typ)
  apply (metis (mono_tags, lifting) case_prodI event_of_inverse label_of_in_names mem_Collect_eq snd_conv to_uval_inv to_uval_typ)
  using from_uval_inv image_iff apply fastforce
  apply (simp add: event_of_inverse)
  apply (subst pabs_apply)
    apply auto
  apply (metis (mono_tags, lifting) case_prodI event_of_inverse label_of_in_names mem_Collect_eq snd_conv to_uval_inv to_uval_typ)
  apply (subst pabs_apply)
    apply auto
  apply (metis (mono_tags, lifting) case_prodI event_of_inverse label_of_in_names mem_Collect_eq snd_conv to_uval_inv to_uval_typ)
  done

term outp

term anim_outp

lemma outp_as_animev [code_unfold]:
  "wf_channel c \<Longrightarrow> outp (channel_prism c) v = animevs [anim_outp c True v (Ret ())]"
  apply (simp add: animevs_def channel_prism_def outp_def pfun_eq_iff pfun_of_animevs_def)
  using to_uval_typ apply (auto simp add: animevs_def pfun_of_animevs_def anim_outp_def inp_in_where_def pfun_eq_iff wf_channel_def channel_prism_def channel_build_def channel_match_def mk_event_event_of_def ev_name_labelled_event ev_uval.rep_eq ev_val.rep_eq)
  done


definition 
  "test_anim_inp = 
      mk_eq_ITree (loop (\<lambda> s::integer list. 
        (animevs ([anim_inp c_Input True (\<lambda> v. True) (\<lambda> v. Ret (s @ [v]))
                  ,anim_outp c_State True s (Ret s)
                  ,anim_outp c_Output (s \<noteq> []) (hd s) (Ret (tl s))]))) [])"

term outp

term map_prod

definition
"test_anim_inp2 = 
  mk_eq_ITree (loop (\<lambda> s::integer list. 
                     (inp Input \<bind> (\<lambda> x. Ret (x # s))) \<box> (guard (s \<noteq> []) >> outp Output (hd s) >> (Ret (tl s)))) [])" 
        
export_code test_anim_inp in Haskell

declare map_pfun_pfun_of_animevs [code]

declare pfun_of_aevs_override [code]

animate test_anim_inp2

typ integer

term rat_of_rational

term int_of_integer



find_theorems quotient_of
  
animate testITree2

end