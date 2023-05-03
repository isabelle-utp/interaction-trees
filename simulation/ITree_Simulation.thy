subsection \<open> Simulation Harness \<close>

theory ITree_Simulation                 
  imports Executable_Universe Channel_Type_Rep Animation_Event "Interaction_Trees.ITrees" 
  keywords "animate" :: "thy_defn"
begin

(*
text \<open> The following additional constructor for partial functions allows us to request an
  value covered by @{typ uval}. \<close>

definition pfun_of_ufun :: "(uval \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> utyp \<Rightarrow> (uval \<Rightarrow> 'b) \<Rightarrow> 'e \<Zpfun> 'b" where
"pfun_of_ufun c t P = (\<lambda> e\<in>{build\<^bsub>c\<^esub> v | v. v \<in> uvals t} \<bullet> P (the (match\<^bsub>c\<^esub> e)))"

lemma map_pfun_pfun_of_ufun [code]: "map_pfun f (pfun_of_ufun c t P) = pfun_of_ufun c t (f \<circ> P)"
  by (simp add: pfun_of_ufun_def pfun_eq_iff)


record uevent =
  uev_name :: uname
  uev_outp :: uval
  uev_inp  :: uval

term ev_val

(*
declare [[typedef_overloaded]]

datatype ('e, 'b) chf =
  ChanF (chf_chn: "'e name") \<comment> \<open> The channel name \<close>
        (chf_mk_ev: "(uval \<times> uval) \<Rightarrow> uval") \<comment> \<open> Build an event from the input and output params \<close>
        (chf_dest_ev: "uval \<Rightarrow> (uval \<times> uval)")
        (chf_out: "uval") \<comment> \<open> The value output by the process (displayed in the animator) \<close>
        (chf_typ: "utyp") \<comment> \<open> The type of data requested by the animator \<close>
        (chf_cont: "uval \<Rightarrow> 'b") \<comment> \<open> The continuation for each kind of value received \<close>

term event_of

definition pfun_of_chfun :: "('e::uchantyperep, 'b) chf \<Rightarrow> 'e \<Zpfun> 'b" where 
  "pfun_of_chfun chf 
    = (\<lambda> e\<in>{e. \<exists> inp outp. uchan_dest e = event_of (label_of (chf_chn chf), (chf_mk_ev chf (inp, outp)))} 
       \<bullet> (chf_cont chf) undefined)"

code_datatype pfun_of_alist pfun_of_map pfun_of_ufun pfun_of_chfun pfun_entries
*)

datatype ('e, 'b) chf =
  ChanF (chf_chn: "(uevent \<Longrightarrow>\<^sub>\<triangle> 'e)") \<comment> \<open> The channel, including a name, output value, and input value \<close>
        (chf_out: "uname \<times> uval") \<comment> \<open> The value output by the process (displayed in the animator) \<close>
        (chf_typ: "utyp") \<comment> \<open> The type of data requested by the animator \<close>
        (chf_cont: "uval \<Rightarrow> 'b") \<comment> \<open> The continuation for each kind of value received \<close>

definition pfun_of_chfun :: 
  "('e, 'b) chf \<Rightarrow> 'e \<Zpfun> 'b" where
"pfun_of_chfun chf = 
    (\<lambda> e\<in>{build\<^bsub>chf_chn chf\<^esub> \<lparr> uev_name = fst (chf_out chf)
                             , uev_outp = snd (chf_out chf)
                             , uev_inp = v \<rparr> 
          | v. v \<in> uvals (chf_typ chf)} 
    \<bullet> (chf_cont chf) (uev_inp (the (match\<^bsub>chf_chn chf\<^esub> e))))"

definition
  "map_chfun f chf = ChanF (chf_chn chf) (chf_out chf) (chf_typ chf) (f \<circ> chf_cont chf)"

lemma map_pfun_pfun_of_chfun: 
  "map_pfun f (pfun_of_chfun chf) = pfun_of_chfun (map_chfun f chf)"
  by (simp add: map_chfun_def pfun_of_chfun_def pfun_eq_iff)

lemma "pfun_app (pfun_of_chfun chf) e = undefined"
  apply (simp add: pfun_of_chfun_def)
  apply (subst pabs_apply)
    apply simp_all
  oops

definition pfun_of_chfuns ::
  "('e, 'b) chf list \<Rightarrow> 'e \<Zpfun> 'b" where
"pfun_of_chfuns chfs = foldr (\<lambda> c f. pfun_of_chfun c \<oplus> f) chfs {}\<^sub>p"

lemma map_pfun_pfun_of_chfuns [code]:
  "map_pfun f (pfun_of_chfuns chfs) = pfun_of_chfuns (map (map_chfun f) chfs)"
  by (induct chfs, simp_all add: pfun_of_chfuns_def map_pfun_pfun_of_chfun)

lemma pfun_of_chfuns_Nil [simp]: "pfun_of_chfuns [] = {}\<^sub>p"
  by (simp add: pfun_of_chfuns_def)

lemma pfun_of_chfuns_Cons [simp]: "pfun_of_chfuns (chf # chfs) = pfun_of_chfun chf \<oplus> pfun_of_chfuns chfs"
  by (simp add: pfun_of_chfuns_def)

lemma pfun_of_chfuns_override [code]: 
  "pfun_of_chfuns chfs1 \<oplus> pfun_of_chfuns chfs2 = pfun_of_chfuns (chfs1 @ chfs2)"
  by (induct chfs1 arbitrary: chfs2; simp add: override_assoc; metis override_assoc)

definition prism_comp :: "('a \<Longrightarrow>\<^sub>\<triangle> 'b) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'c) \<Rightarrow> 'a \<Longrightarrow>\<^sub>\<triangle> 'c" where
"prism_comp X Y = \<lparr> prism_match = (\<lambda> s. Option.bind (match\<^bsub>Y\<^esub> s) match\<^bsub>X\<^esub>)
                  , prism_build = build\<^bsub>Y\<^esub> \<circ> build\<^bsub>X\<^esub> \<rparr>"

definition itree_chf :: "uname \<Rightarrow> ('inp::uvals \<times> 'out::uvals \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'out \<Rightarrow> ('inp \<Rightarrow> ('e, 's) itree) \<Rightarrow> ('e, ('e, 's) itree) chf" where
"itree_chf n c out P = ChanF undefined (n, to_uval out) UTYPE('inp) (P \<circ> from_uval)"
*)

(* The conceptual type for the ITree structure we'd like is as below: *)

typ \<open> ('inp::uvals \<times> 'out::uvals \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'out \<Rightarrow> ('inp \<Rightarrow> ('e, 's) itree) \<close>

code_datatype pfun_of_alist pfun_of_map pfun_of_animevs pfun_entries

code_identifier
  code_module ITree_Simulation \<rightharpoonup> (Haskell) Interaction_Trees
| code_module Partial_Fun \<rightharpoonup> (Haskell) Interaction_Trees
| code_module Executable_Universe \<rightharpoonup> (Haskell) Interaction_Trees
| code_module Channel_Type_Rep \<rightharpoonup> (Haskell) Interaction_Trees
| code_module Animation_Event \<rightharpoonup> (Haskell) Interaction_Trees
| code_module Interaction_Trees \<rightharpoonup> (Haskell) Interaction_Trees

generate_file \<open>code/simulate/Simulate.hs\<close> = \<open>
module Simulate (simulate) where
import Interaction_Trees;
import Prelude;
import System.IO;
import Data.Ratio;

-- These library functions help us to trim the "_C" strings from pretty printed events

isPrefixOf              :: (Eq a) => [a] -> [a] -> Bool;
isPrefixOf [] _         =  True;
isPrefixOf _  []        =  False;
isPrefixOf (x:xs) (y:ys)=  x == y && isPrefixOf xs ys;

removeSubstr :: String -> String -> String;
removeSubstr w "" = "";
removeSubstr w s@(c:cs) = (if w `isPrefixOf` s then Prelude.drop (Prelude.length w) s else c : removeSubstr w cs);

instance Show Uval where
  show UnitV = "()"
  show (BoolV x) = show x
  show (IntV x) = show x
  show (RatV x) = show (fromRational x)
  show (StringV x) = show x
  show (EnumV _ x) = x
  show (PairV xy) = show xy
  show (ListV typ xs) = show xs

instance Show Utyp where
  show UnitT = "()"
  show BoolT = "bool"
  show IntT = "int"
  show RatT = "rat"
  show StringT = "string"
  show (EnumT s) = "enum"
  show (PairT (s, t)) = "(" ++ show s ++ ", " ++ show t ++ ")"
  show (ListT s) = "[" ++ show s ++ "]"

show_animev :: Animev a b -> String
show_animev (AnimInput (Name_of (n, t)) _ _) = n ++ "?<"  ++ show t ++ ">"
show_animev (AnimOutput (Name_of (n, t)) v _) = n ++ "!" ++ show v

mk_readUval :: Read a => (a -> Uval) -> String -> IO Uval
mk_readUval f n = 
  do { putStr ("Input <" ++ n ++ "> value: ")
     ; e <- getLine
     ; return (f (read e)) }

readUtyp :: Utyp -> IO Uval
readUtyp BoolT = mk_readUval BoolV "bool"
readUtyp IntT = mk_readUval IntV "int"
readUtyp UnitT = return UnitV

simulate_cnt :: (Eq e, Prelude.Show e, Prelude.Show s) => Prelude.Int -> Itree e s -> Prelude.IO ();
simulate_cnt n (Ret x) = Prelude.putStrLn ("Terminated: " ++ Prelude.show x);
simulate_cnt n (Sil p) = 
  do { if (n == 0) then Prelude.putStrLn "Internal Activity..." else return ();
       if (n >= 20) then do { Prelude.putStr "Many steps (> 20); Continue? [Y/N]"; q <- Prelude.getLine; 
                              if (q == "Y") then simulate_cnt 0 p else Prelude.putStrLn "Ended early.";
                            }
                    else simulate_cnt (n + 1) p
     };
simulate_cnt n (Vis (Pfun_of_alist [])) = Prelude.putStrLn "Deadlocked.";
simulate_cnt n t@(Vis (Pfun_of_alist m)) = 
  do { Prelude.putStrLn ("Events:" ++ Prelude.concat (map (\(n, e) -> " (" ++ Prelude.show n ++ ") " ++ removeSubstr "_C" e ++ ";") (zip [1..] (map (Prelude.show . fst) m))));
       e <- Prelude.getLine;
       if (e == "q" || e == "Q") then
         Prelude.putStrLn "Simulation terminated"
       else
       case (Prelude.reads e) of
         []       -> do { Prelude.putStrLn "No parse"; simulate_cnt n t }
         [(v, _)] -> if (v > Prelude.length m)
                       then do { Prelude.putStrLn "Rejected"; simulate_cnt n t }
                       else simulate_cnt 0 (snd (m !! (v - 1)))
     };                                                            
simulate_cnt n t@(Vis (Pfun_of_animevs m)) =
  do { putStrLn ("Events:" ++ concat (map (\(i, e) -> " (" ++ show i ++ ") " ++ show_animev e ++ ";") (zip [1..] m)));
       e <- Prelude.getLine;
       if (e == "q" || e == "Q") then
         Prelude.putStrLn "Simulation terminated"
       else
       case (Prelude.reads e) of
         []       -> do { Prelude.putStrLn "No parse"; simulate_cnt n t }
         [(v, _)] -> if (v > Prelude.length m)
                       then do { Prelude.putStrLn "Rejected"; simulate_cnt n t }
                       else case (m!!(v - 1)) of
                              (AnimInput (Name_of (nm, typ)) b p) ->
                                do { val <- readUtyp typ -- Ask for any inputs needed
                                   ; if b val 
                                     then simulate_cnt 0 (p val) 
                                     else do { Prelude.putStrLn "Rejected"; simulate_cnt n t }
                                   }
                              (AnimOutput (Name_of (n, t)) v p) -> simulate_cnt 0 p };


simulate :: (Eq e, Prelude.Show e, Prelude.Show s) => Itree e s -> Prelude.IO ();
simulate p = do { hSetBuffering stdout NoBuffering; putStrLn ""; putStrLn "Starting ITree Simulation..."; simulate_cnt 0 p }


\<close>

(* The code below is the case for an opaque map function. It depends on there being a Read instance. *)

(*
simulate_cnt n t@(Vis (Pfun_of_map f)) = 
  do { Prelude.putStr ("Enter an event:");
       e <- Prelude.getLine;
       if (e == "q" || e == "Q") then
         Prelude.putStrLn "Simulation terminated"
       else
       case (Prelude.reads e) of
         []       -> do { Prelude.putStrLn "No parse"; simulate_cnt n t } 
         [(v, _)] -> case f v of
                       Nothing -> do { Prelude.putStrLn "Rejected"; simulate_cnt n t }
                       Just t' -> simulate_cnt 0 t'
     };    
*)

(*
simulate_cnt n t@(Vis (Pfun_of_ufun chan typ m)) = 
  do { v <- readUtyp typ; 
       simulate_cnt 0 (m v) }
simulate_cnt n (Vis (Pfun_of_chfuns [])) = Prelude.putStrLn "Deadlocked.";
simulate_cnt n t@(Vis (Pfun_of_chfuns m)) =
  do { Prelude.putStrLn ("Events:" ++ Prelude.concat (map (\(i, ChanF c (n, p) _ _) -> " (" ++ show i ++ ") " ++ n ++ " " ++ show p ++ ";") (zip [1..] m)));
       e <- Prelude.getLine;
       if (e == "q" || e == "Q") then
         Prelude.putStrLn "Simulation terminated"
       else
       case (Prelude.reads e) of
         []       -> do { Prelude.putStrLn "No parse"; simulate_cnt n t }
         [(v, _)] -> if (v > Prelude.length m)
                       then do { Prelude.putStrLn "Rejected"; simulate_cnt n t }
                       else let (typ, p) = (\(ChanF _ _ t p) -> (t, p)) (m!!(v - 1)) 
                            in do { val <- readUtyp typ
                                  ; simulate_cnt 0 (p val) } -- Ask for any inputs needed
     };                                                            

*)

ML \<open> 

structure ITree_Simulator =
struct

structure ISim_Path = Theory_Data
  (type T = Path.T option
   val empty = NONE
   val extend = I
   val merge = fn (_, y) => y);

fun simulator_setup thy = 
  let open Isabelle_System; val tmp = Path.expand (create_tmp_path "itree-simulate" "")
  in case (ISim_Path.get thy) of NONE => () | SOME oldtmp => rm_tree oldtmp;
    make_directory tmp; (tmp, ISim_Path.put (SOME tmp) thy)
  end

fun sim_files_cp ghc tmp = 
  "(fn path => let open Isabelle_System; val path' = Path.append path (Path.make [\"code\", \"simulate\"])" ^
  " in writeln \"Compiling animation...\"; bash (\"cd \" ^ Path.implode path' ^ \"; " ^ ghc ^ " Simulation >> /dev/null\") ; copy_dir path' (Path.explode \"" ^ tmp ^ "\") end)";

open Named_Target

fun firstLower s =
  case String.explode s of [] => "" | c :: cs => String.implode (Char.toLower c :: cs);

fun simulation_file model thy =
  "module Main where \n" ^
  "import Simulate; \n" ^
  "import " ^ thy ^ "; \n" ^
  "main = simulate " ^ firstLower model

fun prep_simulation model thy ctx =
  let open Generated_Files; 
      val (tmp, thy') = simulator_setup (Local_Theory.exit_global ctx);
      val ctx' = Named_Target.theory_init thy'
      val ghc = getenv "ISABELLE_GHC"
      val _ = if (ghc = "") then error "GHC is not set up. Please set the environment variable ISABELLE_GHC." else ()
  in
  generate_file (Path.binding0 (Path.make ["code", "simulate", "Simulation.hs"]), (Input.string (simulation_file model thy))) ctx' |>
  (fn ctx' => 
    let val _ = compile_generated_files 
                 ctx'
                 [([], (Local_Theory.exit_global ctx')), ([Path.binding0 (Path.make ["code", "simulate", "Simulate.hs"])], @{theory})] 
                 [] [([Path.binding0 (Path.make ["code", "simulate", "Simulation"])], SOME true)]
                 (Path.binding0 (Path.make []))
                 (Input.string (sim_files_cp ghc (Path.implode tmp)))
    in ctx' end)
  end

fun run_simulation thy =
  
  case ISim_Path.get thy of
    NONE => error "No animation" |
    SOME f => 
      let val p = Path.append f (Path.make ["simulate"])
      in writeln (Active.run_system_shell_command (SOME (Path.implode p)) ("./Simulation") "Start animation") end

fun simulate model thy =
  let val ctx = Named_Target.theory_init thy
      val ctx' =
        (Code_Target.export_code true [Code.read_const (Local_Theory.exit_global ctx) model] [((("Haskell", ""), SOME ({physical = false}, (Path.explode "simulate", Position.none))), [])] ctx)
        |> prep_simulation model (Context.theory_name thy)
  in run_simulation (Local_Theory.exit_global ctx'); (Local_Theory.exit_global ctx')
  end 

end;
\<close>

definition show_channel :: "String.literal \<Rightarrow> 'a::show \<Rightarrow> String.literal" where
"show_channel c p = c + STR '' '' + show p"

ML_file \<open>Show_Channel.ML\<close>

ML \<open>
  Outer_Syntax.command @{command_keyword animate} "animate an ITree"
  (Parse.name >> (fn model => Toplevel.theory (ITree_Simulator.simulate model)));

\<close>

end