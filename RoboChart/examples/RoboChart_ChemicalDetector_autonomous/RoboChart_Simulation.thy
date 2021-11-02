subsection \<open> Simulation Harness\<close>
text \<open>This file is copied from @{verbatim "ITree_Simulation.thy"}. The @{verbatim Simulate} 
Haskell module are updated specifically for the autonomous chemical detector example to simplify 
the display of the @{text gas} events. 
\<close>

theory RoboChart_Simulation
  imports Interaction_Trees.ITree_Extraction
  keywords "animate1" :: "thy_defn"
begin

generate_file \<open>code/simulate/Simulate.hs\<close> = \<open>
module Simulate (simulate) where
import Interaction_Trees;
import Partial_Fun;
import System.IO;
import qualified Data.List.Split;
import qualified Data.List;

-- These library functions help us to trim the "_C" strings from pretty printed events

isPrefixOf              :: (Eq a) => [a] -> [a] -> Bool;
isPrefixOf [] _         =  True;
isPrefixOf _  []        =  False;
isPrefixOf (x:xs) (y:ys)=  x == y && isPrefixOf xs ys;

removeSubstr :: String -> String -> String;
removeSubstr w "" = "";
removeSubstr w s@(c:cs) = (if w `isPrefixOf` s then Prelude.drop (Prelude.length w) s else c : removeSubstr w cs);

replace :: String -> String -> String -> String;
replace old new = Data.List.intercalate new . Data.List.Split.splitOn old

renameGasEvent :: String -> String;
renameGasEvent gas = 
  (
  replace " ()]" "]" (
    replace " ()," "," (
      removeSubstr "Chemical_GasSensor_ext " (
        replace "(Chemical_IntensityC 1)" "1)" (
          replace "(Chemical_IntensityC 0)" "0)" (
            replace "(Chemical_ChemC 1)" "(1," (
              replace "(Chemical_ChemC 0)" "(0," (
                replace "(Abs_bit0 (Pos One))" "1" (
                  replace "(Abs_bit0 Zero_int)" "0" (
                    removeSubstr "Chemical_GasSensor_ext " (
                      removeSubstr "Bmake Type" (
                        removeSubstr "_C" gas)))
                  )
                )
              )
            )
          )
        )
      )
    )
  );
{-  (removeSubstr "_C" gas) >>=
  (\e -> removeSubstr "Bmake Type" e) >>=
  (\e -> removeSubstr "Chemical_GasSensor_ext" e);
-}

simulate_cnt :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Prelude.Int -> Itree e s -> Prelude.IO ();
simulate_cnt n (Ret x) = Prelude.putStrLn ("Terminated: " ++ Prelude.show x);
simulate_cnt n (Sil p) = 
  do { if (n == 0) then Prelude.putStrLn "Internal Activity..." else return ();
       if (n >= 2000) then do { Prelude.putStr "Many steps (> 2000); Continue? [Y/N]"; q <- Prelude.getLine; 
                              if (q == "Y") then simulate_cnt 0 p else Prelude.putStrLn "Ended early.";
                            }
                    else simulate_cnt (n + 1) p
     };
simulate_cnt n (Vis (Pfun_of_alist [])) = Prelude.putStrLn "Deadlocked.";
simulate_cnt n t@(Vis (Pfun_of_alist m)) = 
  do { Prelude.putStrLn ("Events:" ++ Prelude.concat (map (\(n, e) -> " (" ++ Prelude.show n ++ ") " ++ renameGasEvent e ++ ";") (zip [1..] (map (Prelude.show . fst) m))));
{-  do { Prelude.putStrLn ("Events:" ++ Prelude.concat (map (\(n, e) -> " (" ++ Prelude.show n ++ ") " ++ removeSubstr "_C" e ++ ";") (zip [1..] (map (Prelude.show . fst) m))));
-}     
       Prelude.putStr ("[Choose: 1-" ++ Prelude.show (Prelude.length m) ++ "]: ");
       e <- Prelude.getLine;
       if (e == "q" || e == "Q") then
         Prelude.putStrLn "Simulation terminated"
       else
       case (Prelude.reads e) of
         []       -> if (Prelude.length m == 1)
                       then do { Prelude.putStrLn (renameGasEvent (Prelude.show (fst (m !! 0)))) ; simulate_cnt 0 (snd (m !! (0)))}
                       else do { Prelude.putStrLn "No parse"; simulate_cnt n t }
         [(v, _)] -> if (v > Prelude.length m)
                       then do { Prelude.putStrLn "Rejected"; simulate_cnt n t }
                       else do { Prelude.putStrLn (renameGasEvent (Prelude.show (fst (m !! (v-1))))) ; simulate_cnt 0 (snd (m !! (v - 1)))}
     };
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

simulate :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Itree e s -> Prelude.IO ();
simulate p = do { hSetBuffering stdout NoBuffering; putStrLn ""; putStrLn "Starting ITree Simulation..."; simulate_cnt 0 p }
\<close>

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
    mkdir tmp; (tmp, ISim_Path.put (SOME tmp) thy)
  end

fun sim_files_cp tmp = 
  "(fn path => let open Isabelle_System; val path' = Path.append path (Path.make [\"code\", \"simulate\"])" ^
  " in writeln \"Compiling animation...\"; bash (\"cd \" ^ Path.implode path' ^ \"; ghc Simulation >> /dev/null\") ; copy_dir path' (Path.explode \"" ^ tmp ^ "\") end)"

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
  in
  generate_file (Path.binding0 (Path.make ["code", "simulate", "Simulation.hs"]), (Input.string (simulation_file model thy))) ctx' |>
  (fn ctx' => 
    let val _ = compile_generated_files 
                 ctx'
                 [([], (Local_Theory.exit_global ctx')), ([Path.binding0 (Path.make ["code", "simulate", "Simulate.hs"])], @{theory})] 
                 [] [([Path.binding0 (Path.make ["code", "simulate", "Simulation"])], SOME true)]
                 (Path.binding0 (Path.make []))
                 (Input.string (sim_files_cp (Path.implode tmp)))
    in ctx' end)


(*  (fn ctx => let val _ = export_generated_files ctx [([], Local_Theory.exit_global ctx), ([], @{theory})] in ctx end) *)
  end

fun run_simulation thy =
  case ISim_Path.get thy of
    NONE => error "No animation" |
    SOME f => writeln (Active.run_system_shell_command (SOME (Path.implode f)) ("./Simulation") "Start animation")

fun simulate model thy =
  let val ctx = Named_Target.theory_init thy
      val ctx' =
        (Code_Target.export_code true [Code.read_const (Local_Theory.exit_global ctx) model] [((("Haskell", ""), SOME ({physical = false}, (Path.explode "simulate", Position.none))), (Token.explode (Thy_Header.get_keywords' @{context}) Position.none "string_classes"))] ctx)
        |> prep_simulation model (Context.theory_name thy)
  in run_simulation (Local_Theory.exit_global ctx'); (Local_Theory.exit_global ctx')
  end 

end;
\<close>

ML \<open>
  Outer_Syntax.command @{command_keyword animate1} "animate an ITree"
  (Parse.name >> (fn model => Toplevel.theory (ITree_Simulator.simulate model)))
\<close>

end