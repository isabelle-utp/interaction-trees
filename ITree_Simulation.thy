theory ITree_Simulation
  imports ITree_Extraction
begin

generate_file \<open>code/simulate/Simulate.hs\<close> = \<open>
module Simulate (simulate) where
import Interaction_Trees;
import Partial_Fun;

-- These library functions help us to trim the "_C" strings from pretty printed events

isPrefixOf              :: (Eq a) => [a] -> [a] -> Bool;
isPrefixOf [] _         =  True;
isPrefixOf _  []        =  False;
isPrefixOf (x:xs) (y:ys)=  x == y && isPrefixOf xs ys;

removeSubstr :: String -> String -> String;
removeSubstr w "" = "";
removeSubstr w s@(c:cs) = (if w `isPrefixOf` s then Prelude.drop (Prelude.length w) s else c : removeSubstr w cs);

simulate_cnt :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Prelude.Int -> Itree e s -> Prelude.IO ();
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
       case (Prelude.reads e) of
         []       -> do { Prelude.putStrLn "No parse"; simulate_cnt n t }
         [(v, _)] -> if (v > Prelude.length m)
                       then do { Prelude.putStrLn "Rejected"; simulate_cnt n t }
                       else simulate_cnt 0 (snd (m !! (v - 1)))
     };
simulate_cnt n t@(Vis (Pfun_of_map f)) = 
  do { Prelude.putStr ("Enter an event:");
       e <- Prelude.getLine;
       case (Prelude.reads e) of
         []       -> do { Prelude.putStrLn "No parse"; simulate_cnt n t } 
         [(v, _)] -> case f v of
                       Nothing -> do { Prelude.putStrLn "Rejected"; simulate_cnt n t }
                       Just t' -> simulate_cnt 0 t'
     };

simulate :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Itree e s -> Prelude.IO ();
simulate = simulate_cnt 0;
\<close>

ML \<open> Path.explode "/tmp/hello"\<close>

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
  "(fn path => let open Isabelle_System" ^
  " in copy_dir (Path.append path (Path.make [\"code\", \"simulate\"])) (Path.explode \"" ^ tmp ^ "\") end)"

open Named_Target

fun prep_simulation thy =
  let val (tmp, thy') = simulator_setup thy
  in
  Generated_Files.compile_generated_files 
    (Named_Target.theory_init thy') 
    [([], thy'), ([Path.binding0 (Path.make ["code", "simulate", "Simulate.hs"])], @{theory})] [] []
    (Path.binding0 (Path.make []))
  (Input.string (sim_files_cp (Path.implode tmp))); thy'
  end

fun run_simulation thy =
  case ISim_Path.get thy of
    NONE => error "No simulation" |
    SOME f => writeln (Active.run_system_shell_command ("cd " ^ Path.implode f ^ "; ghci Simulate.hs") "Start Simulation")

end;
\<close>

end