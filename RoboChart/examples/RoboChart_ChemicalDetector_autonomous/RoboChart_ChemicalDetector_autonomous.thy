section \<open> Module \label{sec:chem_module}\<close>

theory RoboChart_ChemicalDetector_autonomous
  imports "RoboChart_ChemicalDetector_autonomous_general"
    "RoboChart_ChemicalDetector_autonomous_maincontroller"
    "RoboChart_ChemicalDetector_autonomous_microcontroller"
begin

text \<open>For the channel name in the channel type for the module of a RoboChart model, we use a simple 
name without adding a suffix. This is to make the events in the animation of the model have the 
same name as the event name in the platform. \<close>
chantype Chan_ChemicalDetector =
  terminate :: unit 
  flag :: "InOut"
  gas :: "InOut \<times> 2 Chemical_GasSensor blist[2]"
  obstacle :: "InOut \<times> Location_Loc"
  odometer :: "InOut \<times> core_real"
  resume :: "InOut"
  turn :: "InOut \<times> Chemical_Angle"
  stop :: "InOut"
  randomWalkCall :: unit
  moveCall :: "core_real \<times> Chemical_Angle"
  shortRandomWalkCall :: unit
  (* timeout *)
  stuck_timeout :: "InOut"

definition Memory_ChemicalDetector where
"Memory_ChemicalDetector = skip"

text \<open>The definition below gives a renaming map between the events of @{text MainController} and 
those of the module. For the events of @{text MainController} that are connected to 
@{text MicroController}, we do not change the directions of them here, but invert their directions 
when renaming events of @{text MicroController}. This is to ensure that the output of an event (such as 
@{text stop}) of @{text MainController} is connected to the input of the event of 
@{text MicroController}.
\<close>
definition rename_ChemicalDetector_D__MainController_events where
"rename_ChemicalDetector_D__MainController_events = 
  (enumchanp2_1 (terminate_MainController_C, terminate_C) [()]) @
  (enumchansp2_2 [(gas_MainController_C, gas_C)] InOut_list lseq_gassensor_enum) @
  (enumchansp2_2 [(turn_MainController_C, turn_C)] InOut_list Chemical_Angle_list) @
  (enumchansp2_1 [(stop_MainController_C, stop_C), (resume_MainController_C, resume_C)] InOut_list)
"

definition rename_D__MainController where
"rename_D__MainController idd = (
  (D__MainController idd) \<lbrace>(set rename_ChemicalDetector_D__MainController_events)\<rbrace>) "

text \<open>As mentioned previously, for the events of @{text MicroController} that are connected to 
@{text MainController}, the directions of those renamed events should be opposite. In the definition 
of a renaming map between the events of @{text MicroController} and those of the module, 
the directions of @{text stop} and @{text resume} are inverted. The direction of @{text turn} is not
 inverted here because the event is asynchronously connected. For an asynchronous connection, its 
CSP semantics introduces another buffer process @{text buffer0} below in between the two connected 
events. We invert the directions of events in the buffer process and keep the directions here 
unchanged. This achieves the same effect.
\<close>
definition rename_ChemicalDetector_D__MicroController_events where
"rename_ChemicalDetector_D__MicroController_events = 
  (enumchanp2_1 (terminate_MicroController_C, terminate_C) [()]) @
  (enumchansp2_2 [(obstacle_MicroController_C, obstacle_C)] InOut_list Location_Loc_list) @
  (enumchansp2_2 [(odometer_MicroController_C, odometer_C)] InOut_list rc.core_real_list) @
  (enumchansp2_1 [(flag_MicroController_C, flag_C)] InOut_list) @
  (enumchansp2_1 [(randomWalkCall_MicroController_C, randomWalkCall_C),
      (shortRandomWalkCall_MicroController_C, shortRandomWalkCall_C)] [()]) @
  (enumchansp2_2 [(moveCall_MicroController_C, moveCall_C)]
      rc.core_real_list Chemical_Angle_list) @
  (enumchansp2_2 [(turn_MicroController_C, turn_C)] InOut_list Chemical_Angle_list) @
  [(stop_MicroController_C din, stop_C dout), (stop_MicroController_C dout, stop_C din),
   (resume_MicroController_C din, resume_C dout), (resume_MicroController_C dout, resume_C din)
  ]
  @ (enumchansp2_1 [(stuck_timeout_MicroController_C, stuck_timeout_C)] InOut_list)
"

definition rename_D__MicroController where
"rename_D__MicroController idd = (
  (D__MicroController idd) \<lbrace>(set rename_ChemicalDetector_D__MicroController_events)\<rbrace>)"

text \<open> The connection from @{text MainController} to @{text MicroController} on the event 
@{text turn} is asynchronous, and so its CSP semantics has a buffer in between. 
The buffer is defined below. The function @{term buffer0} defines an one-place buffer (a list) as 
specified in the CSP semantics. When the buffer is full, the only element in the buffer can also be 
overridden.

We note that the direction of the event for input in @{term buffer0} is @{term dout} and that for 
output is @{term din}. This is to ensure the output of the event in @{text MainController} is 
connected to the input of the event in @{text MicroController} asynchronously.
\<close>
definition buffer0 :: "Chemical_Angle list \<Rightarrow> (Chan_ChemicalDetector, Chemical_Angle list) itree"  where
"buffer0 = loop (\<lambda>la. 
  do {guard(length la \<ge> 0 \<and> length la \<le> 1); 
      v \<leftarrow> inp_in turn (set [(dout, a). a \<leftarrow> Chemical_Angle_list]); 
      Ret [snd v]} \<box>
  do {guard(length la > 0); outp turn (din, hd la); Ret []}
)"

definition ChemicalDetector_controllers_sync_events where
"ChemicalDetector_controllers_sync_events = (set (
  [terminate_C ()] @
  (enumchans1 [resume_C, stop_C] InOut_list)
))
"

definition ChemicalDetector_controllers_buffer_events where
"ChemicalDetector_controllers_buffer_events = (set (
  (enumchans2 [turn_C] InOut_list Chemical_Angle_list)
))
"

definition D__ChemicalDetector where
"D__ChemicalDetector (idd::integer) = 
  (
    (
      (par_hide 
        (discard_state (buffer0 []))
        ChemicalDetector_controllers_buffer_events
        (
          (
            (
              (rename_D__MainController idd) 
              \<parallel>\<^bsub> (ChemicalDetector_controllers_sync_events) \<^esub> 
              (rename_D__MicroController idd)
            ) \<setminus> (ChemicalDetector_controllers_sync_events - (set [terminate_C ()]))
          )
          \<parallel>\<^bsub> (set []) \<^esub> 
          Memory_ChemicalDetector
        )
      ) \<lbrakk> set [terminate_C ()] \<Zrres> skip
    ) \<setminus> (set [terminate_C ()])
  )
"

text \<open>This @{term D_ChemicalDetector_sim} below is defined to animate @{term D__ChemicalDetector}. This 
is not part of the semantics of the model, but just for animation. \<close>
definition "D_ChemicalDetector_sim = D__ChemicalDetector 0"
animate1 D_ChemicalDetector_sim

subsubsection \<open> Export code \<close>
export_code
  D__ChemicalDetector
  in Haskell 
  module_name RoboChart_ChemicalDetector
  file_prefix RoboChart_ChemicalDetector 
  (string_classes)

(*
generate_file \<open>code/RoboChart_ChemicalDetector/Simulate.hs\<close> = 
\<open>module Simulate (simulate) where
import Interaction_Trees;
import Partial_Fun;
import System.IO;
import qualified Data.List.Split;
import qualified Data.List;

isPrefixOf              :: (Eq a) => [a] -> [a] -> Bool;
isPrefixOf [] _         =  True;
isPrefixOf _  []        =  False;
isPrefixOf (x:xs) (y:ys)=  x == y && isPrefixOf xs ys;

removeSubstr :: String -> String -> String;
removeSubstr w "" = "";
removeSubstr w s@(c:cs) = (if w `isPrefixOf` s then Prelude.drop (Prelude.length w) s else c : removeSubstr w cs);

replace :: String -> String -> String -> String;
replace old new = Data.List.intercalate new . Data.List.Split.splitOn old;

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

simulate :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Interaction_Trees.Itree e s -> Prelude.IO ();
simulate = simulate_cnt 0;
\<close>

generate_file \<open>code/RoboChart_ChemicalDetector/Main.hs\<close> = 
\<open>import Interaction_Trees;
import Partial_Fun;
import Simulate;
import RoboChart_ChemicalDetector_autonomous;

main :: IO ()
main =
  do
    Simulate.simulate (RoboChart_ChemicalDetector_autonomous.d_ChemicalDetector 0);
\<close>

(*
instance (Prelude.Show a, Prelude.Show b) => Prelude.Show (Bounded_List.Blist a b) where {
  show (Bounded_List.Bmake a b) = Prelude.show b;
};
*)
*)

generate_file \<open>code/RoboChart_ChemicalDetector/Simulate.hs\<close> = 
\<open>
isPrefixOf              :: (Eq a) => [a] -> [a] -> Bool;
isPrefixOf [] _         =  True;
isPrefixOf _  []        =  False;
isPrefixOf (x:xs) (y:ys)=  x == y && isPrefixOf xs ys;

removeSubstr :: String -> String -> String;
removeSubstr w "" = "";
removeSubstr w s@(c:cs) = (if w `isPrefixOf` s then Prelude.drop (Prelude.length w) s else c : removeSubstr w cs);

replace :: String -> String -> String -> String;
replace old new = Data.List.intercalate new . Data.List.Split.splitOn old;

renameGasEvent :: String -> String;
renameGasEvent gas = 
  (
  replace " ()]" "]" (
    replace " ()," "," (
      removeSubstr "Chemical_GasSensor_ext " (
        replace "(PrimTypeC 0) (PrimTypeC 0)" "(0, 0)" (
        replace "(PrimTypeC 0) (PrimTypeC 1)" "(0, 1)" (
        replace "(PrimTypeC 1) (PrimTypeC 0)" "(1, 0)" (
        replace "(PrimTypeC 1) (PrimTypeC 1)" "(1, 1)" (
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
simulate = simulate_cnt 0;
\<close>

generate_file \<open>code/RoboChart_ChemicalDetector/Main.hs\<close> = 
\<open>module Main where {
import RoboChart_ChemicalDetector;

main = simulate (d_ChemicalDetector 0);
}
\<close>

export_generated_files 
  \<open>code/RoboChart_ChemicalDetector/Simulate.hs\<close>
  \<open>code/RoboChart_ChemicalDetector/Main.hs\<close>

end
