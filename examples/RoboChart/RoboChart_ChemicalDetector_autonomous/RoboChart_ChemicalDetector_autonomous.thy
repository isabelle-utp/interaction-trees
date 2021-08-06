section \<open> Animation of the autonomous chemical detector RoboChart model \<close>
text \<open> This theory aims for animation of a trivial RoboChart model based on its CSP
 semantics. 
\<close>
theory RoboChart_ChemicalDetector_autonomous
  imports "RoboChart_ChemicalDetector_autonomous_general"
    "RoboChart_ChemicalDetector_autonomous_maincontroller"
    "RoboChart_ChemicalDetector_autonomous_microcontroller"
begin

subsection \<open> Module \<close>
chantype Chan_ChemicalDetector =
  terminate_ChemicalDetector :: unit 
  flag_ChemicalDetector :: "InOut"
  gas_ChemicalDetector :: "InOut \<times> 2 Chemical_GasSensor[2]blist"
  obstacle_ChemicalDetector :: "InOut \<times> Location_Loc"
  odometer_ChemicalDetector :: "InOut \<times> core_real"
  resume_ChemicalDetector :: "InOut"
  turn_ChemicalDetector :: "InOut \<times> Chemical_Angle"
  stop_ChemicalDetector :: "InOut"
  randomeWalkCall_ChemicalDetector :: unit
  moveCall_ChemicalDetector :: "core_real \<times> Chemical_Angle"
  shortRandomWalkCall_ChemicalDetector :: unit

definition Memory_ChemicalDetector where
"Memory_ChemicalDetector = skip"

definition rename_ChemicalDetector_D__MainController_events where
"rename_ChemicalDetector_D__MainController_events = 
  (enumchanp2_1 (terminate_MainController_C, terminate_ChemicalDetector_C) [()]) @
  (enumchansp2_2 [(gas_MainController_C, gas_ChemicalDetector_C)] InOut_list lseq_gassensor_enum) @
  (enumchansp2_2 [(turn_MainController_C, turn_ChemicalDetector_C)] InOut_list Chemical_Angle_list) @
  (enumchansp2_1 [(stop_MainController_C, stop_ChemicalDetector_C), 
      (resume_MainController_C, resume_ChemicalDetector_C)] InOut_list) 
"

definition rename_D__MainController where
"rename_D__MainController idd = 
  rename (set rename_ChemicalDetector_D__MainController_events) (D__MainController idd)"

definition rename_ChemicalDetector_D__MicroController_events where
"rename_ChemicalDetector_D__MicroController_events = 
  (enumchanp2_1 (terminate_MicroController_C, terminate_ChemicalDetector_C) [()]) @
  (enumchansp2_2 [(obstacle_MicroController_C, obstacle_ChemicalDetector_C)]  
      InOut_list Location_Loc_list) @
  (enumchansp2_2 [(odometer_MicroController_C, odometer_ChemicalDetector_C)]  
      InOut_list rc.core_real_list) @
  (enumchansp2_2 [(turn_MicroController_C, turn_ChemicalDetector_C)] 
      InOut_list Chemical_Angle_list) @
  (enumchansp2_1 [(flag_MicroController_C, flag_ChemicalDetector_C)] InOut_list) @
  (enumchansp2_1 [(randomeWalkCall_MicroController_C, randomeWalkCall_ChemicalDetector_C),
      (shortRandomWalkCall_MicroController_C, shortRandomWalkCall_ChemicalDetector_C)] [()]) @
  (enumchansp2_2 [(moveCall_MicroController_C, moveCall_ChemicalDetector_C)]
      rc.core_real_list Chemical_Angle_list) @
  \<comment> \<open> stop.in of MicroController -> stop.out of ManController through stop_ChemicalDetector_C\<close>
  [(stop_MicroController_C din, stop_ChemicalDetector_C dout),
    (stop_MicroController_C dout, stop_ChemicalDetector_C din),
    (resume_MicroController_C din, resume_ChemicalDetector_C dout),
    (resume_MicroController_C dout, resume_ChemicalDetector_C din)
  ]
"

definition rename_D__MicroController where
"rename_D__MicroController idd = 
  rename (set rename_ChemicalDetector_D__MicroController_events) (D__MicroController idd)"

text \<open> The connection from MainController to MicroController on the event turn is asynchronous, 
and so its CSP semantics has a buffer in between. The buffer is defined below.
\<close>
definition buffer0 :: "Chemical_Angle list \<Rightarrow> (Chan_ChemicalDetector, Chemical_Angle list) itree"  where
"buffer0 = loop (\<lambda>la. 
  do {guard(length la = 0); 
      v \<leftarrow> inp_in turn_ChemicalDetector (set [(dout, a). a \<leftarrow> Chemical_Angle_list]); 
      Ret [snd v]} \<box>
  do {guard(length la > 0); 
      x \<leftarrow> inp_in turn_ChemicalDetector (set [(dout, a). a \<leftarrow> Chemical_Angle_list]); 
      Ret [snd x]}  \<box>
  do {guard(length la > 0); outp turn_ChemicalDetector (din, hd la); Ret []}
)"

definition ChemicalDetector_controllers_sync_events where
"ChemicalDetector_controllers_sync_events = (set (
  [terminate_ChemicalDetector_C ()] @
  (enumchans1 [resume_ChemicalDetector_C, stop_ChemicalDetector_C] InOut_list)
))
"

definition ChemicalDetector_controllers_buffer_events where
"ChemicalDetector_controllers_buffer_events = (set (
  (enumchans2 [turn_ChemicalDetector_C] InOut_list Chemical_Angle_list)
))
"

definition D__ChemicalDetector where
"D__ChemicalDetector (idd::integer) = 
  (hide
    (
      (par_hide 
        (discard_state (buffer0 []))
        ChemicalDetector_controllers_buffer_events
        (
          (
            hide 
              (
                (rename_D__MainController idd) 
                \<parallel>\<^bsub> (ChemicalDetector_controllers_sync_events) \<^esub> 
                (rename_D__MicroController idd)
              )
              (ChemicalDetector_controllers_sync_events - (set [terminate_ChemicalDetector_C ()]))
          )
          \<parallel>\<^bsub> (set []) \<^esub> 
          Memory_ChemicalDetector
        )
      ) \<lbrakk> set [terminate_ChemicalDetector_C ()] \<Zrres> skip
    )
    (set [terminate_ChemicalDetector_C ()])
  )
"

subsection \<open> Export code \<close>
export_code
  D__ChemicalDetector
  in Haskell 
  (* module_name RoboChart_ChemicalDetector *)
  file_prefix RoboChart_ChemicalDetector 
  (string_classes)

generate_file \<open>code/RoboChart_ChemicalDetector/Simulate.hs\<close> = 
\<open>module Simulate (simulate) where
import qualified Interaction_Trees;
import qualified Partial_Fun;

isPrefixOf              :: (Eq a) => [a] -> [a] -> Bool;
isPrefixOf [] _         =  True;
isPrefixOf _  []        =  False;
isPrefixOf (x:xs) (y:ys)=  x == y && isPrefixOf xs ys;

removeSubstr :: String -> String -> String;
removeSubstr w "" = "";
removeSubstr w s@(c:cs) = (if w `isPrefixOf` s then Prelude.drop (Prelude.length w) s else c : removeSubstr w cs);

simulate_cnt :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Prelude.Int -> Interaction_Trees.Itree e s -> Prelude.IO ();
simulate_cnt n (Interaction_Trees.Ret x) = Prelude.putStrLn ("Terminated: " ++ Prelude.show x);
simulate_cnt n (Interaction_Trees.Sil p) =
  do { if (n == 0) then Prelude.putStrLn "Internal Activity..." else return ();
       if (n >= 2000) then do { Prelude.putStr "Many steps (> 2000); Continue? [Y/N]"; q <- Prelude.getLine;
                              if (q == "Y") then simulate_cnt 0 p else Prelude.putStrLn "Ended early.";
                            }
                    else simulate_cnt (n + 1) p
     };
simulate_cnt n (Interaction_Trees.Vis (Partial_Fun.Pfun_of_alist [])) = Prelude.putStrLn "Deadlocked.";
simulate_cnt n t@(Interaction_Trees.Vis (Partial_Fun.Pfun_of_alist m)) =
  do { Prelude.putStrLn ("Events:" ++ Prelude.concat (map (\(n, e) -> " (" ++ Prelude.show n ++ ") " ++ removeSubstr "_C" e ++ ";") (zip [1..] (map (Prelude.show . fst) m))));
       e <- Prelude.getLine;
       case (Prelude.reads e) of
         []       -> if (Prelude.length m == 1)
                       then simulate_cnt 0 (snd (m !! (0)))
                       else do { Prelude.putStrLn "No parse"; simulate_cnt n t }
         [(v, _)] -> if (v > Prelude.length m)
                       then do { Prelude.putStrLn "Rejected"; simulate_cnt n t }
                       else simulate_cnt 0 (snd (m !! (v - 1)))
     };

simulate :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Interaction_Trees.Itree e s -> Prelude.IO ();
simulate = simulate_cnt 0;
\<close>

generate_file \<open>code/RoboChart_ChemicalDetector/Main.hs\<close> = 
\<open>import qualified Interaction_Trees;
import qualified Partial_Fun;
import qualified Simulate;
import qualified RoboChart_ChemicalDetector_autonomous;

main :: IO ()
main =
  do
    Simulate.simulate (RoboChart_ChemicalDetector_autonomous.d_ChemicalDetector 0);
\<close>

export_generated_files 
  \<open>code/RoboChart_ChemicalDetector/Simulate.hs\<close>
  \<open>code/RoboChart_ChemicalDetector/Main.hs\<close>

end
