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
  terminate :: unit 
  flag :: "InOut"
  gas :: "InOut \<times> 2 Chemical_GasSensor[2]blist"
  obstacle :: "InOut \<times> Location_Loc"
  odometer :: "InOut \<times> core_real"
  resume :: "InOut"
  turn :: "InOut \<times> Chemical_Angle"
  stop :: "InOut"
  randomeWalkCall :: unit
  moveCall :: "core_real \<times> Chemical_Angle"
  shortRandomWalkCall :: unit
  (* timeout *)
  stuck_timeout :: "InOut"

definition Memory_ChemicalDetector where
"Memory_ChemicalDetector = skip"

definition rename_ChemicalDetector_D__MainController_events where
"rename_ChemicalDetector_D__MainController_events = 
  (enumchanp2_1 (terminate_MainController_C, terminate_C) [()]) @
  (enumchansp2_2 [(gas_MainController_C, gas_C)] InOut_list lseq_gassensor_enum) @
  (enumchansp2_2 [(turn_MainController_C, turn_C)] InOut_list Chemical_Angle_list) @
  (enumchansp2_1 [(stop_MainController_C, stop_C), 
      (resume_MainController_C, resume_C)] InOut_list) 
"

definition rename_D__MainController where
"rename_D__MainController idd = (
  (D__MainController idd) \<lbrakk>(set rename_ChemicalDetector_D__MainController_events)\<rbrakk>) "

definition rename_ChemicalDetector_D__MicroController_events where
"rename_ChemicalDetector_D__MicroController_events = 
  (enumchanp2_1 (terminate_MicroController_C, terminate_C) [()]) @
  (enumchansp2_2 [(obstacle_MicroController_C, obstacle_C)]  
      InOut_list Location_Loc_list) @
  (enumchansp2_2 [(odometer_MicroController_C, odometer_C)]  
      InOut_list rc.core_real_list) @
  (enumchansp2_2 [(turn_MicroController_C, turn_C)] 
      InOut_list Chemical_Angle_list) @
  (enumchansp2_1 [(flag_MicroController_C, flag_C)] InOut_list) @
  (enumchansp2_1 [(randomeWalkCall_MicroController_C, randomeWalkCall_C),
      (shortRandomWalkCall_MicroController_C, shortRandomWalkCall_C)] [()]) @
  (enumchansp2_2 [(moveCall_MicroController_C, moveCall_C)]
      rc.core_real_list Chemical_Angle_list) @
  \<comment> \<open> stop.in of MicroController -> stop.out of ManController through stop_C\<close>
  [(stop_MicroController_C din, stop_C dout),
    (stop_MicroController_C dout, stop_C din),
    (resume_MicroController_C din, resume_C dout),
    (resume_MicroController_C dout, resume_C din)
  ]
  \<comment> \<open> timeout \<close>
  @ (enumchansp2_1 [(stuck_timeout_MicroController_C, stuck_timeout_C)] InOut_list)
"

definition rename_D__MicroController where
"rename_D__MicroController idd = (
  (D__MicroController idd) \<lbrakk>(set rename_ChemicalDetector_D__MicroController_events)\<rbrakk>)"

text \<open> The connection from MainController to MicroController on the event turn is asynchronous, 
and so its CSP semantics has a buffer in between. The buffer is defined below.
\<close>
definition buffer0 :: "Chemical_Angle list \<Rightarrow> (Chan_ChemicalDetector, Chemical_Angle list) itree"  where
"buffer0 = loop (\<lambda>la. 
  do {guard(length la = 0); 
      v \<leftarrow> inp_in turn (set [(dout, a). a \<leftarrow> Chemical_Angle_list]); 
      Ret [snd v]} \<box>
  do {guard(length la > 0); 
      x \<leftarrow> inp_in turn (set [(dout, a). a \<leftarrow> Chemical_Angle_list]); 
      Ret [snd x]}  \<box>
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
import qualified Bounded_List;
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
  do { Prelude.putStrLn ("Events:" ++ Prelude.concat (map (\(n, e) -> " (" ++ Prelude.show n ++ ") " ++ renameGasEvent e ++ ";") (zip [1..] (map (Prelude.show . fst) m))));
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

(*
instance (Prelude.Show a, Prelude.Show b) => Prelude.Show (Bounded_List.Blist a b) where {
  show (Bounded_List.Bmake a b) = Prelude.show b;
};
*)

export_generated_files 
  \<open>code/RoboChart_ChemicalDetector/Simulate.hs\<close>
  \<open>code/RoboChart_ChemicalDetector/Main.hs\<close>

end
