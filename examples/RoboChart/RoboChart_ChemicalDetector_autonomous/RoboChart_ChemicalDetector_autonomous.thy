section \<open> Simulation of a very basic RoboChart model \<close>
text \<open> This theory aims for simulation of a trivial RoboChart model based on its CSP
 semantics. We use the @{term "rename"} operator for renaming.
\<close>
theory RoboChart_ChemicalDetector_autonomous
  imports "RoboChart_ChemicalDetector_autonomous_general"
    "RoboChart_ChemicalDetector_autonomous_maincontroller"
    "RoboChart_ChemicalDetector_autonomous_microcontroller"
begin

subsection \<open> Module \<close>
chantype Chan_mod0 =
(* terminates of MainCtrl are mapped to it *)
  terminate_mod0 :: unit 
(* variable channels: set_x and get_x of Movement and stm1 are mapped to these channels *)
  set_x_mod0 :: core_int
  get_x_mod0 :: core_int
(* shared variable channels *)
  set_EXT_x_mod0_MainCtrl :: core_int
(* e1 of Movement is mapped to it *)
  e1_mod0 :: "InOut \<times> core_int"
(* e2 of stm1 is mapped to it *)
  e2_mod0 :: "InOut"

definition Memory_mod0 where
"Memory_mod0 = loop (\<lambda> id::integer.
  ( do {x \<leftarrow> inp_in set_x_mod0 rc.core_int_set; 
        outp set_EXT_x_mod0_MainCtrl x; Ret (id)}
  )
)"

(*
definition rename_mod0_MainCtrl_events where
"rename_mod0_MainCtrl_events = 
  [(terminate_MainCtrl_C (), terminate_mod0_C ())] @
  [(set_x_MainCtrl_C n, set_x_mod0_C n). n \<leftarrow> rc.core_int_list] @
  [(get_x_MainCtrl_C n, get_x_mod0_C n). n \<leftarrow> rc.core_int_list] @
  [(e1_MainCtrl_C (d, n), e1_mod0_C (d, n)). d \<leftarrow> InOut_list, n \<leftarrow> rc.core_int_list] @
  [(e2_MainCtrl_C (d), e2_mod0_C (d)). d \<leftarrow> InOut_list] @
  [(set_EXT_x_MainCtrl_C n, set_EXT_x_mod0_MainCtrl_C n). n \<leftarrow> rc.core_int_list]
"
*)
definition rename_mod0_MainCtrl_events where
"rename_mod0_MainCtrl_events = 
  (enumchanp2_1 (terminate_MainCtrl_C,terminate_mod0_C) [()]) @
  (enumchansp2_1 [(set_x_MainCtrl_C, set_x_mod0_C), (get_x_MainCtrl_C, get_x_mod0_C), 
      (set_EXT_x_MainCtrl_C, set_EXT_x_mod0_MainCtrl_C)] rc.core_int_list) @
  (enumchanp2_1 (e2_MainCtrl_C, e2_mod0_C) InOut_list) @
  (enumchanp2_2 (e1_MainCtrl_C, e1_mod0_C) InOut_list rc.core_int_list)
"

definition rename_D__MainCtrl where
"rename_D__MainCtrl idd = rename (set rename_mod0_MainCtrl_events) (D__MainCtrl idd)"

definition "mod0_set_x_events = set (
  enumchan1 set_x_mod0_C  rc.core_int_list
)"

definition "mod0_get_x_events = set (
  enumchan1 get_x_mod0_C  rc.core_int_list
)"

definition "mod0_set_EXT_x_events = set (
  enumchan1 set_EXT_x_mod0_MainCtrl_C  rc.core_int_list
)"

definition D__ctr_mem where
"D__ctr_mem (idd::integer) = (
              (rename_D__MainCtrl idd) 
              \<parallel>\<^bsub> (mod0_set_x_events \<union> mod0_set_EXT_x_events) \<^esub> 
              (discard_state (Memory_mod0 idd))
            )"

definition D__mod0 where
"D__mod0 (idd::integer) = 
  (hide
    (
      (skip \<parallel>\<^bsub> {} \<^esub> 
        (
          hide 
            (
              (rename_D__MainCtrl idd) 
              \<parallel>\<^bsub> (mod0_set_x_events \<union> mod0_set_EXT_x_events) \<^esub> 
              (discard_state (Memory_mod0 idd))
            )
            ((mod0_set_x_events \<union> mod0_get_x_events) \<union> mod0_set_EXT_x_events)
        )
      )  \<lbrakk> set [terminate_mod0_C ()] \<Zrres> skip
    )
    (set [terminate_mod0_C ()])
  )
"

subsection \<open> Export code \<close>
export_code
  Movement_Memory_opt_x
  Movement_Memory_opt_l
  Movement_MemoryTransitions_opt_0
  Movement_MemoryTransitions_opt_1
  I_Movement_i0
  State_Movement_s0
  State_Movement_s0_R
  STM_Movement
  MemorySTM_opt_Movement 
  rename_MemorySTM_opt_Movement
  D__Movement 
  stm1_Memory_opt_x
  stm1_MemoryTransitions_opt_0
  I_stm1_i0
  State_stm1_s0
  State_stm1_s0_R
  STM_stm1
  MemorySTM_opt_stm1
  D__stm1
  rename_D__Movement
  rename_D__stm1
  D__MainCtrl
  rename_D__MainCtrl
  D__ctr_mem
  D__mod0
  in Haskell 
  (* module_name RoboChart_basic *)
  file_prefix RoboChart_basic 
  (string_classes) 

generate_file \<open>code/RoboChart_basic/Simulate.hs\<close> = 
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

export_generated_files \<open>code/RoboChart_basic/Simulate.hs\<close>

end
