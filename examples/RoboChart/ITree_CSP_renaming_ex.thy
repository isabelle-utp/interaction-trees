section \<open>  \<close>
text \<open> 
\<close>

theory ITree_CSP_renaming_ex
  imports "../../ITree_RoboChart"
begin

subsection \<open> General definitions \<close>
definition "int_max = (1::integer)"
definition "int_min = (-1::integer)"

abbreviation "core_int_list \<equiv> 
  int2integer_list [(int_of_integer int_min)..(int_of_integer int_max)]"

abbreviation "core_int_set \<equiv> set core_int_list"

subsubsection \<open> stm0 \<close>
datatype SIDS_stm0 = SID_stm0
  | SID_stm0_s0

definition "SIDS_stm0_list = [SID_stm0, SID_stm0_s0]"
definition "SIDS_stm0_set = set SIDS_stm0_list"
definition "SIDS_stm0_without_s0 = (removeAll SID_stm0_s0 SIDS_stm0_list)"

datatype TIDS_stm0 = NULLTRANSITION_stm0
	              | TID_stm0_t0
	              | TID_stm0_t1
	              | TID_stm0_t2

definition "TIDS_stm0_list = [NULLTRANSITION_stm0, TID_stm0_t0, TID_stm0_t1, TID_stm0_t2]"
definition "TIDS_stm0_set = set TIDS_stm0_list"

definition "ITIDS_stm0_list = [TID_stm0_t1, TID_stm0_t2]"
definition "ITIDS_stm0 = set ITIDS_stm0_list"  

subsubsection \<open> stm1 \<close>

datatype SIDS_stm1 = SID_stm1
  | SID_stm1_s0

definition "SIDS_stm1_list = [SID_stm1, SID_stm1_s0]"
definition "SIDS_stm1_set = set SIDS_stm1_list"
definition "SIDS_stm1_without_s0 = (removeAll SID_stm1_s0 SIDS_stm1_list)"

datatype TIDS_stm1 = NULLTRANSITION_stm1
	              | TID_stm1_t0
	              | TID_stm1_t1
	              | TID_stm1_t2

definition "TIDS_stm1_list = [NULLTRANSITION_stm1, TID_stm1_t0, TID_stm1_t1, TID_stm1_t2]"
definition "TIDS_stm1_set = set TIDS_stm1_list"

definition "ITIDS_stm1_list = [TID_stm1_t1, TID_stm1_t2]"
definition "ITIDS_stm1 = set ITIDS_stm1_list"

subsection \<open> Channel type\<close>
chantype Chan =
  e1__stm0 :: "TIDS_stm0 \<times> InOut \<times> core_int"
(*
  e1_ctr0 :: "InOut \<times> core_int"
  e1_mod0 :: "InOut \<times> core_int"
*)

chantype Chan1 =
  e1_stm0 :: "TIDS_stm0 \<times> InOut \<times> core_int"

subsection \<open> Process \<close>
definition P0 where
"P0 = loop (\<lambda> x::integer. 
    (
     do {(tid, d, x) \<leftarrow> inp_in e1__stm0 (set [(TID_stm0_t2, din, x). x \<leftarrow> core_int_list]); Ret (x)} \<box> 
     do {(tid, d, x) \<leftarrow> inp_in e1__stm0 (set [(TID_stm0_t1, din, x). x \<leftarrow> core_int_list]); Ret (x)}
    )
  )"

definition P1 where
"P1 = loop (\<lambda> id::integer. 
    (
     do {(tid, d, x) \<leftarrow> inp_in e1__stm0 (set [(TID_stm0_t2, din, x). x \<leftarrow> core_int_list, x > 0]); Ret (x)} \<box> 
     do {(tid, d, x) \<leftarrow> inp_in e1__stm0 (set [(TID_stm0_t1, din, x). x \<leftarrow> core_int_list, x \<le> 0]); Ret (x)}
    )
  )"

definition channel_set where
"channel_set = 
  set ([e1__stm0_C (tid, dir, n). 
          tid \<leftarrow> [TID_stm0_t1, TID_stm0_t2], 
          dir \<leftarrow> [din, dout], 
          n \<leftarrow> core_int_list]
)"

definition P where
"P = (discard_state (P0 0)) \<parallel>\<^bsub> channel_set \<^esub> (discard_state (P1 0))"

definition rename_map where
"rename_map = 
  [(e1__stm0_C (tid, dir, n), e1_stm0_C (tid, dir, n)) . 
          tid \<leftarrow> TIDS_stm0_list, 
          dir \<leftarrow> InOut_list, 
          n \<leftarrow> core_int_list] @
  []
"

definition Pr where
"Pr = rename (pinj_of_alist rename_map) (P)"

value "pfun_of_pinj (pinv (pinj_of_alist rename_map))"
value "pfun_of_pinj
  (pinj_of_alist
    [(e1_stm0_C (NULLTRANSITION_stm0, din, - 1), e1__stm0_C (NULLTRANSITION_stm0, din, - 1)),
     (e1_stm0_C (NULLTRANSITION_stm0, din, 0), e1__stm0_C (NULLTRANSITION_stm0, din, 0))])"

print_codeproc
code_thms pfun_of_pinj
code_deps pfun_of_pinj

subsection \<open> Export code \<close>
export_code
  P
  Pr
  in Haskell
  file_prefix renaming_ex 
  (string_classes) 

generate_file \<open>code/renaming_ex/Simulate.hs\<close> = 
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
       if (n >= 20) then do { Prelude.putStr "Many steps (> 20); Continue? [Y/N]"; q <- Prelude.getLine;
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

export_generated_files \<open>code/renaming_ex/Simulate.hs\<close>

end