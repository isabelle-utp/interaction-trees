section \<open> Renaming Experiments \<close>

text \<open> This theory aims for experiments of various renaming solutions. \<close>

theory CSP_renaming_experiment
  imports "../../ITree_RoboChart"
begin

declare [[show_types]]

(* Only choose one for each a\<^sub>2
(1) a\<^sub>1 \<in> dom(g).
  (1.1) a\<^sub>1 \<in> dom(f).
    (1.1.1) f(a\<^sub>1) \<in> dom(g). (f(a\<^sub>1), g(a\<^sub>1)) or (f(a\<^sub>1), g(f(a\<^sub>1)))
    (1.1.2) f(a\<^sub>1) \<notin> dom(g). (f(a\<^sub>1), g(a\<^sub>1))
  (1.2) a\<^sub>1 \<notin> dom(f). (a\<^sub>1, g(a\<^sub>1))
(2) a\<^sub>1 \<notin> dom(g)
  (2.1) a\<^sub>1 \<in> ran(f). 
    (2.1.1) \<exists> x. f(x) = a\<^sub>1 \<and> x \<in> dom(g). (a\<^sub>1, g(SOME x. f(x) = a\<^sub>1 \<and> x \<in> dom(g)))
    (2.1.2) \<not>\<exists> x. f(x) = a\<^sub>1 \<and> x \<in> dom(g). (a\<^sub>1, undefined) 
  (2.2) a\<^sub>1 \<notin> dom(f). (a\<^sub>1, undefined)
*)

(* a\<^sub>2 may lead to a nondeterministic choice of ...
(1) a\<^sub>1 \<in> dom(g).
  (1.1) a\<^sub>1 \<in> dom(f).
    (1.1.1) f(a\<^sub>1) \<in> dom(g). (f(a\<^sub>1), g(a\<^sub>1) |~| g(f(a\<^sub>1)))
        such as [(a1, a2)] [(a1, c1), (a2, c2)] = [(a2, c1 |~| c2)]
    (1.1.2) f(a\<^sub>1) \<notin> dom(g). (f(a\<^sub>1), g(a\<^sub>1)) 
        such as [(a1, a2)] [(a1, c1), (a3, c3)] = [(a2, c1), (a3, c3)]
  (1.2) a\<^sub>1 \<notin> dom(f). (a\<^sub>1, g(a\<^sub>1) |~| ran ((dom (f \<rhd>\<^sub>p {a\<^sub>1})) \<lhd>\<^sub>p g))
        such as [(a1, a3), (a2, a3)] [(a1, c1), (a3, c3)] = [(a3, c3 |~| c1)]
(2) a\<^sub>1 \<notin> dom(g). (a\<^sub>1, if ran ((dom (f \<rhd>\<^sub>p {a\<^sub>1})) \<lhd>\<^sub>p g) = {} then undefined else Some ran ((dom (f \<rhd>\<^sub>p {a\<^sub>1})) \<lhd>\<^sub>p g))
*)

definition range_restrict :: "('key \<times> 'val) list \<Rightarrow> 'val set \<Rightarrow>  ('key \<times> 'val) list"
  where range_restrict_eq: "range_restrict m A = filter (\<lambda>(_, v). v \<in> A) m"

lemma range_restrict_simps [simp]:
  "range_restrict [] A = []"
  "range_restrict (p#ps) A = (if snd p \<in> A then p # range_restrict ps A else range_restrict ps A)"
  by (auto simp add: range_restrict_eq)

lemma "map_of [(a\<^sub>1, a\<^sub>2), (a\<^sub>1, a\<^sub>1)] = map_of [(a\<^sub>1, a\<^sub>2)]"
  by simp

definition intchoice_set :: "('e, 'a) itree set \<Rightarrow> ('e, 'a) itree" where
"intchoice_set s = (if s = {} then deadlock else (SOME x. x \<in> s))"

(* Partial renaming and other events not in the renaming map are not changed. *)
(*
a\<^sub>2 may from (a\<^sub>2, F(a\<^sub>2)), or from (a\<^sub>1, a\<^sub>2) in \<rho> and then (\<rho>(a\<^sub>1), F(a\<^sub>1))
*)

definition Vis_rename1 :: "('e\<^sub>1 \<Zpfun> 'e\<^sub>1) \<Rightarrow> ('e\<^sub>1 \<Zpfun> ('e\<^sub>1, 'a) itree) \<Rightarrow> ('e\<^sub>1 \<Zpfun> ('e\<^sub>1, 'a) itree)"  where 
"Vis_rename1 \<rho> F = pfun_of_map
(\<lambda>a\<^sub>2::'e\<^sub>1. 
    if (F a\<^sub>2) = undefined 
    then (
          if pran ((pdom (\<rho> \<rhd>\<^sub>p {a\<^sub>2})) \<lhd>\<^sub>p F) = {}
          then undefined 
          else Some (intchoice_set (pran ((pdom (\<rho> \<rhd>\<^sub>p {a\<^sub>2})) \<lhd>\<^sub>p F))))
    else (
          if pran ((pdom (\<rho> \<rhd>\<^sub>p {a\<^sub>2})) \<lhd>\<^sub>p F) = {} 
          then Some (F a\<^sub>2)
          else Some (intchoice_set ({(F a\<^sub>2)} \<union> pran ((pdom (\<rho> \<rhd>\<^sub>p {a\<^sub>2})) \<lhd>\<^sub>p F))))
)"

primcorec rename1 :: "('e\<^sub>1 \<Zpfun> 'e\<^sub>1) \<Rightarrow> ('e\<^sub>1, 'a) itree \<Rightarrow> ('e\<^sub>1, 'a) itree" where
"rename1 \<rho> P = 
  (case P of
    Ret x \<Rightarrow> Ret x |
    Sil P \<Rightarrow> Sil (rename1 \<rho> P) |
    Vis F \<Rightarrow> Vis (map_pfun (rename1 \<rho>) (Vis_rename1 \<rho> F)))"

(* Total renaming and all events will be renamed. *)
(*
  a\<^sub>2 are only from (a\<^sub>1, a\<^sub>2) in \<rho> and then (\<rho>(a\<^sub>1), F(a\<^sub>1))
*)


definition Vis_rename2 :: "('e\<^sub>1 \<Zpfun> 'e\<^sub>2) \<Rightarrow> ('e\<^sub>1 \<Zpfun> ('e\<^sub>1, 'a) itree) \<Rightarrow> ('e\<^sub>2 \<Zpfun> ('e\<^sub>1, 'a) itree)"  where 
"Vis_rename2 \<rho> F = F \<circ>\<^sub>p pfun_of_pinj (pinv (pinj_of_pfun ((pdom F) \<lhd>\<^sub>p \<rho>)))"

primcorec rename2 :: "('e\<^sub>1 \<Zpfun> 'e\<^sub>2) \<Rightarrow> ('e\<^sub>1, 'a) itree \<Rightarrow> ('e\<^sub>2, 'a) itree" where
"rename2 \<rho> P = 
  (case P of
    Ret x \<Rightarrow> Ret x |
    Sil P \<Rightarrow> Sil (rename2 \<rho> P) |
    Vis F \<Rightarrow> Vis (map_pfun (rename2 \<rho>) (Vis_rename2 \<rho> F)))"

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
  e1'_stm0 :: "InOut \<times> core_int"

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
  [(e1__stm0_C (tid, dir, n), e1'_stm0_C (dir, n)) . 
          tid \<leftarrow> TIDS_stm0_list, 
          dir \<leftarrow> InOut_list, 
          n \<leftarrow> core_int_list] @
  []
"

chantype testch =
  cin :: "InOut \<times> core_int"
  cout :: "core_int"

value "graph_pfun (set [(cout_C 1, cin_C (din, 1)), (cout_C 1, cin_C (dout, 1))])"

value "graph_pfun (set [(1::integer, 2::integer), (1, 3)])"
value "graph_pfun (set [(1::integer, 2::integer)])"

value "graph_pfun ((set [cin_C (din, 1), cin_C (dout, 1)] \<lhd>\<^sub>r (set 
  [(cin_C (din, 1), cout_C 1), (cin_C (dout, 1), cout_C 1)]))\<inverse>)"

definition Pr where
"Pr = rename (set rename_map) (P)"

definition rename_map1 where
"rename_map1 = 
  [(e1__stm0_C (tid, dir, n), e1__stm0_C (tid, dir, n)) . 
          tid \<leftarrow> TIDS_stm0_list, 
          dir \<leftarrow> InOut_list, 
          n \<leftarrow> core_int_list] @
  []
"

term "map"
definition Prr where
"Prr = rename1 (pfun_of_alist (map (\<lambda> (x,y). (y,x)) rename_map1)) (P)"

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