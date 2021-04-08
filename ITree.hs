{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ITree(Nat, Num, Itree) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just), Show(..), Read(..), read, getLine, lookup, print, IO, putStr, putStrLn, Int);
import qualified Prelude;
import Text.Read (readMaybe);

data Nat = Zero_nat | Suc Nat;

data Num = One | Bit0 Num | Bit1 Num;

data Set a = Set [a] | Coset [a];

data Pfun a b = Pfun_of_alist [(a, b)] | Pfun_of_map (a -> Maybe b);

data Itree a b = Ret b | Sil (Itree a b) | Vis (Pfun a (Itree a b));

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

hd :: forall a. [a] -> a;
hd (x21 : x22) = x21;

tl :: forall a. [a] -> [a];
tl [] = [];
tl (x21 : x22) = x22;

restrict :: forall a b. (Eq a) => Set a -> [(a, b)] -> [(a, b)];
restrict a = filter (\ (k, _) -> member k a);

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (Suc n) xs;
gen_length n [] = n;

pdom :: forall a b. Pfun a b -> Set a;
pdom (Pfun_of_alist xs) = Set (map fst xs);

map_pfun :: forall a b c. (a -> b) -> Pfun c a -> Pfun c b;
map_pfun f (Pfun_of_alist m) = Pfun_of_alist (map (\ (k, v) -> (k, f v)) m);

bind_itree :: forall a b c. Itree a b -> (b -> Itree a c) -> Itree a c;
bind_itree (Vis t) k = Vis (map_pfun (\ x -> bind_itree x k) t);
bind_itree (Sil t) k = Sil (bind_itree t k);
bind_itree (Ret v) k = Sil (k v);

zero_pfun :: forall a b. Pfun a b;
zero_pfun = Pfun_of_alist [];

plus_pfun :: forall a b. Pfun a b -> Pfun a b -> Pfun a b;
plus_pfun (Pfun_of_alist f) (Pfun_of_alist g) = Pfun_of_alist (g ++ f);

uminus_set :: forall a. Set a -> Set a;
uminus_set (Coset xs) = Set xs;
uminus_set (Set xs) = Coset xs;

pdom_res :: forall a b. (Eq a) => Set a -> Pfun a b -> Pfun a b;
pdom_res a (Pfun_of_alist m) = Pfun_of_alist (restrict a m);

simulate_cnt :: (Eq e, Show e, Read e, Show s) => Int -> Itree e s -> IO ();
simulate_cnt n (Ret x) = putStrLn ("Terminated: " ++ show x);
simulate_cnt n (Sil p) = 
  do { putStrLn "Internal Activity";
       if (n >= 10) then do { putStr "Continue? [Y/N]"; q <- getLine; 
                              if (q == "Y") then simulate_cnt 0 p else putStrLn "Ended early.";
                            }
                    else simulate_cnt (n + 1) p
     };
simulate_cnt n (Vis (Pfun_of_alist [])) = putStrLn "Deadlocked.";
simulate_cnt n t@(Vis (Pfun_of_alist m)) = 
  do { putStrLn ("Events: " ++ show (map fst m));
       e <- getLine;
       case (readMaybe e) of
         Nothing -> do { putStrLn "No parse"; simulate_cnt n t }
         Just v -> case (lookup v m) of
                     Nothing -> do { putStrLn "Rejected"; simulate_cnt n t }
                     Just k -> simulate_cnt 0 k
     };

simulate :: (Eq e, Show e, Read e, Show s) => Itree e s -> IO ();
simulate = simulate_cnt 0;

}
