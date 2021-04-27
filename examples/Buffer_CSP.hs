{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Buffer_CSP(Chan, Nat, Num, Set, Prism_ext, Itree, echo, buffer) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Chan = Input_C Integer | Output_C Integer | State_C [Integer]
  deriving (Prelude.Read, Prelude.Show);

equal_Chan :: Chan -> Chan -> Bool;
equal_Chan (Output_C x2) (State_C x3) = False;
equal_Chan (State_C x3) (Output_C x2) = False;
equal_Chan (Input_C x1) (State_C x3) = False;
equal_Chan (State_C x3) (Input_C x1) = False;
equal_Chan (Input_C x1) (Output_C x2) = False;
equal_Chan (Output_C x2) (Input_C x1) = False;
equal_Chan (State_C x3) (State_C y3) = x3 == y3;
equal_Chan (Output_C x2) (Output_C y2) = x2 == y2;
equal_Chan (Input_C x1) (Input_C y1) = x1 == y1;

instance Eq Chan where {
  a == b = equal_Chan a b;
};

data Nat = Zero_nat | Suc Nat deriving (Prelude.Read, Prelude.Show);

data Num = One | Bit0 Num | Bit1 Num deriving (Prelude.Read, Prelude.Show);

data Set a = Set [a] | Coset [a] deriving (Prelude.Read, Prelude.Show);

data Pfun a b = Pfun_of_alist [(a, b)] | Pfun_of_map (a -> Maybe b);

data Prism_ext a b c = Prism_ext (b -> Maybe a) (a -> b) c;

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

prism_build :: forall a b c. Prism_ext a b c -> a -> b;
prism_build (Prism_ext prism_match prism_build more) = prism_build;

outp :: forall a b. Prism_ext a b () -> a -> Itree b ();
outp c v = Vis (Pfun_of_alist [(prism_build c v, Ret ())]);

is_none :: forall a. Maybe a -> Bool;
is_none (Just x) = False;
is_none Nothing = True;

zero_pfun :: forall a b. Pfun a b;
zero_pfun = Pfun_of_alist [];

deadlock :: forall a b. Itree a b;
deadlock = Vis zero_pfun;

guard :: forall a. Bool -> Itree a ();
guard b = (if b then Ret () else deadlock);

map_pfun :: forall a b c. (a -> b) -> Pfun c a -> Pfun c b;
map_pfun f (Pfun_of_alist m) = Pfun_of_alist (map (\ (k, v) -> (k, f v)) m);

bind_itree :: forall a b c. Itree a b -> (b -> Itree a c) -> Itree a c;
bind_itree (Vis t) k = Vis (map_pfun (\ x -> bind_itree x k) t);
bind_itree (Sil t) k = Sil (bind_itree t k);
bind_itree (Ret v) k = k v;

while :: forall a b. (a -> Bool) -> (a -> Itree b a) -> a -> Itree b a;
while b p s = (if b s then Sil (bind_itree (p s) (while b p)) else Ret s);

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (Suc n) xs;
gen_length n [] = n;

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

prism_match :: forall a b c. Prism_ext a b c -> b -> Maybe a;
prism_match (Prism_ext prism_match prism_build more) = prism_match;

the :: forall a. Maybe a -> a;
the (Just x2) = x2;

inp_list :: forall a b. Prism_ext a b () -> [a] -> Itree b a;
inp_list c b =
  Vis (Pfun_of_alist
        (map_filter
          (\ x ->
            (if not (is_none (prism_match c (prism_build c x)))
              then Just (prism_build c x,
                          Ret (the (prism_match c (prism_build c x))))
              else Nothing))
          b));

inp_in :: forall a b. Prism_ext a b () -> Set a -> Itree b a;
inp_in c (Set b) = inp_list c b;

pdom :: forall a b. Pfun a b -> Set a;
pdom (Pfun_of_alist xs) = Set (map fst xs);

plus_pfun :: forall a b. Pfun a b -> Pfun a b -> Pfun a b;
plus_pfun (Pfun_of_alist f) (Pfun_of_alist g) = Pfun_of_alist (g ++ f);

uminus_set :: forall a. Set a -> Set a;
uminus_set (Coset xs) = Set xs;
uminus_set (Set xs) = Coset xs;

pdom_res :: forall a b. (Eq a) => Set a -> Pfun a b -> Pfun a b;
pdom_res a (Pfun_of_alist m) = Pfun_of_alist (restrict a m);

map_prod :: forall a b. (Eq a) => Pfun a b -> Pfun a b -> Pfun a b;
map_prod f g =
  plus_pfun (pdom_res (uminus_set (pdom g)) f)
    (pdom_res (uminus_set (pdom f)) g);

ctor_prism ::
  forall a b. (a -> b) -> (b -> Bool) -> (b -> a) -> Prism_ext a b ();
ctor_prism ctor disc sel =
  Prism_ext (\ d -> (if disc d then Just (sel d) else Nothing)) ctor ();

un_Output_C :: Chan -> Integer;
un_Output_C (Output_C x2) = x2;

is_Output_C :: Chan -> Bool;
is_Output_C (Input_C x1) = False;
is_Output_C (Output_C x2) = True;
is_Output_C (State_C x3) = False;

output :: Prism_ext Integer Chan ();
output = ctor_prism Output_C is_Output_C un_Output_C;

un_Input_C :: Chan -> Integer;
un_Input_C (Input_C x1) = x1;

is_Input_C :: Chan -> Bool;
is_Input_C (Input_C x1) = True;
is_Input_C (Output_C x2) = False;
is_Input_C (State_C x3) = False;

input :: Prism_ext Integer Chan ();
input = ctor_prism Input_C is_Input_C un_Input_C;

top_set :: forall a. Set a;
top_set = Coset [];

echo :: () -> Itree Chan ();
echo =
  while (\ _ -> True) (\ _ -> bind_itree (inp_in input top_set) (outp output));

extchoice_itree ::
  forall a b. (Eq a, Eq b) => Itree a b -> Itree a b -> Itree a b;
extchoice_itree p q =
  (case (p, q) of {
    (Ret r, Ret y) -> (if r == y then Ret r else Vis zero_pfun);
    (Ret _, Sil qa) -> Sil (extchoice_itree p qa);
    (Ret r, Vis _) -> Ret r;
    (Sil pa, _) -> Sil (extchoice_itree pa q);
    (Vis _, Ret a) -> Ret a;
    (Vis _, Sil qa) -> Sil (extchoice_itree p qa);
    (Vis f, Vis g) -> Vis (map_prod f g);
  });

size_list :: forall a. [a] -> Nat;
size_list = gen_length Zero_nat;

un_State_C :: Chan -> [Integer];
un_State_C (State_C x3) = x3;

is_State_C :: Chan -> Bool;
is_State_C (Input_C x1) = False;
is_State_C (Output_C x2) = False;
is_State_C (State_C x3) = True;

state :: Prism_ext [Integer] Chan ();
state = ctor_prism State_C is_State_C un_State_C;

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero_nat = False;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero_nat n = True;

buffer :: [Integer] -> Itree Chan [Integer];
buffer =
  while (\ _ -> True)
    (\ s ->
      extchoice_itree
        (extchoice_itree
          (bind_itree
            (inp_list input
              [(0 :: Integer), (1 :: Integer), (2 :: Integer), (3 :: Integer)])
            (\ i -> Ret (s ++ [i])))
          (bind_itree (guard (less_nat Zero_nat (size_list s)))
            (\ _ -> bind_itree (outp output (hd s)) (\ _ -> Ret (tl s)))))
        (bind_itree (outp state s) (\ _ -> Ret s)));

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
  do { Prelude.putStrLn ("Events: " ++ Prelude.show (map fst m));
       e <- Prelude.getLine;
       case (Prelude.reads e) of
         []       -> do { Prelude.putStrLn "No parse"; simulate_cnt n t }
         [(v, _)] -> case (Prelude.lookup v m) of
                       Nothing -> do { Prelude.putStrLn "Rejected"; simulate_cnt n t }
                       Just k -> simulate_cnt 0 k
     };

simulate :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Itree e s -> Prelude.IO ();
simulate = simulate_cnt 0;

}
