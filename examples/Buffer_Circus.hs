{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Buffer_Circus(Chan, Schan, Pfun, Itree, Set, State_ext, Nat, Num, Prism_ext,
                  Lens_ext, deadlock, bitree, buffer, mytest, partest, diverge)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just), Show(..), Read(..), read, getLine, lookup, print, IO, putStr, putStrLn, Int);
import qualified Prelude;
import Text.Read (readMaybe);

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

default_unit :: ();
default_unit = ();

class Default a where {
  defaulta :: a;
};

instance Default () where {
  defaulta = default_unit;
};

data Schan = A_C () | B_C () | C_C () deriving (Prelude.Read, Prelude.Show);

equal_schan :: Schan -> Schan -> Bool;
equal_schan (B_C x2) (C_C x3) = False;
equal_schan (C_C x3) (B_C x2) = False;
equal_schan (A_C x1) (C_C x3) = False;
equal_schan (C_C x3) (A_C x1) = False;
equal_schan (A_C x1) (B_C x2) = False;
equal_schan (B_C x2) (A_C x1) = False;
equal_schan (C_C x3) (C_C y3) = x3 == y3;
equal_schan (B_C x2) (B_C y2) = x2 == y2;
equal_schan (A_C x1) (A_C y1) = x1 == y1;

instance Eq Schan where {
  a == b = equal_schan a b;
};

data Pfun a b = Pfun_of_alist [(a, b)] | Pfun_of_map (a -> Maybe b);

zero_pfun :: forall a b. Pfun a b;
zero_pfun = Pfun_of_alist [];

data Itree a b = Ret b | Sil (Itree a b) | Vis (Pfun a (Itree a b));

plus_pfun :: forall a b. Pfun a b -> Pfun a b -> Pfun a b;
plus_pfun (Pfun_of_alist f) (Pfun_of_alist g) = Pfun_of_alist (g ++ f);

data Set a = Set [a] | Coset [a] deriving (Prelude.Read, Prelude.Show);

uminus_set :: forall a. Set a -> Set a;
uminus_set (Coset xs) = Set xs;
uminus_set (Set xs) = Coset xs;

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

restrict :: forall a b. (Eq a) => Set a -> [(a, b)] -> [(a, b)];
restrict a = filter (\ (k, _) -> member k a);

pdom_res :: forall a b. (Eq a) => Set a -> Pfun a b -> Pfun a b;
pdom_res a (Pfun_of_alist m) = Pfun_of_alist (restrict a m);

pdom :: forall a b. Pfun a b -> Set a;
pdom (Pfun_of_alist xs) = Set (map fst xs);

map_prod :: forall a b. (Eq a) => Pfun a b -> Pfun a b -> Pfun a b;
map_prod f g =
  plus_pfun (pdom_res (uminus_set (pdom g)) f)
    (pdom_res (uminus_set (pdom f)) g);

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

class Extchoice a where {
  extchoice :: a -> a -> a;
};

instance (Eq a, Eq b) => Extchoice (Itree a b) where {
  extchoice = extchoice_itree;
};

data State_ext a = State_ext [Integer] a deriving (Prelude.Read, Prelude.Show);

equal_State_ext :: forall a. (Eq a) => State_ext a -> State_ext a -> Bool;
equal_State_ext (State_ext buf_va morea) (State_ext buf_v more) =
  buf_va == buf_v && morea == more;

instance (Eq a) => Eq (State_ext a) where {
  a == b = equal_State_ext a b;
};

buf_v :: forall a. State_ext a -> [Integer];
buf_v (State_ext buf_v more) = buf_v;

extend :: forall a. State_ext () -> a -> State_ext a;
extend r more = State_ext (buf_v r) more;

make :: [Integer] -> State_ext ();
make buf_v = State_ext buf_v ();

default_State_ext :: forall a. (Default a) => State_ext a;
default_State_ext = extend (make []) defaulta;

instance (Default a) => Default (State_ext a) where {
  defaulta = default_State_ext;
};

data Nat = Zero_nat | Suc Nat deriving (Prelude.Read, Prelude.Show);

data Num = One | Bit0 Num | Bit1 Num deriving (Prelude.Read, Prelude.Show);

data Andor a b = Left a | Right b | Both (a, b)
  deriving (Prelude.Read, Prelude.Show);

data Prism_ext a b c = Prism_ext (b -> Maybe a) (a -> b) c;

data Lens_ext a b c = Lens_ext (b -> a) (b -> a -> b) c;

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

map_of :: forall a b. (Eq a) => [(a, b)] -> a -> Maybe b;
map_of ((l, v) : ps) k = (if l == k then Just v else map_of ps k);
map_of [] k = Nothing;

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (removeAll x xs);
insert x (Set xs) = Set (inserta x xs);

remove :: forall a. (Eq a) => a -> Set a -> Set a;
remove x (Coset xs) = Coset (inserta x xs);
remove x (Set xs) = Set (removeAll x xs);

bind :: forall a b. Maybe a -> (a -> Maybe b) -> Maybe b;
bind Nothing f = Nothing;
bind (Just x) f = f x;

hd :: forall a. [a] -> a;
hd (x21 : x22) = x21;

tl :: forall a. [a] -> [a];
tl [] = [];
tl (x21 : x22) = x22;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

is_empty :: forall a. Set a -> Bool;
is_empty (Set xs) = null xs;

the_elem :: forall a. Set a -> a;
the_elem (Set [x]) = x;

prism_match :: forall a b c. Prism_ext a b c -> b -> Maybe a;
prism_match (Prism_ext prism_match prism_build more) = prism_match;

inp :: forall a b. Prism_ext a b () -> Itree b a;
inp c = Vis (Pfun_of_map (\ e -> bind (prism_match c e) (Just . Ret)));

map_pfun :: forall a b c. (a -> b) -> Pfun c a -> Pfun c b;
map_pfun f (Pfun_of_alist m) = Pfun_of_alist (map (\ (k, v) -> (k, f v)) m);

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);
sup_set (Set xs) a = fold insert xs a;

inf_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
inf_set a (Coset xs) = fold remove xs a;
inf_set a (Set xs) = Set (filter (\ x -> member x a) xs);

pfun_entries :: forall a b. Set a -> (a -> b) -> Pfun a b;
pfun_entries (Set ks) f = Pfun_of_alist (map (\ k -> (k, f k)) ks);

the :: forall a. Maybe a -> a;
the (Just x2) = x2;

pfun_app :: forall a b. (Eq a) => Pfun a b -> a -> b;
pfun_app (Pfun_of_alist xs) k =
  (if membera (map fst xs) k then the (map_of xs k) else error "undefined");

pfuse :: forall a b c. (Eq a) => Pfun a b -> Pfun a c -> Pfun a (b, c);
pfuse f g =
  pfun_entries (inf_set (pdom f) (pdom g))
    (\ x -> (pfun_app f x, pfun_app g x));

emerge ::
  forall a b c. (Eq a) => Pfun a b -> Set a -> Pfun a c -> Pfun a (Andor b c);
emerge f a g =
  plus_pfun
    (plus_pfun (map_pfun Both (pdom_res a (pfuse f g)))
      (map_pfun Left (pdom_res (uminus_set (sup_set a (pdom g))) f)))
    (map_pfun Right (pdom_res (uminus_set (sup_set a (pdom f))) g));

par ::
  forall a b c d.
    (Eq a) => Itree a b -> Set a -> ((b, c) -> d) -> Itree a c -> Itree a d;
par p a f q =
  (case (p, q) of {
    (Ret r, Ret y) -> Ret (f (r, y));
    (Ret _, Sil qa) -> Sil (par p a f qa);
    (Ret r, Vis g) ->
      Vis (map_pfun (par (Ret r) a f) (pdom_res (uminus_set a) g));
    (Sil pa, _) -> Sil (par pa a f q);
    (Vis pfun, Ret v) ->
      Vis (map_pfun (\ pa -> par pa a f (Ret v))
            (pdom_res (uminus_set a) pfun));
    (Vis _, Sil qa) -> Sil (par p a f qa);
    (Vis pfun, Vis g) ->
      Vis (map_pfun (\ b -> (case b of {
                              Left pa -> par pa a f (Vis g);
                              Right ba -> par (Vis pfun) a f ba;
                              Both ba -> (case ba of {
   (pa, bb) -> par pa a f bb;
 });
                            }))
            (emerge pfun a g));
  });

equal_nat :: Nat -> Nat -> Bool;
equal_nat Zero_nat (Suc x2) = False;
equal_nat (Suc x2) Zero_nat = False;
equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2;
equal_nat Zero_nat Zero_nat = True;

one_nat :: Nat;
one_nat = Suc Zero_nat;

deadlock :: forall a b. Itree a b;
deadlock = Vis zero_pfun;

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (Suc n) xs;
gen_length n [] = n;

size_list :: forall a. [a] -> Nat;
size_list = gen_length Zero_nat;

card :: forall a. (Eq a) => Set a -> Nat;
card (Set xs) = size_list (remdups xs);

hide :: forall a b. (Eq a) => Itree a b -> Set a -> Itree a b;
hide p a =
  (case p of {
    Ret aa -> Ret aa;
    Sil pa -> Sil (hide pa a);
    Vis f ->
      (if equal_nat (card (inf_set a (pdom f))) one_nat
        then Sil (hide (pfun_app f (the_elem (inf_set a (pdom f)))) a)
        else (if is_empty (inf_set a (pdom f))
               then Vis (map_pfun (\ x -> hide x a) f) else deadlock));
  });

prism_build :: forall a b c. Prism_ext a b c -> a -> b;
prism_build (Prism_ext prism_match prism_build more) = prism_build;

outp :: forall a b. Prism_ext a b () -> a -> Itree b ();
outp c v = Vis (Pfun_of_alist [(prism_build c v, Ret ())]);

bind_itree :: forall a b c. Itree a b -> (b -> Itree a c) -> Itree a c;
bind_itree (Vis t) k = Vis (map_pfun (\ x -> bind_itree x k) t);
bind_itree (Sil t) k = Sil (bind_itree t k);
bind_itree (Ret v) k = Sil (k v);

while :: forall a b. (a -> Bool) -> (a -> Itree b a) -> a -> Itree b a;
while b p s = (if b s then Sil (bind_itree (p s) (while b p)) else Ret s);

sexp :: forall a b. (a -> b) -> a -> b;
sexp x = x;

inp_in :: forall a b. Prism_ext a b () -> [a] -> Itree b a;
inp_in c b = Vis (Pfun_of_alist (map (\ v -> (prism_build c v, Ret v)) b));

skip :: forall a b. a -> Itree b a;
skip = Ret;

kleisli_comp :: forall a b c d. (a -> b -> c) -> (d -> a) -> b -> d -> c;
kleisli_comp bnd f g = (\ x -> bnd (f x) g);

assigns :: forall a b c. (a -> b) -> a -> Itree c b;
assigns sigma = (\ s -> Ret (sigma s));

proc :: forall a b. (Default a) => (a -> a) -> (a -> Itree b a) -> Itree b ();
proc i a =
  kleisli_comp bind_itree
    (kleisli_comp bind_itree
      (kleisli_comp bind_itree (assigns (\ _ -> defaulta)) (assigns i)) a)
    (assigns (\ _ -> ())) ();

test :: forall a b. (a -> Bool) -> a -> Itree b a;
test b = (\ s -> (if b s then Ret s else deadlock));

input ::
  forall a b c. Prism_ext a b () -> (a -> c -> Itree b c) -> c -> Itree b c;
input c p = (\ s -> bind_itree (inp c) (\ x -> p x s));

un_Output_C :: Chan -> Integer;
un_Output_C (Output_C x2) = x2;

is_Output_C :: Chan -> Bool;
is_Output_C (Input_C x1) = False;
is_Output_C (Output_C x2) = True;
is_Output_C (State_C x3) = False;

ctor_prism ::
  forall a b. (a -> b) -> (b -> Bool) -> (b -> a) -> Prism_ext a b ();
ctor_prism ctor disc sel =
  Prism_ext (\ d -> (if disc d then Just (sel d) else Nothing)) ctor ();

outputa :: Prism_ext Integer Chan ();
outputa = ctor_prism Output_C is_Output_C un_Output_C;

un_Input_C :: Chan -> Integer;
un_Input_C (Input_C x1) = x1;

is_Input_C :: Chan -> Bool;
is_Input_C (Input_C x1) = True;
is_Input_C (Output_C x2) = False;
is_Input_C (State_C x3) = False;

inputa :: Prism_ext Integer Chan ();
inputa = ctor_prism Input_C is_Input_C un_Input_C;

bitree :: () -> Itree Chan ();
bitree =
  while (\ _ -> True)
    (\ _ ->
      bind_itree
        (inp_in inputa
          [(0 :: Integer), (1 :: Integer), (2 :: Integer), (3 :: Integer)])
        (outp outputa));

extchoice_fun :: forall a b. (Extchoice b) => (a -> b) -> (a -> b) -> a -> b;
extchoice_fun p q = (\ s -> extchoice (p s) (q s));

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero_nat = False;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero_nat n = True;

lens_put :: forall a b c. Lens_ext a b c -> b -> a -> b;
lens_put (Lens_ext lens_get lens_put more) = lens_put;

subst_upd :: forall a b c. (a -> b) -> Lens_ext c b () -> (a -> c) -> a -> b;
subst_upd sigma x e = (\ s -> lens_put x (sigma s) (e s));

lens_get :: forall a b c. Lens_ext a b c -> b -> a;
lens_get (Lens_ext lens_get lens_put more) = lens_get;

un_State_C :: Chan -> [Integer];
un_State_C (State_C x3) = x3;

is_State_C :: Chan -> Bool;
is_State_C (Input_C x1) = False;
is_State_C (Output_C x2) = False;
is_State_C (State_C x3) = True;

state :: Prism_ext [Integer] Chan ();
state = ctor_prism State_C is_State_C un_State_C;

subst_id :: forall a. a -> a;
subst_id = (\ s -> s);

buf_v_update ::
  forall a. ([Integer] -> [Integer]) -> State_ext a -> State_ext a;
buf_v_update buf_va (State_ext buf_v more) = State_ext (buf_va buf_v) more;

buf :: forall a. Lens_ext [Integer] (State_ext a) ();
buf = Lens_ext buf_v (\ sigma u -> buf_v_update (\ _ -> u) sigma) ();

input_in ::
  forall a b c.
    Prism_ext a b () -> [a] -> (a -> c -> Itree b c) -> c -> Itree b c;
input_in c a p = (\ s -> bind_itree (inp_in c a) (\ x -> p x s));

output ::
  forall a b c.
    Prism_ext a b () -> (c -> a) -> (c -> Itree b c) -> c -> Itree b c;
output c e p = (\ s -> bind_itree (outp c (e s)) (\ _ -> p s));

buffer :: Itree Chan ();
buffer =
  (proc ::
    (State_ext () -> State_ext ()) ->
      (State_ext () -> Itree Chan (State_ext ())) -> Itree Chan ())
    (subst_upd subst_id buf (sexp (\ _ -> [])))
    (while (\ _ -> True)
      ((extchoice_fun ::
         (State_ext () -> Itree Chan (State_ext ())) ->
           (State_ext () -> Itree Chan (State_ext ())) ->
             State_ext () -> Itree Chan (State_ext ()))
        ((extchoice_fun ::
           (State_ext () -> Itree Chan (State_ext ())) ->
             (State_ext () -> Itree Chan (State_ext ())) ->
               State_ext () -> Itree Chan (State_ext ()))
          (input_in inputa
            [(0 :: Integer), (1 :: Integer), (2 :: Integer), (3 :: Integer)]
            (\ i ->
              assigns
                (subst_upd subst_id buf (sexp (\ s -> lens_get buf s ++ [i])))))
          (kleisli_comp bind_itree
            (kleisli_comp bind_itree
              (test (sexp (\ s ->
                            less_nat Zero_nat (size_list (lens_get buf s)))))
              (output outputa (sexp (\ s -> hd (lens_get buf s)))
                (assigns
                  (subst_upd subst_id buf
                    (sexp (\ s -> tl (lens_get buf s)))))))
            (output state (sexp (lens_get buf)) skip)))
        (output state (sexp (lens_get buf)) skip)));

mytest :: [Integer] -> Itree Chan [Integer];
mytest =
  while (\ _ -> True)
    (extchoice_fun (input inputa (\ i s -> Ret (s ++ [i]))) (\ _ -> deadlock));

bot_set :: forall a. Set a;
bot_set = Set [];

un_c_C :: Schan -> ();
un_c_C (C_C x3) = x3;

is_c_C :: Schan -> Bool;
is_c_C (A_C x1) = False;
is_c_C (B_C x2) = False;
is_c_C (C_C x3) = True;

c :: Prism_ext () Schan ();
c = ctor_prism C_C is_c_C un_c_C;

un_b_C :: Schan -> ();
un_b_C (B_C x2) = x2;

is_b_C :: Schan -> Bool;
is_b_C (A_C x1) = False;
is_b_C (B_C x2) = True;
is_b_C (C_C x3) = False;

b :: Prism_ext () Schan ();
b = ctor_prism B_C is_b_C un_b_C;

un_a_C :: Schan -> ();
un_a_C (A_C x1) = x1;

is_a_C :: Schan -> Bool;
is_a_C (A_C x1) = True;
is_a_C (B_C x2) = False;
is_a_C (C_C x3) = False;

a :: Prism_ext () Schan ();
a = ctor_prism A_C is_a_C un_a_C;

partest :: () -> Itree Schan ();
partest =
  (\ s ->
    hide (par (while (\ _ -> True)
                (\ _ ->
                  bind_itree (outp a ())
                    (\ _ -> bind_itree (outp b ()) (\ _ -> Ret ())))
                s)
           (insert (prism_build b ()) bot_set) (\ _ -> ())
           (while (\ _ -> True)
             (\ _ ->
               bind_itree (outp b ())
                 (\ _ -> bind_itree (outp c ()) (\ _ -> Ret ())))
             s))
      (insert (prism_build b ()) bot_set));

diverge :: forall a b. Itree a b;
diverge = Sil diverge;

simulate_cnt :: (Eq e, Show e, Read e, Show s) => Prelude.Int -> Itree e s -> IO ();
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
