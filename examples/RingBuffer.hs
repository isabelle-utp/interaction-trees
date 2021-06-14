{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  RingBuffer(Nat, Chan, Itree, Set, ControllerState_ext, Int, Num, ring,
              controller, cRing)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

newtype Nat = Nat Integer deriving (Prelude.Read, Prelude.Show);

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

instance Eq Nat where {
  a == b = equal_nat a b;
};

data Chan = Rd_C (Nat, Integer) | Wrt_C (Nat, Integer) | Input_C Integer
  | Output_C Integer deriving (Prelude.Read, Prelude.Show);

equal_chan :: Chan -> Chan -> Bool;
equal_chan (Input_C x3) (Output_C x4) = False;
equal_chan (Output_C x4) (Input_C x3) = False;
equal_chan (Wrt_C x2) (Output_C x4) = False;
equal_chan (Output_C x4) (Wrt_C x2) = False;
equal_chan (Wrt_C x2) (Input_C x3) = False;
equal_chan (Input_C x3) (Wrt_C x2) = False;
equal_chan (Rd_C x1) (Output_C x4) = False;
equal_chan (Output_C x4) (Rd_C x1) = False;
equal_chan (Rd_C x1) (Input_C x3) = False;
equal_chan (Input_C x3) (Rd_C x1) = False;
equal_chan (Rd_C x1) (Wrt_C x2) = False;
equal_chan (Wrt_C x2) (Rd_C x1) = False;
equal_chan (Output_C x4) (Output_C y4) = x4 == y4;
equal_chan (Input_C x3) (Input_C y3) = x3 == y3;
equal_chan (Wrt_C x2) (Wrt_C y2) = x2 == y2;
equal_chan (Rd_C x1) (Rd_C y1) = x1 == y1;

instance Eq Chan where {
  a == b = equal_chan a b;
};

default_unit :: ();
default_unit = ();

class Default a where {
  defaulta :: a;
};

instance Default () where {
  defaulta = default_unit;
};

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
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

data CellState_ext a = CellState_ext Integer a
  deriving (Prelude.Read, Prelude.Show);

equal_CellState_ext ::
  forall a. (Eq a) => CellState_ext a -> CellState_ext a -> Bool;
equal_CellState_ext (CellState_ext val_va morea) (CellState_ext val_v more) =
  val_va == val_v && morea == more;

instance (Eq a) => Eq (CellState_ext a) where {
  a == b = equal_CellState_ext a b;
};

val_v :: forall a. CellState_ext a -> Integer;
val_v (CellState_ext val_v more) = val_v;

extend :: forall a. CellState_ext () -> a -> CellState_ext a;
extend r more = CellState_ext (val_v r) more;

make :: Integer -> CellState_ext ();
make val_v = CellState_ext val_v ();

default_CellState_ext :: forall a. (Default a) => CellState_ext a;
default_CellState_ext = extend (make (0 :: Integer)) defaulta;

instance (Default a) => Default (CellState_ext a) where {
  defaulta = default_CellState_ext;
};

data ControllerState_ext a = ControllerState_ext Nat Integer Integer Nat Nat a
  deriving (Prelude.Read, Prelude.Show);

equal_ControllerState_ext ::
  forall a. (Eq a) => ControllerState_ext a -> ControllerState_ext a -> Bool;
equal_ControllerState_ext
  (ControllerState_ext sz_va ringsize_va cache_va rtop_va rbot_va morea)
  (ControllerState_ext sz_v ringsize_v cache_v rtop_v rbot_v more) =
  equal_nat sz_va sz_v &&
    ringsize_va == ringsize_v &&
      cache_va == cache_v &&
        equal_nat rtop_va rtop_v && equal_nat rbot_va rbot_v && morea == more;

instance (Eq a) => Eq (ControllerState_ext a) where {
  a == b = equal_ControllerState_ext a b;
};

ringsize_v :: forall a. ControllerState_ext a -> Integer;
ringsize_v (ControllerState_ext sz_v ringsize_v cache_v rtop_v rbot_v more) =
  ringsize_v;

cache_v :: forall a. ControllerState_ext a -> Integer;
cache_v (ControllerState_ext sz_v ringsize_v cache_v rtop_v rbot_v more) =
  cache_v;

rtop_v :: forall a. ControllerState_ext a -> Nat;
rtop_v (ControllerState_ext sz_v ringsize_v cache_v rtop_v rbot_v more) =
  rtop_v;

rbot_v :: forall a. ControllerState_ext a -> Nat;
rbot_v (ControllerState_ext sz_v ringsize_v cache_v rtop_v rbot_v more) =
  rbot_v;

sz_v :: forall a. ControllerState_ext a -> Nat;
sz_v (ControllerState_ext sz_v ringsize_v cache_v rtop_v rbot_v more) = sz_v;

extenda :: forall a. ControllerState_ext () -> a -> ControllerState_ext a;
extenda r more =
  ControllerState_ext (sz_v r) (ringsize_v r) (cache_v r) (rtop_v r) (rbot_v r)
    more;

makea :: Nat -> Integer -> Integer -> Nat -> Nat -> ControllerState_ext ();
makea sz_v ringsize_v cache_v rtop_v rbot_v =
  ControllerState_ext sz_v ringsize_v cache_v rtop_v rbot_v ();

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

default_ControllerState_ext :: forall a. (Default a) => ControllerState_ext a;
default_ControllerState_ext =
  extenda (makea zero_nat (0 :: Integer) (0 :: Integer) zero_nat zero_nat)
    defaulta;

instance (Default a) => Default (ControllerState_ext a) where {
  defaulta = default_ControllerState_ext;
};

newtype Int = Int_of_integer Integer deriving (Prelude.Read, Prelude.Show);

data Num = One | Bit0 Num | Bit1 Num deriving (Prelude.Read, Prelude.Show);

data Andor a b = Left a | Right b | Both (a, b)
  deriving (Prelude.Read, Prelude.Show);

data Prism_ext a b c = Prism_ext (b -> Maybe a) (a -> b) c;

data Lens_ext a b c = Lens_ext (b -> a) (b -> a -> b) c;

integer_of_int :: Int -> Integer;
integer_of_int (Int_of_integer k) = k;

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (max (0 :: Integer) k);

nat :: Int -> Nat;
nat = nat_of_integer . integer_of_int;

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

minus_int :: Int -> Int -> Int;
minus_int k l = Int_of_integer (integer_of_int k - integer_of_int l);

less_int :: Int -> Int -> Bool;
less_int k l = integer_of_int k < integer_of_int l;

one_int :: Int;
one_int = Int_of_integer (1 :: Integer);

upto_aux :: Int -> Int -> [Int] -> [Int];
upto_aux i j js =
  (if less_int j i then js else upto_aux i (minus_int j one_int) (j : js));

upto :: Int -> Int -> [Int];
upto i j = upto_aux i j [];

foldl :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldl f a [] = a;
foldl f a (x : xs) = foldl f (f a x) xs;

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

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

is_empty :: forall a. Set a -> Bool;
is_empty (Set xs) = null xs;

the_elem :: forall a. Set a -> a;
the_elem (Set [x]) = x;

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
  forall a b c. (Eq a) => Itree a b -> Set a -> Itree a c -> Itree a (b, c);
par p a q =
  (case (p, q) of {
    (Ret r, Ret y) -> Ret (r, y);
    (Ret _, Sil qa) -> Sil (par p a qa);
    (Ret r, Vis g) ->
      Vis (map_pfun (par (Ret r) a) (pdom_res (uminus_set a) g));
    (Sil pa, _) -> Sil (par pa a q);
    (Vis pfun, Ret v) ->
      Vis (map_pfun (\ pa -> par pa a (Ret v)) (pdom_res (uminus_set a) pfun));
    (Vis _, Sil qa) -> Sil (par p a qa);
    (Vis pfun, Vis g) ->
      Vis (map_pfun (\ b -> (case b of {
                              Left pa -> par pa a q;
                              Right ba -> par p a ba;
                              Both ba -> (case ba of {
   (pa, bb) -> par pa a bb;
 });
                            }))
            (emerge pfun a g));
  });

deadlock :: forall a b. Itree a b;
deadlock = Vis zero_pfun;

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (suc n) xs;
gen_length n [] = n;

size_list :: forall a. [a] -> Nat;
size_list = gen_length zero_nat;

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

is_none :: forall a. Maybe a -> Bool;
is_none (Just x) = False;
is_none Nothing = True;

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

val_v_update ::
  forall a. (Integer -> Integer) -> CellState_ext a -> CellState_ext a;
val_v_update val_va (CellState_ext val_v more) =
  CellState_ext (val_va val_v) more;

val :: forall a. Lens_ext Integer (CellState_ext a) ();
val = Lens_ext val_v (\ sigma u -> val_v_update (\ _ -> u) sigma) ();

lens_get :: forall a b c. Lens_ext a b c -> b -> a;
lens_get (Lens_ext lens_get lens_put more) = lens_get;

bind_itree :: forall a b c. Itree a b -> (b -> Itree a c) -> Itree a c;
bind_itree (Vis t) k = Vis (map_pfun (\ x -> bind_itree x k) t);
bind_itree (Sil t) k = Sil (bind_itree t k);
bind_itree (Ret v) k = k v;

output ::
  forall a b c.
    Prism_ext a b () -> (c -> a) -> (c -> Itree b c) -> c -> Itree b c;
output c e p = (\ s -> bind_itree (outp c (e s)) (\ _ -> p s));

un_rd_C :: Chan -> (Nat, Integer);
un_rd_C (Rd_C x1) = x1;

is_rd_C :: Chan -> Bool;
is_rd_C (Rd_C x1) = True;
is_rd_C (Wrt_C x2) = False;
is_rd_C (Input_C x3) = False;
is_rd_C (Output_C x4) = False;

ctor_prism ::
  forall a b. (a -> b) -> (b -> Bool) -> (b -> a) -> Prism_ext a b ();
ctor_prism ctor disc sel =
  Prism_ext (\ d -> (if disc d then Just (sel d) else Nothing)) ctor ();

rd :: Prism_ext (Nat, Integer) Chan ();
rd = ctor_prism Rd_C is_rd_C un_rd_C;

skip :: forall a b. a -> Itree b a;
skip = Ret;

sexp :: forall a b. (a -> b) -> a -> b;
sexp x = x;

read :: Nat -> CellState_ext () -> Itree Chan (CellState_ext ());
read i = output rd (sexp (\ s -> (i, lens_get val s))) skip;

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n = Nat (max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

zero_int :: Int;
zero_int = Int_of_integer (0 :: Integer);

int_of_nat :: Nat -> Int;
int_of_nat n = Int_of_integer (integer_of_nat n);

bot_set :: forall a. Set a;
bot_set = Set [];

extchoice_fun :: forall a b. (Extchoice b) => (a -> b) -> (a -> b) -> a -> b;
extchoice_fun p q = (\ s -> extchoice (p s) (q s));

kleisli_comp :: forall a b c d. (a -> b -> c) -> (d -> a) -> b -> d -> c;
kleisli_comp bnd f g = (\ x -> bnd (f x) g);

lens_put :: forall a b c. Lens_ext a b c -> b -> a -> b;
lens_put (Lens_ext lens_get lens_put more) = lens_put;

subst_upd :: forall a b c. (a -> b) -> Lens_ext c b () -> (a -> c) -> a -> b;
subst_upd sigma x e = (\ s -> lens_put x (sigma s) (e s));

subst_id :: forall a. a -> a;
subst_id = (\ s -> s);

while :: forall a b. (a -> Bool) -> (a -> Itree b a) -> a -> Itree b a;
while b p s = (if b s then bind_itree (p s) (Sil . while b p) else Ret s);

assigns :: forall a b c. (a -> b) -> a -> Itree c b;
assigns sigma = (\ s -> Ret (sigma s));

proc :: forall a b. (Default a) => (a -> a) -> (a -> Itree b a) -> Itree b ();
proc i a =
  kleisli_comp bind_itree
    (kleisli_comp bind_itree
      (kleisli_comp bind_itree (assigns (\ _ -> defaulta)) (assigns i)) a)
    (assigns (\ _ -> ())) ();

prism_match :: forall a b c. Prism_ext a b c -> b -> Maybe a;
prism_match (Prism_ext prism_match prism_build more) = prism_match;

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

input_in ::
  forall a b c.
    Prism_ext a b () -> (c -> [a]) -> (a -> c -> Itree b c) -> c -> Itree b c;
input_in c a p = (\ s -> bind_itree (inp_list c (a s)) (\ x -> p x s));

un_wrt_C :: Chan -> (Nat, Integer);
un_wrt_C (Wrt_C x2) = x2;

is_wrt_C :: Chan -> Bool;
is_wrt_C (Rd_C x1) = False;
is_wrt_C (Wrt_C x2) = True;
is_wrt_C (Input_C x3) = False;
is_wrt_C (Output_C x4) = False;

wrt :: Prism_ext (Nat, Integer) Chan ();
wrt = ctor_prism Wrt_C is_wrt_C un_wrt_C;

write :: Nat -> CellState_ext () -> Itree Chan (CellState_ext ());
write i =
  input_in wrt
    (sexp (\ _ ->
            map (\ a -> (i, a))
              [(0 :: Integer), (1 :: Integer), (2 :: Integer), (3 :: Integer)]))
    (\ (_, v) -> assigns (subst_upd subst_id val (sexp (\ _ -> v))));

iRingCell :: Nat -> Itree Chan ();
iRingCell i =
  proc (subst_upd subst_id val (sexp (\ _ -> (0 :: Integer))))
    (kleisli_comp bind_itree (write i)
      (while (\ _ -> True) (extchoice_fun (read i) (write i))));

maxring :: Nat;
maxring = nat_of_integer (20 :: Integer);

gpar_csp ::
  forall a b c. (Eq a) => Itree a b -> Set a -> Itree a c -> Itree a ();
gpar_csp p cs q = bind_itree (par p cs q) (\ (_, _) -> Ret ());

ring :: Itree Chan ();
ring =
  foldl (\ a x -> gpar_csp a bot_set ((iRingCell . nat) x)) (Ret ())
    (upto zero_int (int_of_nat (minus_nat maxring one_nat)));

cache_v_update ::
  forall a.
    (Integer -> Integer) -> ControllerState_ext a -> ControllerState_ext a;
cache_v_update cache_va
  (ControllerState_ext sz_v ringsize_v cache_v rtop_v rbot_v more) =
  ControllerState_ext sz_v ringsize_v (cache_va cache_v) rtop_v rbot_v more;

cache :: forall a. Lens_ext Integer (ControllerState_ext a) ();
cache = Lens_ext cache_v (\ sigma u -> cache_v_update (\ _ -> u) sigma) ();

rbot_v_update ::
  forall a. (Nat -> Nat) -> ControllerState_ext a -> ControllerState_ext a;
rbot_v_update rbot_va
  (ControllerState_ext sz_v ringsize_v cache_v rtop_v rbot_v more) =
  ControllerState_ext sz_v ringsize_v cache_v rtop_v (rbot_va rbot_v) more;

rbot :: forall a. Lens_ext Nat (ControllerState_ext a) ();
rbot = Lens_ext rbot_v (\ sigma u -> rbot_v_update (\ _ -> u) sigma) ();

sz_v_update ::
  forall a. (Nat -> Nat) -> ControllerState_ext a -> ControllerState_ext a;
sz_v_update sz_va
  (ControllerState_ext sz_v ringsize_v cache_v rtop_v rbot_v more) =
  ControllerState_ext (sz_va sz_v) ringsize_v cache_v rtop_v rbot_v more;

sz :: forall a. Lens_ext Nat (ControllerState_ext a) ();
sz = Lens_ext sz_v (\ sigma u -> sz_v_update (\ _ -> u) sigma) ();

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod (abs k) (abs l)
                  else (case divMod (abs k) (abs l) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else apsnd negate
                         (if k < (0 :: Integer) then divMod (abs k) (abs l)
                           else (case divMod (abs k) (abs l) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

modulo_integer :: Integer -> Integer -> Integer;
modulo_integer k l = snd (divmod_integer k l);

modulo_nat :: Nat -> Nat -> Nat;
modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

storeNewCache ::
  Integer -> ControllerState_ext () -> Itree Chan (ControllerState_ext ());
storeNewCache x =
  kleisli_comp bind_itree
    (kleisli_comp bind_itree
      (assigns
        (subst_upd subst_id sz
          (sexp (\ s -> minus_nat (lens_get sz s) one_nat))))
      (assigns (subst_upd subst_id cache (sexp (\ _ -> x)))))
    (assigns
      (subst_upd subst_id rbot
        (sexp (\ s ->
                modulo_nat (plus_nat (lens_get rbot s) one_nat) maxring))));

un_output_C :: Chan -> Integer;
un_output_C (Output_C x4) = x4;

is_output_C :: Chan -> Bool;
is_output_C (Rd_C x1) = False;
is_output_C (Wrt_C x2) = False;
is_output_C (Input_C x3) = False;
is_output_C (Output_C x4) = True;

outputa :: Prism_ext Integer Chan ();
outputa = ctor_prism Output_C is_output_C un_output_C;

noNewCache :: ControllerState_ext () -> Itree Chan (ControllerState_ext ());
noNewCache = assigns (subst_upd subst_id sz (sexp (\ _ -> zero_nat)));

test :: forall a b. (a -> Bool) -> a -> Itree b a;
test b = (\ s -> (if b s then Ret s else deadlock));

outputController ::
  ControllerState_ext () -> Itree Chan (ControllerState_ext ());
outputController =
  kleisli_comp bind_itree
    (test (sexp (\ s -> less_nat zero_nat (lens_get sz s))))
    (output outputa (sexp (lens_get cache))
      (extchoice_fun
        (kleisli_comp bind_itree
          (test (sexp (\ s -> less_nat one_nat (lens_get sz s))))
          (input_in rd
            (sexp (\ s ->
                    map (\ a -> (lens_get rbot s, a))
                      [(0 :: Integer), (1 :: Integer), (2 :: Integer),
                        (3 :: Integer)]))
            (\ (_, a) -> storeNewCache a)))
        (kleisli_comp bind_itree
          (test (sexp (\ s -> equal_nat (lens_get sz s) one_nat)))
          noNewCache)));

rtop_v_update ::
  forall a. (Nat -> Nat) -> ControllerState_ext a -> ControllerState_ext a;
rtop_v_update rtop_va
  (ControllerState_ext sz_v ringsize_v cache_v rtop_v rbot_v more) =
  ControllerState_ext sz_v ringsize_v cache_v (rtop_va rtop_v) rbot_v more;

rtop :: forall a. Lens_ext Nat (ControllerState_ext a) ();
rtop = Lens_ext rtop_v (\ sigma u -> rtop_v_update (\ _ -> u) sigma) ();

un_input_C :: Chan -> Integer;
un_input_C (Input_C x3) = x3;

is_input_C :: Chan -> Bool;
is_input_C (Rd_C x1) = False;
is_input_C (Wrt_C x2) = False;
is_input_C (Input_C x3) = True;
is_input_C (Output_C x4) = False;

input :: Prism_ext Integer Chan ();
input = ctor_prism Input_C is_input_C un_input_C;

storeInput :: ControllerState_ext () -> Itree Chan (ControllerState_ext ());
storeInput =
  kleisli_comp bind_itree
    (assigns
      (subst_upd subst_id sz (sexp (\ s -> plus_nat (lens_get sz s) one_nat))))
    (assigns
      (subst_upd subst_id rtop
        (sexp (\ s ->
                modulo_nat (plus_nat (lens_get rtop s) one_nat) maxring))));

cacheInput ::
  Integer -> ControllerState_ext () -> Itree Chan (ControllerState_ext ());
cacheInput x =
  kleisli_comp bind_itree
    (assigns (subst_upd subst_id sz (sexp (\ _ -> one_nat))))
    (assigns (subst_upd subst_id cache (sexp (\ _ -> x))));

inputController ::
  ControllerState_ext () -> Itree Chan (ControllerState_ext ());
inputController =
  kleisli_comp bind_itree
    (test (sexp (\ s -> less_nat (lens_get sz s) (minus_nat maxring one_nat))))
    (input_in input
      (sexp (\ _ ->
              [(0 :: Integer), (1 :: Integer), (2 :: Integer), (3 :: Integer)]))
      (\ x ->
        extchoice_fun
          (kleisli_comp bind_itree
            (test (sexp (\ s -> equal_nat (lens_get sz s) zero_nat)))
            (cacheInput x))
          (kleisli_comp bind_itree
            (test (sexp (\ s -> less_nat zero_nat (lens_get sz s))))
            (output wrt (sexp (\ s -> (lens_get rtop s, x))) storeInput))));

initController :: ControllerState_ext () -> ControllerState_ext ();
initController =
  subst_upd
    (subst_upd (subst_upd subst_id sz (sexp (\ _ -> zero_nat))) rbot
      (sexp (\ _ -> zero_nat)))
    rtop (sexp (\ _ -> zero_nat));

controller :: Itree Chan ();
controller =
  proc initController
    (while (\ _ -> True) (extchoice_fun inputController outputController));

cRing :: Itree Chan ();
cRing =
  hide (gpar_csp controller
         (Set (concatMap
                 (\ i ->
                   map (\ v -> Rd_C (nat i, v))
                     [(0 :: Integer), (1 :: Integer), (2 :: Integer),
                       (3 :: Integer)])
                 (upto zero_int (int_of_nat (minus_nat maxring one_nat))) ++
                concatMap
                  (\ i ->
                    map (\ v -> Wrt_C (nat i, v))
                      [(0 :: Integer), (1 :: Integer), (2 :: Integer),
                        (3 :: Integer)])
                  (upto zero_int (int_of_nat (minus_nat maxring one_nat)))))
         ring)
    (Set (concatMap
            (\ i ->
              map (\ v -> Rd_C (nat i, v))
                [(0 :: Integer), (1 :: Integer), (2 :: Integer),
                  (3 :: Integer)])
            (upto zero_int (int_of_nat (minus_nat maxring one_nat))) ++
           concatMap
             (\ i ->
               map (\ v -> Wrt_C (nat i, v))
                 [(0 :: Integer), (1 :: Integer), (2 :: Integer),
                   (3 :: Integer)])
             (upto zero_int (int_of_nat (minus_nat maxring one_nat)))));

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

simulate :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Itree e s -> Prelude.IO ();
simulate = simulate_cnt 0;

}
