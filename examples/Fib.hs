{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Fib(Chan, Itree, FibState_ext, fib) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
{-# import qualified Simulate; #-}

data Nat = Zero_nat | Suc Nat deriving (Prelude.Read, Prelude.Show);

equal_nat :: Nat -> Nat -> Bool;
equal_nat Zero_nat (Suc x2) = False;
equal_nat (Suc x2) Zero_nat = False;
equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2;
equal_nat Zero_nat Zero_nat = True;

newtype Chan = Out_C Nat deriving (Prelude.Read, Prelude.Show);

equal_chan :: Chan -> Chan -> Bool;
equal_chan (Out_C x) (Out_C ya) = equal_nat x ya;

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

data FibState_ext a = FibState_ext Nat Nat a
  deriving (Prelude.Read, Prelude.Show);

equal_FibState_ext ::
  forall a. (Eq a) => FibState_ext a -> FibState_ext a -> Bool;
equal_FibState_ext (FibState_ext x_va y_va morea) (FibState_ext x_v y_v more) =
  equal_nat x_va x_v && equal_nat y_va y_v && morea == more;

instance (Eq a) => Eq (FibState_ext a) where {
  a == b = equal_FibState_ext a b;
};

y_v :: forall a. FibState_ext a -> Nat;
y_v (FibState_ext x_v y_v more) = y_v;

x_v :: forall a. FibState_ext a -> Nat;
x_v (FibState_ext x_v y_v more) = x_v;

extend :: forall a. FibState_ext () -> a -> FibState_ext a;
extend r more = FibState_ext (x_v r) (y_v r) more;

make :: Nat -> Nat -> FibState_ext ();
make x_v y_v = FibState_ext x_v y_v ();

default_FibState_ext :: forall a. (Default a) => FibState_ext a;
default_FibState_ext = extend (make Zero_nat Zero_nat) defaulta;

instance (Default a) => Default (FibState_ext a) where {
  defaulta = default_FibState_ext;
};

data Prism_ext a b c = Prism_ext (b -> Maybe a) (a -> b) c;

data Lens_ext a b c = Lens_ext (b -> a) (b -> a -> b) c;

extchoice_fun :: forall a b. (Extchoice b) => (a -> b) -> (a -> b) -> a -> b;
extchoice_fun p q = (\ s -> extchoice (p s) (q s));

kleisli_comp :: forall a b c d. (a -> b -> c) -> (d -> a) -> b -> d -> c;
kleisli_comp bnd f g = (\ x -> bnd (f x) g);

map_pfun :: forall a b c. (a -> b) -> Pfun c a -> Pfun c b;
map_pfun f (Pfun_of_alist m) = Pfun_of_alist (map (\ (k, v) -> (k, f v)) m);

bind_itree :: forall a b c. Itree a b -> (b -> Itree a c) -> Itree a c;
bind_itree (Vis t) k = Vis (map_pfun (\ x -> bind_itree x k) t);
bind_itree (Sil t) k = Sil (bind_itree t k);
bind_itree (Ret v) k = k v;

deadlock :: forall a b. Itree a b;
deadlock = Vis zero_pfun;

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

one_nat :: Nat;
one_nat = Suc Zero_nat;

lens_put :: forall a b c. Lens_ext a b c -> b -> a -> b;
lens_put (Lens_ext lens_get lens_put more) = lens_put;

subst_upd :: forall a b c. (a -> b) -> Lens_ext c b () -> (a -> c) -> a -> b;
subst_upd sigma x e = (\ s -> lens_put x (sigma s) (e s));

subst_id :: forall a. a -> a;
subst_id = (\ s -> s);

prism_build :: forall a b c. Prism_ext a b c -> a -> b;
prism_build (Prism_ext prism_match prism_build more) = prism_build;

outp :: forall a b. Prism_ext a b () -> a -> Itree b ();
outp c v = Vis (Pfun_of_alist [(prism_build c v, Ret ())]);

output ::
  forall a b c.
    Prism_ext a b () -> (c -> a) -> (c -> Itree b c) -> c -> Itree b c;
output c e p = (\ s -> bind_itree (outp c (e s)) (\ _ -> p s));

sexp :: forall a b. (a -> b) -> a -> b;
sexp x = x;

y_v_update :: forall a. (Nat -> Nat) -> FibState_ext a -> FibState_ext a;
y_v_update y_va (FibState_ext x_v y_v more) = FibState_ext x_v (y_va y_v) more;

y :: forall a. Lens_ext Nat (FibState_ext a) ();
y = Lens_ext y_v (\ sigma u -> y_v_update (\ _ -> u) sigma) ();

x_v_update :: forall a. (Nat -> Nat) -> FibState_ext a -> FibState_ext a;
x_v_update x_va (FibState_ext x_v y_v more) = FibState_ext (x_va x_v) y_v more;

x :: forall a. Lens_ext Nat (FibState_ext a) ();
x = Lens_ext x_v (\ sigma u -> x_v_update (\ _ -> u) sigma) ();

ctor_prism ::
  forall a b. (a -> b) -> (b -> Bool) -> (b -> a) -> Prism_ext a b ();
ctor_prism ctor disc sel =
  Prism_ext (\ d -> (if disc d then Just (sel d) else Nothing)) ctor ();

un_out_C :: Chan -> Nat;
un_out_C (Out_C x) = x;

out :: Prism_ext Nat Chan ();
out = ctor_prism Out_C (\ _ -> True) un_out_C;

initFib :: forall a. FibState_ext a -> Itree Chan (FibState_ext a);
initFib =
  output out (sexp (\ _ -> one_nat))
    (output out (sexp (\ _ -> one_nat))
      (kleisli_comp bind_itree
        (assigns (subst_upd subst_id x (sexp (\ _ -> one_nat))))
        (assigns (subst_upd subst_id y (sexp (\ _ -> one_nat))))));

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero_nat n = n;

lens_get :: forall a b c. Lens_ext a b c -> b -> a;
lens_get (Lens_ext lens_get lens_put more) = lens_get;

outFib :: forall a. FibState_ext a -> Itree Chan (FibState_ext a);
outFib =
  output out (sexp (\ s -> plus_nat (lens_get x s) (lens_get y s)))
    (assigns
      (subst_upd (subst_upd subst_id x (sexp (lens_get y))) y
        (sexp (\ s -> plus_nat (lens_get x s) (lens_get y s)))));

init :: FibState_ext () -> FibState_ext ();
init =
  subst_upd (subst_upd subst_id x (sexp (\ _ -> Zero_nat))) y
    (sexp (\ _ -> Zero_nat));

fib :: Itree Chan ();
fib = proc init
        (kleisli_comp bind_itree initFib
          (while (\ _ -> True) (extchoice_fun outFib (\ _ -> deadlock))));

}
