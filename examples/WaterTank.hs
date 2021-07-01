{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module WaterTank(Chan, Itree, TankState_ext, Lens_ext, waterTank) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Chan = Tock_C () | ViewLevel_C Integer | Switch_C ()
  deriving (Prelude.Read, Prelude.Show);

equal_chan :: Chan -> Chan -> Bool;
equal_chan (ViewLevel_C x2) (Switch_C x3) = False;
equal_chan (Switch_C x3) (ViewLevel_C x2) = False;
equal_chan (Tock_C x1) (Switch_C x3) = False;
equal_chan (Switch_C x3) (Tock_C x1) = False;
equal_chan (Tock_C x1) (ViewLevel_C x2) = False;
equal_chan (ViewLevel_C x2) (Tock_C x1) = False;
equal_chan (Switch_C x3) (Switch_C y3) = x3 == y3;
equal_chan (ViewLevel_C x2) (ViewLevel_C y2) = x2 == y2;
equal_chan (Tock_C x1) (Tock_C y1) = x1 == y1;

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

newtype Pinj a b = Pinj_of_alist [(a, b)] deriving (Prelude.Read, Prelude.Show);

data Pfun a b = Pfun_of_alist [(a, b)] | Pfun_of_map (a -> Maybe b)
  | Pfun_of_pinj (Pinj a b);

zero_pfun :: forall a b. Pfun a b;
zero_pfun = Pfun_of_alist [];

data Itree a b = Ret b | Sil (Itree a b) | Vis (Pfun a (Itree a b));

genchoice ::
  forall a b.
    (Eq b) => (Pfun a (Itree a b) ->
                Pfun a (Itree a b) -> Pfun a (Itree a b)) ->
                Itree a b -> Itree a b -> Itree a b;
genchoice m p q =
  (case (p, q) of {
    (Ret r, Ret y) -> (if r == y then Ret r else Vis zero_pfun);
    (Ret _, Sil qa) -> Sil (genchoice m p qa);
    (Ret r, Vis _) -> Ret r;
    (Sil pa, _) -> Sil (genchoice m pa q);
    (Vis _, Ret a) -> Ret a;
    (Vis _, Sil qa) -> Sil (genchoice m p qa);
    (Vis f, Vis g) -> Vis (m f g);
  });

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
extchoice_itree = genchoice map_prod;

class Extchoice a where {
  extchoice :: a -> a -> a;
};

instance (Eq a, Eq b) => Extchoice (Itree a b) where {
  extchoice = extchoice_itree;
};

data TankState_ext a = TankState_ext Bool Integer Bool a
  deriving (Prelude.Read, Prelude.Show);

equal_TankState_ext ::
  forall a. (Eq a) => TankState_ext a -> TankState_ext a -> Bool;
equal_TankState_ext (TankState_ext flowOn_va level_va finished_va morea)
  (TankState_ext flowOn_v level_v finished_v more) =
  flowOn_va == flowOn_v &&
    level_va == level_v && finished_va == finished_v && morea == more;

instance (Eq a) => Eq (TankState_ext a) where {
  a == b = equal_TankState_ext a b;
};

default_integer :: Integer;
default_integer = (0 :: Integer);

default_bool :: Bool;
default_bool = False;

finished_v :: forall a. TankState_ext a -> Bool;
finished_v (TankState_ext flowOn_v level_v finished_v more) = finished_v;

flowOn_v :: forall a. TankState_ext a -> Bool;
flowOn_v (TankState_ext flowOn_v level_v finished_v more) = flowOn_v;

level_v :: forall a. TankState_ext a -> Integer;
level_v (TankState_ext flowOn_v level_v finished_v more) = level_v;

extend :: forall a. TankState_ext () -> a -> TankState_ext a;
extend r more = TankState_ext (flowOn_v r) (level_v r) (finished_v r) more;

make :: Bool -> Integer -> Bool -> TankState_ext ();
make flowOn_v level_v finished_v = TankState_ext flowOn_v level_v finished_v ();

default_TankState_ext :: forall a. (Default a) => TankState_ext a;
default_TankState_ext =
  extend (make default_bool default_integer default_bool) defaulta;

instance (Default a) => Default (TankState_ext a) where {
  defaulta = default_TankState_ext;
};

data Num = One | Bit0 Num | Bit1 Num deriving (Prelude.Read, Prelude.Show);

data Prism_ext a b c = Prism_ext (b -> Maybe a) (a -> b) c;

data Lens_ext a b c = Lens_ext (b -> a) (b -> a -> b) c;

flowOn_v_update ::
  forall a. (Bool -> Bool) -> TankState_ext a -> TankState_ext a;
flowOn_v_update flowOn_va (TankState_ext flowOn_v level_v finished_v more) =
  TankState_ext (flowOn_va flowOn_v) level_v finished_v more;

flowOn :: forall a. Lens_ext Bool (TankState_ext a) ();
flowOn = Lens_ext flowOn_v (\ sigma u -> flowOn_v_update (\ _ -> u) sigma) ();

level_v_update ::
  forall a. (Integer -> Integer) -> TankState_ext a -> TankState_ext a;
level_v_update level_va (TankState_ext flowOn_v level_v finished_v more) =
  TankState_ext flowOn_v (level_va level_v) finished_v more;

level :: forall a. Lens_ext Integer (TankState_ext a) ();
level = Lens_ext level_v (\ sigma u -> level_v_update (\ _ -> u) sigma) ();

lens_put :: forall a b c. Lens_ext a b c -> b -> a -> b;
lens_put (Lens_ext lens_get lens_put more) = lens_put;

subst_upd :: forall a b c. (a -> b) -> Lens_ext c b () -> (a -> c) -> a -> b;
subst_upd sigma x e = (\ s -> lens_put x (sigma s) (e s));

lens_get :: forall a b c. Lens_ext a b c -> b -> a;
lens_get (Lens_ext lens_get lens_put more) = lens_get;

subst_id :: forall a. a -> a;
subst_id = (\ s -> s);

assigns :: forall a b c. (a -> b) -> a -> Itree c b;
assigns sigma = (\ s -> Ret (sigma s));

sexp :: forall a b. (a -> b) -> a -> b;
sexp x = x;

tstep :: Integer;
tstep = (1 :: Integer);

rate :: Integer;
rate = (5 :: Integer);

ode :: TankState_ext () -> Itree Chan (TankState_ext ());
ode = assigns
        (subst_upd subst_id level
          (sexp (\ s ->
                  lens_get level s +
                    tstep *
                      (if lens_get flowOn s then rate
                        else (if lens_get level s == (0 :: Integer)
                               then (0 :: Integer) else negate rate)))));

prism_build :: forall a b c. Prism_ext a b c -> a -> b;
prism_build (Prism_ext prism_match prism_build more) = prism_build;

outp :: forall a b. Prism_ext a b () -> a -> Itree b ();
outp c v = Vis (Pfun_of_alist [(prism_build c v, Ret ())]);

kleisli_comp :: forall a b c d. (a -> b -> c) -> (d -> a) -> b -> d -> c;
kleisli_comp bnd f g = (\ x -> bnd (f x) g);

map_pfun :: forall a b c. (a -> b) -> Pfun c a -> Pfun c b;
map_pfun f (Pfun_of_alist m) = Pfun_of_alist (map (\ (k, v) -> (k, f v)) m);

bind_itree :: forall a b c. Itree a b -> (b -> Itree a c) -> Itree a c;
bind_itree (Vis t) k = Vis (map_pfun (\ x -> bind_itree x k) t);
bind_itree (Sil t) k = Sil (bind_itree t k);
bind_itree (Ret v) k = k v;

extchoice_fun :: forall a b. (Extchoice b) => (a -> b) -> (a -> b) -> a -> b;
extchoice_fun p q = (\ s -> extchoice (p s) (q s));

finished_v_update ::
  forall a. (Bool -> Bool) -> TankState_ext a -> TankState_ext a;
finished_v_update finished_va (TankState_ext flowOn_v level_v finished_v more) =
  TankState_ext flowOn_v level_v (finished_va finished_v) more;

finished :: forall a. Lens_ext Bool (TankState_ext a) ();
finished =
  Lens_ext finished_v (\ sigma u -> finished_v_update (\ _ -> u) sigma) ();

un_viewLevel_C :: Chan -> Integer;
un_viewLevel_C (ViewLevel_C x2) = x2;

is_viewLevel_C :: Chan -> Bool;
is_viewLevel_C (Tock_C x1) = False;
is_viewLevel_C (ViewLevel_C x2) = True;
is_viewLevel_C (Switch_C x3) = False;

ctor_prism ::
  forall a b. (a -> b) -> (b -> Bool) -> (b -> a) -> Prism_ext a b ();
ctor_prism ctor disc sel =
  Prism_ext (\ d -> (if disc d then Just (sel d) else Nothing)) ctor ();

viewLevel :: Prism_ext Integer Chan ();
viewLevel = ctor_prism ViewLevel_C is_viewLevel_C un_viewLevel_C;

while :: forall a b. (a -> Bool) -> (a -> Itree b a) -> a -> Itree b a;
while b p s = (if b s then bind_itree (p s) (Sil . while b p) else Ret s);

un_switch_C :: Chan -> ();
un_switch_C (Switch_C x3) = x3;

is_switch_C :: Chan -> Bool;
is_switch_C (Tock_C x1) = False;
is_switch_C (ViewLevel_C x2) = False;
is_switch_C (Switch_C x3) = True;

switch :: Prism_ext () Chan ();
switch = ctor_prism Switch_C is_switch_C un_switch_C;

un_tock_C :: Chan -> ();
un_tock_C (Tock_C x1) = x1;

is_tock_C :: Chan -> Bool;
is_tock_C (Tock_C x1) = True;
is_tock_C (ViewLevel_C x2) = False;
is_tock_C (Switch_C x3) = False;

tock :: Prism_ext () Chan ();
tock = ctor_prism Tock_C is_tock_C un_tock_C;

output ::
  forall a b c.
    Prism_ext a b () -> (c -> a) -> (c -> Itree b c) -> c -> Itree b c;
output c e p = (\ s -> bind_itree (outp c (e s)) (\ _ -> p s));

skip :: forall a b. a -> Itree b a;
skip = Ret;

comms :: TankState_ext () -> Itree Chan (TankState_ext ());
comms =
  kleisli_comp bind_itree
    (assigns (subst_upd subst_id finished (sexp (\ _ -> False))))
    (while (sexp (\ s -> not (lens_get finished s)))
      (extchoice_fun
        (extchoice_fun (output viewLevel (sexp (lens_get level)) skip)
          (output switch (sexp (\ _ -> ()))
            (assigns
              (subst_upd subst_id flowOn
                (sexp (\ s -> not (lens_get flowOn s)))))))
        (output tock (sexp (\ _ -> ()))
          (assigns (subst_upd subst_id finished (sexp (\ _ -> True)))))));

tank :: TankState_ext () -> Itree Chan (TankState_ext ());
tank = kleisli_comp bind_itree ode comms;

proc :: forall a b. (Default a) => (a -> a) -> (a -> Itree b a) -> Itree b ();
proc i a =
  kleisli_comp bind_itree
    (kleisli_comp bind_itree
      (kleisli_comp bind_itree (assigns (\ _ -> defaulta)) (assigns i)) a)
    (assigns (\ _ -> ())) ();

deadlock :: forall a b. Itree a b;
deadlock = Vis zero_pfun;

waterTank :: Itree Chan ();
waterTank =
  proc (subst_upd subst_id level (sexp (\ _ -> (0 :: Integer))))
    (while (\ _ -> True) (extchoice_fun tank (\ _ -> deadlock)));
-- These library functions help us to trim the "_C" strings from pretty printed events

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
