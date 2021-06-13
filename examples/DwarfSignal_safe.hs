{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module DwarfSignal_safe(ProperState, Set, Chan, Itree, dwarf_safe) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

default_unit :: ();
default_unit = ();

class Default a where {
  defaulta :: a;
};

instance Default () where {
  defaulta = default_unit;
};

data ProperState = Dark | Stop | Warning | Drive
  deriving (Prelude.Read, Prelude.Show);

equal_ProperState :: ProperState -> ProperState -> Bool;
equal_ProperState Warning Drive = False;
equal_ProperState Drive Warning = False;
equal_ProperState Stop Drive = False;
equal_ProperState Drive Stop = False;
equal_ProperState Stop Warning = False;
equal_ProperState Warning Stop = False;
equal_ProperState Dark Drive = False;
equal_ProperState Drive Dark = False;
equal_ProperState Dark Warning = False;
equal_ProperState Warning Dark = False;
equal_ProperState Dark Stop = False;
equal_ProperState Stop Dark = False;
equal_ProperState Drive Drive = True;
equal_ProperState Warning Warning = True;
equal_ProperState Stop Stop = True;
equal_ProperState Dark Dark = True;

data LampId = L1 | L2 | L3 deriving (Prelude.Read, Prelude.Show);

equal_LampId :: LampId -> LampId -> Bool;
equal_LampId L2 L3 = False;
equal_LampId L3 L2 = False;
equal_LampId L1 L3 = False;
equal_LampId L3 L1 = False;
equal_LampId L1 L2 = False;
equal_LampId L2 L1 = False;
equal_LampId L3 L3 = True;
equal_LampId L2 L2 = True;
equal_LampId L1 L1 = True;

data Set a = Set [a] | Coset [a] deriving (Prelude.Read, Prelude.Show);

data Chan = Shine_C (Set LampId) | SetNewProperState_C ProperState
  | TurnOff_C LampId | TurnOn_C LampId | LastProperState_C ProperState
  deriving (Prelude.Read, Prelude.Show);

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
less_eq_set (Coset []) (Set []) = False;
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;

equal_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
equal_set a b = less_eq_set a b && less_eq_set b a;

instance Eq LampId where {
  a == b = equal_LampId a b;
};

equal_chan :: Chan -> Chan -> Bool;
equal_chan (TurnOn_C x4) (LastProperState_C x5) = False;
equal_chan (LastProperState_C x5) (TurnOn_C x4) = False;
equal_chan (TurnOff_C x3) (LastProperState_C x5) = False;
equal_chan (LastProperState_C x5) (TurnOff_C x3) = False;
equal_chan (TurnOff_C x3) (TurnOn_C x4) = False;
equal_chan (TurnOn_C x4) (TurnOff_C x3) = False;
equal_chan (SetNewProperState_C x2) (LastProperState_C x5) = False;
equal_chan (LastProperState_C x5) (SetNewProperState_C x2) = False;
equal_chan (SetNewProperState_C x2) (TurnOn_C x4) = False;
equal_chan (TurnOn_C x4) (SetNewProperState_C x2) = False;
equal_chan (SetNewProperState_C x2) (TurnOff_C x3) = False;
equal_chan (TurnOff_C x3) (SetNewProperState_C x2) = False;
equal_chan (Shine_C x1) (LastProperState_C x5) = False;
equal_chan (LastProperState_C x5) (Shine_C x1) = False;
equal_chan (Shine_C x1) (TurnOn_C x4) = False;
equal_chan (TurnOn_C x4) (Shine_C x1) = False;
equal_chan (Shine_C x1) (TurnOff_C x3) = False;
equal_chan (TurnOff_C x3) (Shine_C x1) = False;
equal_chan (Shine_C x1) (SetNewProperState_C x2) = False;
equal_chan (SetNewProperState_C x2) (Shine_C x1) = False;
equal_chan (LastProperState_C x5) (LastProperState_C y5) =
  equal_ProperState x5 y5;
equal_chan (TurnOn_C x4) (TurnOn_C y4) = equal_LampId x4 y4;
equal_chan (TurnOff_C x3) (TurnOff_C y3) = equal_LampId x3 y3;
equal_chan (SetNewProperState_C x2) (SetNewProperState_C y2) =
  equal_ProperState x2 y2;
equal_chan (Shine_C x1) (Shine_C y1) = equal_set x1 y1;

instance Eq Chan where {
  a == b = equal_chan a b;
};

data Pfun a b = Pfun_of_alist [(a, b)] | Pfun_of_map (a -> Maybe b);

zero_pfun :: forall a b. Pfun a b;
zero_pfun = Pfun_of_alist [];

data Itree a b = Ret b | Sil (Itree a b) | Vis (Pfun a (Itree a b));

plus_pfun :: forall a b. Pfun a b -> Pfun a b -> Pfun a b;
plus_pfun (Pfun_of_alist f) (Pfun_of_alist g) = Pfun_of_alist (g ++ f);

uminus_set :: forall a. Set a -> Set a;
uminus_set (Coset xs) = Set xs;
uminus_set (Set xs) = Coset xs;

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

instance Eq ProperState where {
  a == b = equal_ProperState a b;
};

data Dwarf_ext a =
  Dwarf_ext ProperState (Set LampId) (Set LampId) (Set LampId) (Set LampId)
    ProperState a
  deriving (Prelude.Read, Prelude.Show);

equal_Dwarf_ext :: forall a. (Eq a) => Dwarf_ext a -> Dwarf_ext a -> Bool;
equal_Dwarf_ext
  (Dwarf_ext last_proper_state_va turn_off_va turn_on_va last_state_va
    current_state_va desired_proper_state_va morea)
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = equal_ProperState last_proper_state_va last_proper_state_v &&
      equal_set turn_off_va turn_off_v &&
        equal_set turn_on_va turn_on_v &&
          equal_set last_state_va last_state_v &&
            equal_set current_state_va current_state_v &&
              equal_ProperState desired_proper_state_va
                desired_proper_state_v &&
                morea == more;

instance (Eq a) => Eq (Dwarf_ext a) where {
  a == b = equal_Dwarf_ext a b;
};

desired_proper_state_v :: forall a. Dwarf_ext a -> ProperState;
desired_proper_state_v
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = desired_proper_state_v;

last_proper_state_v :: forall a. Dwarf_ext a -> ProperState;
last_proper_state_v
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = last_proper_state_v;

current_state_v :: forall a. Dwarf_ext a -> Set LampId;
current_state_v
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = current_state_v;

last_state_v :: forall a. Dwarf_ext a -> Set LampId;
last_state_v
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = last_state_v;

turn_off_v :: forall a. Dwarf_ext a -> Set LampId;
turn_off_v
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = turn_off_v;

turn_on_v :: forall a. Dwarf_ext a -> Set LampId;
turn_on_v
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = turn_on_v;

extend :: forall a. Dwarf_ext () -> a -> Dwarf_ext a;
extend r more =
  Dwarf_ext (last_proper_state_v r) (turn_off_v r) (turn_on_v r)
    (last_state_v r) (current_state_v r) (desired_proper_state_v r) more;

bot_set :: forall a. Set a;
bot_set = Set [];

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (removeAll x xs);
insert x (Set xs) = Set (inserta x xs);

signalLamps :: ProperState -> Set LampId;
signalLamps Dark = bot_set;
signalLamps Stop = insert L1 (insert L2 bot_set);
signalLamps Warning = insert L1 (insert L3 bot_set);
signalLamps Drive = insert L2 (insert L3 bot_set);

make ::
  ProperState ->
    Set LampId ->
      Set LampId -> Set LampId -> Set LampId -> ProperState -> Dwarf_ext ();
make last_proper_state_v turn_off_v turn_on_v last_state_v current_state_v
  desired_proper_state_v =
  Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v ();

default_Dwarf_ext :: forall a. (Default a) => Dwarf_ext a;
default_Dwarf_ext =
  extend (make Dark bot_set bot_set (signalLamps Stop) (signalLamps Stop) Stop)
    defaulta;

instance (Default a) => Default (Dwarf_ext a) where {
  defaulta = default_Dwarf_ext;
};

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

remove :: forall a. (Eq a) => a -> Set a -> Set a;
remove x (Coset xs) = Coset (inserta x xs);
remove x (Set xs) = Set (removeAll x xs);

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

sexp :: forall a b. (a -> b) -> a -> b;
sexp x = x;

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

inp_in :: forall a b. Prism_ext a b () -> Set a -> Itree b a;
inp_in c (Set b) = inp_list c b;

skip :: forall a b. a -> Itree b a;
skip = Ret;

kleisli_comp :: forall a b c d. (a -> b -> c) -> (d -> a) -> b -> d -> c;
kleisli_comp bnd f g = (\ x -> bnd (f x) g);

bind_itree :: forall a b c. Itree a b -> (b -> Itree a c) -> Itree a c;
bind_itree (Vis t) k = Vis (map_pfun (\ x -> bind_itree x k) t);
bind_itree (Sil t) k = Sil (bind_itree t k);
bind_itree (Ret v) k = k v;

assigns :: forall a b c. (a -> b) -> a -> Itree c b;
assigns sigma = (\ s -> Ret (sigma s));

proc :: forall a b. (Default a) => (a -> a) -> (a -> Itree b a) -> Itree b ();
proc i a =
  kleisli_comp bind_itree
    (kleisli_comp bind_itree
      (kleisli_comp bind_itree (assigns (\ _ -> defaulta)) (assigns i)) a)
    (assigns (\ _ -> ())) ();

deadlock :: forall a b. Itree a b;
deadlock = Vis zero_pfun;

test :: forall a b. (a -> Bool) -> a -> Itree b a;
test b = (\ s -> (if b s then Ret s else deadlock));

gpar_csp ::
  forall a b c. (Eq a) => Itree a b -> Set a -> Itree a c -> Itree a ();
gpar_csp p cs q = bind_itree (par p cs q) (\ (_, _) -> Ret ());

output ::
  forall a b c.
    Prism_ext a b () -> (c -> a) -> (c -> Itree b c) -> c -> Itree b c;
output c e p = (\ s -> bind_itree (outp c (e s)) (\ _ -> p s));

subst_id :: forall a. a -> a;
subst_id = (\ s -> s);

while :: forall a b. (a -> Bool) -> (a -> Itree b a) -> a -> Itree b a;
while b p s = (if b s then bind_itree (p s) (Sil . while b p) else Ret s);

extchoice_fun :: forall a b. (Extchoice b) => (a -> b) -> (a -> b) -> a -> b;
extchoice_fun p q = (\ s -> extchoice (p s) (q s));

un_setNewProperState_C :: Chan -> ProperState;
un_setNewProperState_C (SetNewProperState_C x2) = x2;

is_setNewProperState_C :: Chan -> Bool;
is_setNewProperState_C (Shine_C x1) = False;
is_setNewProperState_C (SetNewProperState_C x2) = True;
is_setNewProperState_C (TurnOff_C x3) = False;
is_setNewProperState_C (TurnOn_C x4) = False;
is_setNewProperState_C (LastProperState_C x5) = False;

ctor_prism ::
  forall a b. (a -> b) -> (b -> Bool) -> (b -> a) -> Prism_ext a b ();
ctor_prism ctor disc sel =
  Prism_ext (\ d -> (if disc d then Just (sel d) else Nothing)) ctor ();

setNewProperStatea :: Prism_ext ProperState Chan ();
setNewProperStatea =
  ctor_prism SetNewProperState_C is_setNewProperState_C un_setNewProperState_C;

un_lastProperState_C :: Chan -> ProperState;
un_lastProperState_C (LastProperState_C x5) = x5;

is_lastProperState_C :: Chan -> Bool;
is_lastProperState_C (Shine_C x1) = False;
is_lastProperState_C (SetNewProperState_C x2) = False;
is_lastProperState_C (TurnOff_C x3) = False;
is_lastProperState_C (TurnOn_C x4) = False;
is_lastProperState_C (LastProperState_C x5) = True;

lastProperStatea :: Prism_ext ProperState Chan ();
lastProperStatea =
  ctor_prism LastProperState_C is_lastProperState_C un_lastProperState_C;

properState :: Set ProperState;
properState = insert Dark (insert Stop (insert Warning (insert Drive bot_set)));

input_in ::
  forall a b c.
    Prism_ext a b () -> (c -> Set a) -> (a -> c -> Itree b c) -> c -> Itree b c;
input_in c a p = (\ s -> bind_itree (inp_in c (a s)) (\ x -> p x s));

sP345 :: forall a. (Eq a) => a -> Itree Chan a;
sP345 =
  input_in lastProperStatea (sexp (\ _ -> properState))
    (\ l ->
      extchoice_fun
        (extchoice_fun
          (kleisli_comp bind_itree
            (test (sexp (\ _ -> equal_ProperState l Stop)))
            (input_in setNewProperStatea
              (sexp (\ _ -> remove Drive properState)) (\ _ -> skip)))
          (kleisli_comp bind_itree
            (test (sexp (\ _ -> equal_ProperState l Dark)))
            (input_in setNewProperStatea
              (sexp (\ _ -> insert Dark (insert Stop bot_set))) (\ _ -> skip))))
        (kleisli_comp bind_itree
          (test (sexp (\ _ ->
                        not (equal_ProperState l Dark) &&
                          not (equal_ProperState l Stop))))
          (input_in setNewProperStatea (sexp (\ _ -> remove Dark properState))
            (\ _ -> skip))));

ctrl :: Itree Chan ();
ctrl =
  (proc ::
    (Dwarf_ext () -> Dwarf_ext ()) ->
      (Dwarf_ext () -> Itree Chan (Dwarf_ext ())) -> Itree Chan ())
    subst_id
    (while (\ _ -> True) (sP345 :: Dwarf_ext () -> Itree Chan (Dwarf_ext ())));

desired_proper_state_v_update ::
  forall a. (ProperState -> ProperState) -> Dwarf_ext a -> Dwarf_ext a;
desired_proper_state_v_update desired_proper_state_va
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
      current_state_v (desired_proper_state_va desired_proper_state_v) more;

desired_proper_state :: forall a. Lens_ext ProperState (Dwarf_ext a) ();
desired_proper_state =
  Lens_ext desired_proper_state_v
    (\ sigma u -> desired_proper_state_v_update (\ _ -> u) sigma) ();

last_proper_state_v_update ::
  forall a. (ProperState -> ProperState) -> Dwarf_ext a -> Dwarf_ext a;
last_proper_state_v_update last_proper_state_va
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = Dwarf_ext (last_proper_state_va last_proper_state_v) turn_off_v turn_on_v
      last_state_v current_state_v desired_proper_state_v more;

last_proper_state :: forall a. Lens_ext ProperState (Dwarf_ext a) ();
last_proper_state =
  Lens_ext last_proper_state_v
    (\ sigma u -> last_proper_state_v_update (\ _ -> u) sigma) ();

current_state_v_update ::
  forall a. (Set LampId -> Set LampId) -> Dwarf_ext a -> Dwarf_ext a;
current_state_v_update current_state_va
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
      (current_state_va current_state_v) desired_proper_state_v more;

current_state :: forall a. Lens_ext (Set LampId) (Dwarf_ext a) ();
current_state =
  Lens_ext current_state_v
    (\ sigma u -> current_state_v_update (\ _ -> u) sigma) ();

last_state_v_update ::
  forall a. (Set LampId -> Set LampId) -> Dwarf_ext a -> Dwarf_ext a;
last_state_v_update last_state_va
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = Dwarf_ext last_proper_state_v turn_off_v turn_on_v
      (last_state_va last_state_v) current_state_v desired_proper_state_v more;

last_state :: forall a. Lens_ext (Set LampId) (Dwarf_ext a) ();
last_state =
  Lens_ext last_state_v (\ sigma u -> last_state_v_update (\ _ -> u) sigma) ();

turn_off_v_update ::
  forall a. (Set LampId -> Set LampId) -> Dwarf_ext a -> Dwarf_ext a;
turn_off_v_update turn_off_va
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = Dwarf_ext last_proper_state_v (turn_off_va turn_off_v) turn_on_v
      last_state_v current_state_v desired_proper_state_v more;

turn_off :: forall a. Lens_ext (Set LampId) (Dwarf_ext a) ();
turn_off =
  Lens_ext turn_off_v (\ sigma u -> turn_off_v_update (\ _ -> u) sigma) ();

turn_on_v_update ::
  forall a. (Set LampId -> Set LampId) -> Dwarf_ext a -> Dwarf_ext a;
turn_on_v_update turn_on_va
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = Dwarf_ext last_proper_state_v turn_off_v (turn_on_va turn_on_v) last_state_v
      current_state_v desired_proper_state_v more;

turn_on :: forall a. Lens_ext (Set LampId) (Dwarf_ext a) ();
turn_on =
  Lens_ext turn_on_v (\ sigma u -> turn_on_v_update (\ _ -> u) sigma) ();

lens_put :: forall a b c. Lens_ext a b c -> b -> a -> b;
lens_put (Lens_ext lens_get lens_put more) = lens_put;

subst_upd :: forall a b c. (a -> b) -> Lens_ext c b () -> (a -> c) -> a -> b;
subst_upd sigma x e = (\ s -> lens_put x (sigma s) (e s));

init :: Dwarf_ext () -> Dwarf_ext ();
init =
  subst_upd
    (subst_upd
      (subst_upd
        (subst_upd
          (subst_upd (subst_upd subst_id last_proper_state (sexp (\ _ -> Stop)))
            turn_off (sexp (\ _ -> bot_set)))
          turn_on (sexp (\ _ -> bot_set)))
        last_state (sexp (\ _ -> signalLamps Stop)))
      current_state (sexp (\ _ -> signalLamps Stop)))
    desired_proper_state (sexp (\ _ -> Stop));

minus_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
minus_set a (Coset xs) = Set (filter (\ x -> member x a) xs);
minus_set a (Set xs) = fold remove xs a;

lens_get :: forall a b c. Lens_ext a b c -> b -> a;
lens_get (Lens_ext lens_get lens_put more) = lens_get;

setNewProperState :: forall a. Dwarf_ext a -> Itree Chan (Dwarf_ext a);
setNewProperState =
  kleisli_comp bind_itree
    (test (sexp (\ s ->
                  equal_set (lens_get current_state s)
                    (signalLamps (lens_get desired_proper_state s)))))
    (input_in setNewProperStatea
      (sexp (\ s -> remove (lens_get desired_proper_state s) properState))
      (\ st ->
        kleisli_comp bind_itree
          (kleisli_comp bind_itree
            (kleisli_comp bind_itree
              (kleisli_comp bind_itree
                (assigns
                  (subst_upd subst_id last_proper_state
                    (sexp (lens_get desired_proper_state))))
                (assigns
                  (subst_upd subst_id turn_off
                    (sexp (\ s ->
                            minus_set (lens_get current_state s)
                              (signalLamps st))))))
              (assigns
                (subst_upd subst_id turn_on
                  (sexp (\ s ->
                          minus_set (signalLamps st)
                            (lens_get current_state s))))))
            (assigns
              (subst_upd subst_id last_state (sexp (lens_get current_state)))))
          (assigns
            (subst_upd subst_id desired_proper_state (sexp (\ _ -> st))))));

lastProperState :: forall a. Dwarf_ext a -> Itree Chan (Dwarf_ext a);
lastProperState =
  output lastProperStatea (sexp (lens_get last_proper_state)) skip;

un_turnOff_C :: Chan -> LampId;
un_turnOff_C (TurnOff_C x3) = x3;

is_turnOff_C :: Chan -> Bool;
is_turnOff_C (Shine_C x1) = False;
is_turnOff_C (SetNewProperState_C x2) = False;
is_turnOff_C (TurnOff_C x3) = True;
is_turnOff_C (TurnOn_C x4) = False;
is_turnOff_C (LastProperState_C x5) = False;

turnOffa :: Prism_ext LampId Chan ();
turnOffa = ctor_prism TurnOff_C is_turnOff_C un_turnOff_C;

turnOff :: forall a. Dwarf_ext a -> Itree Chan (Dwarf_ext a);
turnOff =
  input_in turnOffa (sexp (lens_get turn_off))
    (\ l ->
      kleisli_comp bind_itree
        (kleisli_comp bind_itree
          (kleisli_comp bind_itree
            (assigns
              (subst_upd subst_id turn_off
                (sexp (\ s -> remove l (lens_get turn_off s)))))
            (assigns
              (subst_upd subst_id turn_on
                (sexp (\ s -> remove l (lens_get turn_on s))))))
          (assigns
            (subst_upd subst_id last_state (sexp (lens_get current_state)))))
        (assigns
          (subst_upd subst_id current_state
            (sexp (\ s -> remove l (lens_get current_state s))))));

un_turnOn_C :: Chan -> LampId;
un_turnOn_C (TurnOn_C x4) = x4;

is_turnOn_C :: Chan -> Bool;
is_turnOn_C (Shine_C x1) = False;
is_turnOn_C (SetNewProperState_C x2) = False;
is_turnOn_C (TurnOff_C x3) = False;
is_turnOn_C (TurnOn_C x4) = True;
is_turnOn_C (LastProperState_C x5) = False;

turnOna :: Prism_ext LampId Chan ();
turnOna = ctor_prism TurnOn_C is_turnOn_C un_turnOn_C;

turnOn :: forall a. Dwarf_ext a -> Itree Chan (Dwarf_ext a);
turnOn =
  kleisli_comp bind_itree
    (test (sexp (\ s -> equal_set (lens_get turn_off s) bot_set)))
    (input_in turnOna (sexp (lens_get turn_on))
      (\ l ->
        kleisli_comp bind_itree
          (kleisli_comp bind_itree
            (kleisli_comp bind_itree
              (assigns
                (subst_upd subst_id turn_off
                  (sexp (\ s -> remove l (lens_get turn_off s)))))
              (assigns
                (subst_upd subst_id turn_on
                  (sexp (\ s -> remove l (lens_get turn_on s))))))
            (assigns
              (subst_upd subst_id last_state (sexp (lens_get current_state)))))
          (assigns
            (subst_upd subst_id current_state
              (sexp (\ s ->
                      sup_set (lens_get current_state s)
                        (insert l bot_set)))))));

un_shine_C :: Chan -> Set LampId;
un_shine_C (Shine_C x1) = x1;

is_shine_C :: Chan -> Bool;
is_shine_C (Shine_C x1) = True;
is_shine_C (SetNewProperState_C x2) = False;
is_shine_C (TurnOff_C x3) = False;
is_shine_C (TurnOn_C x4) = False;
is_shine_C (LastProperState_C x5) = False;

shinea :: Prism_ext (Set LampId) Chan ();
shinea = ctor_prism Shine_C is_shine_C un_shine_C;

shine :: forall a. Dwarf_ext a -> Itree Chan (Dwarf_ext a);
shine = output shinea (sexp (lens_get current_state)) skip;

dwarf :: Itree Chan ();
dwarf =
  proc init
    (while (\ _ -> True)
      (extchoice_fun
        (extchoice_fun
          (extchoice_fun (extchoice_fun setNewProperState turnOn) turnOff)
          shine)
        lastProperState));

dwarf_safe :: Itree Chan ();
dwarf_safe =
  gpar_csp dwarf
    (Set (map LastProperState_C [Dark, Stop, Warning, Drive] ++
           map SetNewProperState_C [Dark, Stop, Warning, Drive]))
    ctrl;

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
  do { Prelude.putStrLn ("Events:" ++ Prelude.concat (map (\(n, e) -> " (" ++ Prelude.show n ++ ") " ++ e ++ ";") (zip [1..] (map (Prelude.show . fst) m))));
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