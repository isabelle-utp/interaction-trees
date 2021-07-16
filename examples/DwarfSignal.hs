{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module DwarfSignal(Chan, Itree, Dwarf_ext, dwarfSignal) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

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
  | TurnOff_C LampId | TurnOn_C LampId | Violation_C String
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
equal_chan (TurnOn_C x4) (Violation_C x5) = False;
equal_chan (Violation_C x5) (TurnOn_C x4) = False;
equal_chan (TurnOff_C x3) (Violation_C x5) = False;
equal_chan (Violation_C x5) (TurnOff_C x3) = False;
equal_chan (TurnOff_C x3) (TurnOn_C x4) = False;
equal_chan (TurnOn_C x4) (TurnOff_C x3) = False;
equal_chan (SetNewProperState_C x2) (Violation_C x5) = False;
equal_chan (Violation_C x5) (SetNewProperState_C x2) = False;
equal_chan (SetNewProperState_C x2) (TurnOn_C x4) = False;
equal_chan (TurnOn_C x4) (SetNewProperState_C x2) = False;
equal_chan (SetNewProperState_C x2) (TurnOff_C x3) = False;
equal_chan (TurnOff_C x3) (SetNewProperState_C x2) = False;
equal_chan (Shine_C x1) (Violation_C x5) = False;
equal_chan (Violation_C x5) (Shine_C x1) = False;
equal_chan (Shine_C x1) (TurnOn_C x4) = False;
equal_chan (TurnOn_C x4) (Shine_C x1) = False;
equal_chan (Shine_C x1) (TurnOff_C x3) = False;
equal_chan (TurnOff_C x3) (Shine_C x1) = False;
equal_chan (Shine_C x1) (SetNewProperState_C x2) = False;
equal_chan (SetNewProperState_C x2) (Shine_C x1) = False;
equal_chan (Violation_C x5) (Violation_C y5) = x5 == y5;
equal_chan (TurnOn_C x4) (TurnOn_C y4) = equal_LampId x4 y4;
equal_chan (TurnOff_C x3) (TurnOff_C y3) = equal_LampId x3 y3;
equal_chan (SetNewProperState_C x2) (SetNewProperState_C y2) =
  equal_ProperState x2 y2;
equal_chan (Shine_C x1) (Shine_C y1) = equal_set x1 y1;

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

enum_all_LampId :: (LampId -> Bool) -> Bool;
enum_all_LampId = (\ p -> (p L1 && p L2) && p L3);

enum_ex_LampId :: (LampId -> Bool) -> Bool;
enum_ex_LampId = (\ p -> p L1 || p L2 || p L3);

enum_LampId :: [LampId];
enum_LampId = [L1, L2, L3];

class Countable a where {
};

class (Countable a) => Finite a where {
};

class (Finite a) => Enum a where {
  enum :: [a];
  enum_all :: (a -> Bool) -> Bool;
  enum_ex :: (a -> Bool) -> Bool;
};

instance Countable LampId where {
};

instance Finite LampId where {
};

instance Enum LampId where {
  enum = enum_LampId;
  enum_all = enum_all_LampId;
  enum_ex = enum_ex_LampId;
};

instance Eq ProperState where {
  a == b = equal_ProperState a b;
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

uminus_set :: forall a. Set a -> Set a;
uminus_set (Coset xs) = Set xs;
uminus_set (Set xs) = Coset xs;

restrict :: forall a b. (Eq a) => Set a -> [(a, b)] -> [(a, b)];
restrict a = filter (\ (k, _) -> member k a);

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

map_prod :: forall a b. (Eq a) => Pfun a b -> Pfun a b -> Pfun a b;
map_prod (Pfun_of_alist xs) (Pfun_of_alist ys) =
  Pfun_of_alist
    (restrict (uminus_set (image fst (Set xs))) ys ++
      restrict (uminus_set (image fst (Set ys))) xs);
map_prod (Pfun_of_map f) (Pfun_of_map g) =
  Pfun_of_map (\ x -> (case (f x, g x) of {
                        (Nothing, Nothing) -> Nothing;
                        (Nothing, Just a) -> Just a;
                        (Just xa, Nothing) -> Just xa;
                        (Just _, Just _) -> Nothing;
                      }));
map_prod p (Pfun_of_alist []) = p;
map_prod (Pfun_of_alist []) p = p;

extchoice_itree ::
  forall a b. (Eq a, Eq b) => Itree a b -> Itree a b -> Itree a b;
extchoice_itree = genchoice map_prod;

class Extchoice a where {
  extchoice :: a -> a -> a;
};

instance (Eq a, Eq b) => Extchoice (Itree a b) where {
  extchoice = extchoice_itree;
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

default_ProperState :: ProperState;
default_ProperState = Dark;

bot_set :: forall a. Set a;
bot_set = Set [];

default_set :: forall a. Set a;
default_set = bot_set;

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
  extend
    (make default_ProperState default_set default_set default_set default_set
      default_ProperState)
    defaulta;

instance (Default a) => Default (Dwarf_ext a) where {
  defaulta = default_Dwarf_ext;
};

data Prism_ext a b c = Prism_ext (b -> Maybe a) (a -> b) c;

data Lens_ext a b c = Lens_ext (b -> a) (b -> a -> b) c;

ex :: forall a. (Enum a) => (a -> Bool) -> Bool;
ex p = enum_ex p;

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

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

prism_build :: forall a b c. Prism_ext a b c -> a -> b;
prism_build (Prism_ext prism_match prism_build more) = prism_build;

outp :: forall a b. Prism_ext a b () -> a -> Itree b ();
outp c v = Vis (Pfun_of_alist [(prism_build c v, Ret ())]);

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

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

signalLamps :: ProperState -> Set LampId;
signalLamps Dark = bot_set;
signalLamps Stop = insert L1 (insert L2 bot_set);
signalLamps Warning = insert L1 (insert L3 bot_set);
signalLamps Drive = insert L2 (insert L3 bot_set);

subst_id :: forall a. a -> a;
subst_id = (\ s -> s);

sexp :: forall a b. (a -> b) -> a -> b;
sexp x = x;

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

pabs :: forall a b. Set a -> (a -> Bool) -> (a -> b) -> Pfun a b;
pabs (Set xs) p f =
  Pfun_of_alist
    (map_filter (\ x -> (if p x then Just (x, f x) else Nothing)) xs);

lens_get :: forall a b c. Lens_ext a b c -> b -> a;
lens_get (Lens_ext lens_get lens_put more) = lens_get;

un_shine_C :: Chan -> Set LampId;
un_shine_C (Shine_C x1) = x1;

is_shine_C :: Chan -> Bool;
is_shine_C (Shine_C x1) = True;
is_shine_C (SetNewProperState_C x2) = False;
is_shine_C (TurnOff_C x3) = False;
is_shine_C (TurnOn_C x4) = False;
is_shine_C (Violation_C x5) = False;

ctor_prism ::
  forall a b. (a -> b) -> (b -> Bool) -> (b -> a) -> Prism_ext a b ();
ctor_prism ctor disc sel =
  Prism_ext (\ d -> (if disc d then Just (sel d) else Nothing)) ctor ();

shinea :: Prism_ext (Set LampId) Chan ();
shinea = ctor_prism Shine_C is_shine_C un_shine_C;

map_option :: forall a b. (a -> b) -> Maybe a -> Maybe b;
map_option f Nothing = Nothing;
map_option f (Just x2) = Just (f x2);

map_pfun :: forall a b c. (a -> b) -> Pfun c a -> Pfun c b;
map_pfun f (Pfun_of_map g) = Pfun_of_map (\ x -> map_option f (g x));
map_pfun f (Pfun_of_alist m) = Pfun_of_alist (map (\ (k, v) -> (k, f v)) m);

bind_itree :: forall a b c. Itree a b -> (b -> Itree a c) -> Itree a c;
bind_itree (Vis t) k = Vis (map_pfun (\ x -> bind_itree x k) t);
bind_itree (Sil t) k = Sil (bind_itree t k);
bind_itree (Ret v) k = k v;

output ::
  forall a b c.
    Prism_ext a b () -> (c -> a) -> (c -> Itree b c) -> c -> Itree b c;
output c e p = (\ s -> bind_itree (outp c (e s)) (\ _ -> p s));

skip :: forall a b. a -> Itree b a;
skip = Ret;

shine :: forall a. Dwarf_ext a -> Itree Chan (Dwarf_ext a);
shine = output shinea (sexp (lens_get current_state)) skip;

deadlock :: forall a b. Itree a b;
deadlock = Vis zero_pfun;

test :: forall a b. (a -> Bool) -> a -> Itree b a;
test b = (\ s -> (if b s then Ret s else deadlock));

the :: forall a. Maybe a -> a;
the (Just x2) = x2;

kleisli_comp :: forall a b c d. (a -> b -> c) -> (d -> a) -> b -> d -> c;
kleisli_comp bnd f g = (\ x -> bnd (f x) g);

prism_match :: forall a b c. Prism_ext a b c -> b -> Maybe a;
prism_match (Prism_ext prism_match prism_build more) = prism_match;

inp_in_where ::
  forall a b. Prism_ext a b () -> Set a -> (a -> Bool) -> Itree b a;
inp_in_where c a p =
  Vis (pabs (image (prism_build c) a) (\ e -> p (the (prism_match c e)))
        (\ e -> Ret (the (prism_match c e))));

input_in_where ::
  forall a b c.
    Prism_ext a b () ->
      (c -> Set a) -> (a -> (c -> Bool, c -> Itree b c)) -> c -> Itree b c;
input_in_where c a p =
  (\ s ->
    bind_itree (inp_in_where c (a s) (\ v -> fst (p v) s))
      (\ x -> snd (p x) s));

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);
sup_set (Set xs) a = fold insert xs a;

un_turnOn_C :: Chan -> LampId;
un_turnOn_C (TurnOn_C x4) = x4;

is_turnOn_C :: Chan -> Bool;
is_turnOn_C (Shine_C x1) = False;
is_turnOn_C (SetNewProperState_C x2) = False;
is_turnOn_C (TurnOff_C x3) = False;
is_turnOn_C (TurnOn_C x4) = True;
is_turnOn_C (Violation_C x5) = False;

turnOna :: Prism_ext LampId Chan ();
turnOna = ctor_prism TurnOn_C is_turnOn_C un_turnOn_C;

assigns :: forall a b c. (a -> b) -> a -> Itree c b;
assigns sigma = (\ s -> Ret (sigma s));

turnOn :: forall a. Dwarf_ext a -> Itree Chan (Dwarf_ext a);
turnOn =
  input_in_where turnOna (sexp (lens_get turn_on))
    (\ e ->
      (sexp (\ _ -> True),
        kleisli_comp bind_itree
          (kleisli_comp bind_itree
            (kleisli_comp bind_itree
              (assigns
                (subst_upd subst_id turn_off
                  (sexp (\ s -> remove e (lens_get turn_off s)))))
              (assigns
                (subst_upd subst_id turn_on
                  (sexp (\ s -> remove e (lens_get turn_on s))))))
            (assigns
              (subst_upd subst_id last_state (sexp (lens_get current_state)))))
          (assigns
            (subst_upd subst_id current_state
              (sexp (\ s ->
                      sup_set (lens_get current_state s)
                        (insert e bot_set)))))));

un_turnOff_C :: Chan -> LampId;
un_turnOff_C (TurnOff_C x3) = x3;

is_turnOff_C :: Chan -> Bool;
is_turnOff_C (Shine_C x1) = False;
is_turnOff_C (SetNewProperState_C x2) = False;
is_turnOff_C (TurnOff_C x3) = True;
is_turnOff_C (TurnOn_C x4) = False;
is_turnOff_C (Violation_C x5) = False;

turnOffa :: Prism_ext LampId Chan ();
turnOffa = ctor_prism TurnOff_C is_turnOff_C un_turnOff_C;

turnOff :: forall a. Dwarf_ext a -> Itree Chan (Dwarf_ext a);
turnOff =
  input_in_where turnOffa (sexp (lens_get turn_off))
    (\ e ->
      (sexp (\ _ -> True),
        kleisli_comp bind_itree
          (kleisli_comp bind_itree
            (kleisli_comp bind_itree
              (assigns
                (subst_upd subst_id turn_off
                  (sexp (\ s -> remove e (lens_get turn_off s)))))
              (assigns
                (subst_upd subst_id turn_on
                  (sexp (\ s -> remove e (lens_get turn_on s))))))
            (assigns
              (subst_upd subst_id last_state (sexp (lens_get current_state)))))
          (assigns
            (subst_upd subst_id current_state
              (sexp (\ s -> remove e (lens_get current_state s)))))));

extchoice_fun :: forall a b. (Extchoice b) => (a -> b) -> (a -> b) -> a -> b;
extchoice_fun p q = (\ s -> extchoice (p s) (q s));

minus_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
minus_set a (Coset xs) = Set (filter (\ x -> member x a) xs);
minus_set a (Set xs) = fold remove xs a;

inf_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
inf_set a (Coset xs) = fold remove xs a;
inf_set a (Set xs) = Set (filter (\ x -> member x a) xs);

dwarf_inv :: forall a. Dwarf_ext a -> Bool;
dwarf_inv =
  sexp (\ s ->
         equal_set
           (sup_set (minus_set (lens_get current_state s) (lens_get turn_off s))
             (lens_get turn_on s))
           (signalLamps (lens_get desired_proper_state s)) &&
           equal_set (inf_set (lens_get turn_on s) (lens_get turn_off s))
             bot_set);

forbidStopToDrive :: Dwarf_ext () -> Bool;
forbidStopToDrive =
  sexp (\ s ->
         dwarf_inv s &&
           (if equal_ProperState (lens_get last_proper_state s) Stop
             then not (equal_ProperState (lens_get desired_proper_state s)
                        Drive)
             else True));

maxOneLampChange :: Dwarf_ext () -> Bool;
maxOneLampChange =
  sexp (\ s ->
         dwarf_inv s &&
           ex (\ l ->
                equal_set
                  (minus_set (lens_get current_state s) (lens_get last_state s))
                  (insert l bot_set) ||
                  (equal_set
                     (minus_set (lens_get last_state s)
                       (lens_get current_state s))
                     (insert l bot_set) ||
                    equal_set (lens_get last_state s)
                      (lens_get current_state s))));

darkOnlyFromStop :: Dwarf_ext () -> Bool;
darkOnlyFromStop =
  sexp (\ s ->
         dwarf_inv s &&
           (if equal_ProperState (lens_get desired_proper_state s) Dark
             then equal_ProperState (lens_get last_proper_state s) Stop
             else True));

un_violation_C :: Chan -> String;
un_violation_C (Violation_C x5) = x5;

is_violation_C :: Chan -> Bool;
is_violation_C (Shine_C x1) = False;
is_violation_C (SetNewProperState_C x2) = False;
is_violation_C (TurnOff_C x3) = False;
is_violation_C (TurnOn_C x4) = False;
is_violation_C (Violation_C x5) = True;

violation :: Prism_ext String Chan ();
violation = ctor_prism Violation_C is_violation_C un_violation_C;

darkOnlyToStop :: Dwarf_ext () -> Bool;
darkOnlyToStop =
  sexp (\ s ->
         dwarf_inv s &&
           (if equal_ProperState (lens_get last_proper_state s) Dark
             then equal_ProperState (lens_get desired_proper_state s) Stop
             else True));

neverShowAll :: Dwarf_ext () -> Bool;
neverShowAll =
  sexp (\ s ->
         dwarf_inv s &&
           not (equal_set (lens_get current_state s)
                 (insert L1 (insert L2 (insert L3 bot_set)))));

checkReq :: Dwarf_ext () -> Itree Chan (Dwarf_ext ());
checkReq =
  extchoice_fun
    (extchoice_fun
      (extchoice_fun
        (extchoice_fun
          (kleisli_comp bind_itree (test (sexp (\ s -> not (neverShowAll s))))
            (output violation (sexp (\ _ -> "NeverShowAll")) skip))
          (kleisli_comp bind_itree
            (test (sexp (\ s -> not (maxOneLampChange s))))
            (output violation (sexp (\ _ -> "MaxOneLampChange")) skip)))
        (kleisli_comp bind_itree
          (test (sexp (\ s -> not (forbidStopToDrive s))))
          (output violation (sexp (\ _ -> "ForbidStopToDrive")) skip)))
      (kleisli_comp bind_itree (test (sexp (\ s -> not (darkOnlyToStop s))))
        (output violation (sexp (\ _ -> "DarkOnlyToStop")) skip)))
    (kleisli_comp bind_itree (test (sexp (\ s -> not (darkOnlyFromStop s))))
      (output violation (sexp (\ _ -> "DarkOnlyFromStop")) skip));

process ::
  forall a b c. (Default a) => (a -> a) -> (a -> Itree b c) -> Itree b ();
process i a =
  kleisli_comp bind_itree
    (kleisli_comp bind_itree
      (kleisli_comp bind_itree (assigns (\ _ -> defaulta)) (assigns i)) a)
    (assigns (\ _ -> ())) ();

un_setNewProperState_C :: Chan -> ProperState;
un_setNewProperState_C (SetNewProperState_C x2) = x2;

is_setNewProperState_C :: Chan -> Bool;
is_setNewProperState_C (Shine_C x1) = False;
is_setNewProperState_C (SetNewProperState_C x2) = True;
is_setNewProperState_C (TurnOff_C x3) = False;
is_setNewProperState_C (TurnOn_C x4) = False;
is_setNewProperState_C (Violation_C x5) = False;

setNewProperStatea :: Prism_ext ProperState Chan ();
setNewProperStatea =
  ctor_prism SetNewProperState_C is_setNewProperState_C un_setNewProperState_C;

properState :: Set ProperState;
properState = insert Dark (insert Stop (insert Warning (insert Drive bot_set)));

setNewProperState :: forall a. Dwarf_ext a -> Itree Chan (Dwarf_ext a);
setNewProperState =
  kleisli_comp bind_itree
    (test (sexp (\ s ->
                  equal_set (lens_get current_state s)
                    (signalLamps (lens_get desired_proper_state s)))))
    (input_in_where setNewProperStatea
      (sexp (\ s -> remove (lens_get desired_proper_state s) properState))
      (\ e ->
        (sexp (\ _ -> True),
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
                                (signalLamps e))))))
                (assigns
                  (subst_upd subst_id turn_on
                    (sexp (\ s ->
                            minus_set (signalLamps e)
                              (lens_get current_state s))))))
              (assigns
                (subst_upd subst_id last_state
                  (sexp (lens_get current_state)))))
            (assigns
              (subst_upd subst_id desired_proper_state (sexp (\ _ -> e)))))));

iterate :: forall a b. (a -> Bool) -> (a -> Itree b a) -> a -> Itree b a;
iterate b p s = (if b s then bind_itree (p s) (Sil . iterate b p) else Ret s);

dwarfSignal :: Itree Chan ();
dwarfSignal =
  process init
    (iterate (\ _ -> True)
      (extchoice_fun
        (extchoice_fun
          (extchoice_fun (extchoice_fun checkReq setNewProperState) turnOn)
          turnOff)
        shine));

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
simulate_cnt n t@(Vis (Pfun_of_map f)) = 
  do { Prelude.putStr ("Enter an event:");
       e <- Prelude.getLine;
       case (Prelude.reads e) of
         []       -> do { Prelude.putStrLn "No parse"; simulate_cnt n t } 
         [(v, _)] -> case f v of
                       Nothing -> do { Prelude.putStrLn "Rejected"; simulate_cnt n t }
                       Just t' -> simulate_cnt 0 t'
     };

simulate :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Itree e s -> Prelude.IO ();
simulate = simulate_cnt 0;

}
