{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  DwarfSignal_safe(ProperState, Chan, Dwarf_ext, dwarf, dwarf_safe_nh,
                    dwarf_safe)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Channel_Type;
import qualified Prisms;
import qualified ITree_CSP;
import qualified Expressions;
import qualified Lens_Laws;
import qualified Substitutions;
import qualified ITree_Divergence;
import qualified ITree_Circus;
import qualified Interaction_Trees;
import qualified Product_Type;
import qualified Set;
import qualified HOL;

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

data Chan = Shine_C (Set.Set LampId) | SetNewProperState_C ProperState
  | TurnOff_C LampId | TurnOn_C LampId | LastProperState_C ProperState
  deriving (Prelude.Read, Prelude.Show);

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
equal_chan (Shine_C x1) (Shine_C y1) = Set.equal_set x1 y1;

instance Eq Chan where {
  a == b = equal_chan a b;
};

instance Eq ProperState where {
  a == b = equal_ProperState a b;
};

data Dwarf_ext a =
  Dwarf_ext ProperState (Set.Set LampId) (Set.Set LampId) (Set.Set LampId)
    (Set.Set LampId) ProperState a
  deriving (Prelude.Read, Prelude.Show);

equal_Dwarf_ext :: forall a. (Eq a) => Dwarf_ext a -> Dwarf_ext a -> Bool;
equal_Dwarf_ext
  (Dwarf_ext last_proper_state_va turn_off_va turn_on_va last_state_va
    current_state_va desired_proper_state_va morea)
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = equal_ProperState last_proper_state_va last_proper_state_v &&
      Set.equal_set turn_off_va turn_off_v &&
        Set.equal_set turn_on_va turn_on_v &&
          Set.equal_set last_state_va last_state_v &&
            Set.equal_set current_state_va current_state_v &&
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

current_state_v :: forall a. Dwarf_ext a -> Set.Set LampId;
current_state_v
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = current_state_v;

last_state_v :: forall a. Dwarf_ext a -> Set.Set LampId;
last_state_v
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = last_state_v;

turn_off_v :: forall a. Dwarf_ext a -> Set.Set LampId;
turn_off_v
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = turn_off_v;

turn_on_v :: forall a. Dwarf_ext a -> Set.Set LampId;
turn_on_v
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = turn_on_v;

extend :: forall a. Dwarf_ext () -> a -> Dwarf_ext a;
extend r more =
  Dwarf_ext (last_proper_state_v r) (turn_off_v r) (turn_on_v r)
    (last_state_v r) (current_state_v r) (desired_proper_state_v r) more;

signalLamps :: ProperState -> Set.Set LampId;
signalLamps Dark = Set.bot_set;
signalLamps Stop = Set.insert L1 (Set.insert L2 Set.bot_set);
signalLamps Warning = Set.insert L1 (Set.insert L3 Set.bot_set);
signalLamps Drive = Set.insert L2 (Set.insert L3 Set.bot_set);

make ::
  ProperState ->
    Set.Set LampId ->
      Set.Set LampId ->
        Set.Set LampId -> Set.Set LampId -> ProperState -> Dwarf_ext ();
make last_proper_state_v turn_off_v turn_on_v last_state_v current_state_v
  desired_proper_state_v =
  Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v ();

default_Dwarf_ext :: forall a. (HOL.Default a) => Dwarf_ext a;
default_Dwarf_ext =
  extend
    (make Dark Set.bot_set Set.bot_set (signalLamps Stop) (signalLamps Stop)
      Stop)
    HOL.defaulta;

instance (HOL.Default a) => HOL.Default (Dwarf_ext a) where {
  defaulta = default_Dwarf_ext;
};

un_setNewProperState_C :: Chan -> ProperState;
un_setNewProperState_C (SetNewProperState_C x2) = x2;

is_setNewProperState_C :: Chan -> Bool;
is_setNewProperState_C (Shine_C x1) = False;
is_setNewProperState_C (SetNewProperState_C x2) = True;
is_setNewProperState_C (TurnOff_C x3) = False;
is_setNewProperState_C (TurnOn_C x4) = False;
is_setNewProperState_C (LastProperState_C x5) = False;

setNewProperStatea :: Prisms.Prism_ext ProperState Chan ();
setNewProperStatea =
  Channel_Type.ctor_prism SetNewProperState_C is_setNewProperState_C
    un_setNewProperState_C;

un_lastProperState_C :: Chan -> ProperState;
un_lastProperState_C (LastProperState_C x5) = x5;

is_lastProperState_C :: Chan -> Bool;
is_lastProperState_C (Shine_C x1) = False;
is_lastProperState_C (SetNewProperState_C x2) = False;
is_lastProperState_C (TurnOff_C x3) = False;
is_lastProperState_C (TurnOn_C x4) = False;
is_lastProperState_C (LastProperState_C x5) = True;

lastProperStatea :: Prisms.Prism_ext ProperState Chan ();
lastProperStatea =
  Channel_Type.ctor_prism LastProperState_C is_lastProperState_C
    un_lastProperState_C;

properState :: Set.Set ProperState;
properState =
  Set.insert Dark
    (Set.insert Stop (Set.insert Warning (Set.insert Drive Set.bot_set)));

sP345 :: forall a. (Eq a) => a -> Interaction_Trees.Itree Chan a;
sP345 =
  ITree_Circus.input_in lastProperStatea (Expressions.sexp (\ _ -> properState))
    (\ l ->
      ITree_Circus.extchoice_fun
        (ITree_Circus.extchoice_fun
          (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
            (ITree_Circus.test
              (Expressions.sexp (\ _ -> equal_ProperState l Stop)))
            (ITree_Circus.input_in setNewProperStatea
              (Expressions.sexp (\ _ -> Set.remove Drive properState))
              (\ _ -> ITree_Circus.skip)))
          (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
            (ITree_Circus.test
              (Expressions.sexp (\ _ -> equal_ProperState l Dark)))
            (ITree_Circus.input_in setNewProperStatea
              (Expressions.sexp
                (\ _ -> Set.insert Dark (Set.insert Stop Set.bot_set)))
              (\ _ -> ITree_Circus.skip))))
        (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
          (ITree_Circus.test
            (Expressions.sexp
              (\ _ ->
                not (equal_ProperState l Dark) &&
                  not (equal_ProperState l Stop))))
          (ITree_Circus.input_in setNewProperStatea
            (Expressions.sexp (\ _ -> Set.remove Dark properState))
            (\ _ -> ITree_Circus.skip))));

ctrl :: Interaction_Trees.Itree Chan ();
ctrl =
  (ITree_Circus.proc ::
    (Dwarf_ext () -> Dwarf_ext ()) ->
      (Dwarf_ext () -> Interaction_Trees.Itree Chan (Dwarf_ext ())) ->
        Interaction_Trees.Itree Chan ())
    Substitutions.subst_id
    (ITree_Divergence.while (\ _ -> True)
      (sP345 :: Dwarf_ext () -> Interaction_Trees.Itree Chan (Dwarf_ext ())));

desired_proper_state_v_update ::
  forall a. (ProperState -> ProperState) -> Dwarf_ext a -> Dwarf_ext a;
desired_proper_state_v_update desired_proper_state_va
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
      current_state_v (desired_proper_state_va desired_proper_state_v) more;

desired_proper_state ::
  forall a. Lens_Laws.Lens_ext ProperState (Dwarf_ext a) ();
desired_proper_state =
  Lens_Laws.Lens_ext desired_proper_state_v
    (\ sigma u -> desired_proper_state_v_update (\ _ -> u) sigma) ();

last_proper_state_v_update ::
  forall a. (ProperState -> ProperState) -> Dwarf_ext a -> Dwarf_ext a;
last_proper_state_v_update last_proper_state_va
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = Dwarf_ext (last_proper_state_va last_proper_state_v) turn_off_v turn_on_v
      last_state_v current_state_v desired_proper_state_v more;

last_proper_state :: forall a. Lens_Laws.Lens_ext ProperState (Dwarf_ext a) ();
last_proper_state =
  Lens_Laws.Lens_ext last_proper_state_v
    (\ sigma u -> last_proper_state_v_update (\ _ -> u) sigma) ();

current_state_v_update ::
  forall a. (Set.Set LampId -> Set.Set LampId) -> Dwarf_ext a -> Dwarf_ext a;
current_state_v_update current_state_va
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
      (current_state_va current_state_v) desired_proper_state_v more;

current_state :: forall a. Lens_Laws.Lens_ext (Set.Set LampId) (Dwarf_ext a) ();
current_state =
  Lens_Laws.Lens_ext current_state_v
    (\ sigma u -> current_state_v_update (\ _ -> u) sigma) ();

last_state_v_update ::
  forall a. (Set.Set LampId -> Set.Set LampId) -> Dwarf_ext a -> Dwarf_ext a;
last_state_v_update last_state_va
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = Dwarf_ext last_proper_state_v turn_off_v turn_on_v
      (last_state_va last_state_v) current_state_v desired_proper_state_v more;

last_state :: forall a. Lens_Laws.Lens_ext (Set.Set LampId) (Dwarf_ext a) ();
last_state =
  Lens_Laws.Lens_ext last_state_v
    (\ sigma u -> last_state_v_update (\ _ -> u) sigma) ();

turn_off_v_update ::
  forall a. (Set.Set LampId -> Set.Set LampId) -> Dwarf_ext a -> Dwarf_ext a;
turn_off_v_update turn_off_va
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = Dwarf_ext last_proper_state_v (turn_off_va turn_off_v) turn_on_v
      last_state_v current_state_v desired_proper_state_v more;

turn_off :: forall a. Lens_Laws.Lens_ext (Set.Set LampId) (Dwarf_ext a) ();
turn_off =
  Lens_Laws.Lens_ext turn_off_v
    (\ sigma u -> turn_off_v_update (\ _ -> u) sigma) ();

turn_on_v_update ::
  forall a. (Set.Set LampId -> Set.Set LampId) -> Dwarf_ext a -> Dwarf_ext a;
turn_on_v_update turn_on_va
  (Dwarf_ext last_proper_state_v turn_off_v turn_on_v last_state_v
    current_state_v desired_proper_state_v more)
  = Dwarf_ext last_proper_state_v turn_off_v (turn_on_va turn_on_v) last_state_v
      current_state_v desired_proper_state_v more;

turn_on :: forall a. Lens_Laws.Lens_ext (Set.Set LampId) (Dwarf_ext a) ();
turn_on =
  Lens_Laws.Lens_ext turn_on_v (\ sigma u -> turn_on_v_update (\ _ -> u) sigma)
    ();

init :: Dwarf_ext () -> Dwarf_ext ();
init =
  Substitutions.subst_upd
    (Substitutions.subst_upd
      (Substitutions.subst_upd
        (Substitutions.subst_upd
          (Substitutions.subst_upd
            (Substitutions.subst_upd Substitutions.subst_id last_proper_state
              (Expressions.sexp (\ _ -> Stop)))
            turn_off (Expressions.sexp (\ _ -> Set.bot_set)))
          turn_on (Expressions.sexp (\ _ -> Set.bot_set)))
        last_state (Expressions.sexp (\ _ -> signalLamps Stop)))
      current_state (Expressions.sexp (\ _ -> signalLamps Stop)))
    desired_proper_state (Expressions.sexp (\ _ -> Stop));

setNewProperState ::
  forall a. Dwarf_ext a -> Interaction_Trees.Itree Chan (Dwarf_ext a);
setNewProperState =
  Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
    (ITree_Circus.test
      (Expressions.sexp
        (\ s ->
          Set.equal_set (Lens_Laws.lens_get current_state s)
            (signalLamps (Lens_Laws.lens_get desired_proper_state s)))))
    (ITree_Circus.input_in setNewProperStatea
      (Expressions.sexp
        (\ s ->
          Set.remove (Lens_Laws.lens_get desired_proper_state s) properState))
      (\ st ->
        Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
          (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
            (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
              (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
                (ITree_Circus.assigns
                  (Substitutions.subst_upd Substitutions.subst_id
                    last_proper_state
                    (Expressions.sexp
                      (Lens_Laws.lens_get desired_proper_state))))
                (ITree_Circus.assigns
                  (Substitutions.subst_upd Substitutions.subst_id turn_off
                    (Expressions.sexp
                      (\ s ->
                        Set.minus_set (Lens_Laws.lens_get current_state s)
                          (signalLamps st))))))
              (ITree_Circus.assigns
                (Substitutions.subst_upd Substitutions.subst_id turn_on
                  (Expressions.sexp
                    (\ s ->
                      Set.minus_set (signalLamps st)
                        (Lens_Laws.lens_get current_state s))))))
            (ITree_Circus.assigns
              (Substitutions.subst_upd Substitutions.subst_id last_state
                (Expressions.sexp (Lens_Laws.lens_get current_state)))))
          (ITree_Circus.assigns
            (Substitutions.subst_upd Substitutions.subst_id desired_proper_state
              (Expressions.sexp (\ _ -> st))))));

lastProperState ::
  forall a. Dwarf_ext a -> Interaction_Trees.Itree Chan (Dwarf_ext a);
lastProperState =
  Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
    (ITree_Circus.test
      (Expressions.sexp
        (\ s ->
          Set.equal_set (Lens_Laws.lens_get current_state s)
            (signalLamps (Lens_Laws.lens_get desired_proper_state s)))))
    (ITree_Circus.output lastProperStatea
      (Expressions.sexp (Lens_Laws.lens_get desired_proper_state))
      ITree_Circus.skip);

un_turnOff_C :: Chan -> LampId;
un_turnOff_C (TurnOff_C x3) = x3;

is_turnOff_C :: Chan -> Bool;
is_turnOff_C (Shine_C x1) = False;
is_turnOff_C (SetNewProperState_C x2) = False;
is_turnOff_C (TurnOff_C x3) = True;
is_turnOff_C (TurnOn_C x4) = False;
is_turnOff_C (LastProperState_C x5) = False;

turnOffa :: Prisms.Prism_ext LampId Chan ();
turnOffa = Channel_Type.ctor_prism TurnOff_C is_turnOff_C un_turnOff_C;

turnOff :: forall a. Dwarf_ext a -> Interaction_Trees.Itree Chan (Dwarf_ext a);
turnOff =
  ITree_Circus.input_in turnOffa
    (Expressions.sexp (Lens_Laws.lens_get turn_off))
    (\ l ->
      Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
        (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
          (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
            (ITree_Circus.assigns
              (Substitutions.subst_upd Substitutions.subst_id turn_off
                (Expressions.sexp
                  (\ s -> Set.remove l (Lens_Laws.lens_get turn_off s)))))
            (ITree_Circus.assigns
              (Substitutions.subst_upd Substitutions.subst_id turn_on
                (Expressions.sexp
                  (\ s -> Set.remove l (Lens_Laws.lens_get turn_on s))))))
          (ITree_Circus.assigns
            (Substitutions.subst_upd Substitutions.subst_id last_state
              (Expressions.sexp (Lens_Laws.lens_get current_state)))))
        (ITree_Circus.assigns
          (Substitutions.subst_upd Substitutions.subst_id current_state
            (Expressions.sexp
              (\ s -> Set.remove l (Lens_Laws.lens_get current_state s))))));

un_turnOn_C :: Chan -> LampId;
un_turnOn_C (TurnOn_C x4) = x4;

is_turnOn_C :: Chan -> Bool;
is_turnOn_C (Shine_C x1) = False;
is_turnOn_C (SetNewProperState_C x2) = False;
is_turnOn_C (TurnOff_C x3) = False;
is_turnOn_C (TurnOn_C x4) = True;
is_turnOn_C (LastProperState_C x5) = False;

turnOna :: Prisms.Prism_ext LampId Chan ();
turnOna = Channel_Type.ctor_prism TurnOn_C is_turnOn_C un_turnOn_C;

turnOn :: forall a. Dwarf_ext a -> Interaction_Trees.Itree Chan (Dwarf_ext a);
turnOn =
  Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
    (ITree_Circus.test
      (Expressions.sexp
        (\ s -> Set.equal_set (Lens_Laws.lens_get turn_off s) Set.bot_set)))
    (ITree_Circus.input_in turnOna
      (Expressions.sexp (Lens_Laws.lens_get turn_on))
      (\ l ->
        Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
          (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
            (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
              (ITree_Circus.assigns
                (Substitutions.subst_upd Substitutions.subst_id turn_off
                  (Expressions.sexp
                    (\ s -> Set.remove l (Lens_Laws.lens_get turn_off s)))))
              (ITree_Circus.assigns
                (Substitutions.subst_upd Substitutions.subst_id turn_on
                  (Expressions.sexp
                    (\ s -> Set.remove l (Lens_Laws.lens_get turn_on s))))))
            (ITree_Circus.assigns
              (Substitutions.subst_upd Substitutions.subst_id last_state
                (Expressions.sexp (Lens_Laws.lens_get current_state)))))
          (ITree_Circus.assigns
            (Substitutions.subst_upd Substitutions.subst_id current_state
              (Expressions.sexp
                (\ s ->
                  Set.sup_set (Lens_Laws.lens_get current_state s)
                    (Set.insert l Set.bot_set)))))));

un_shine_C :: Chan -> Set.Set LampId;
un_shine_C (Shine_C x1) = x1;

is_shine_C :: Chan -> Bool;
is_shine_C (Shine_C x1) = True;
is_shine_C (SetNewProperState_C x2) = False;
is_shine_C (TurnOff_C x3) = False;
is_shine_C (TurnOn_C x4) = False;
is_shine_C (LastProperState_C x5) = False;

shinea :: Prisms.Prism_ext (Set.Set LampId) Chan ();
shinea = Channel_Type.ctor_prism Shine_C is_shine_C un_shine_C;

shine :: forall a. Dwarf_ext a -> Interaction_Trees.Itree Chan (Dwarf_ext a);
shine =
  ITree_Circus.output shinea
    (Expressions.sexp (Lens_Laws.lens_get current_state)) ITree_Circus.skip;

dwarf :: Interaction_Trees.Itree Chan ();
dwarf =
  ITree_Circus.proc init
    (ITree_Divergence.while (\ _ -> True)
      (ITree_Circus.extchoice_fun
        (ITree_Circus.extchoice_fun
          (ITree_Circus.extchoice_fun
            (ITree_Circus.extchoice_fun setNewProperState turnOn) turnOff)
          shine)
        lastProperState));

dwarf_safe_nh :: Interaction_Trees.Itree Chan ();
dwarf_safe_nh =
  ITree_CSP.gpar_csp dwarf
    (Set.Set
      (map LastProperState_C [Dark, Stop, Warning, Drive] ++
        map SetNewProperState_C [Dark, Stop, Warning, Drive]))
    ctrl;

dwarf_safe :: Interaction_Trees.Itree Chan ();
dwarf_safe =
  ITree_CSP.hide dwarf_safe_nh
    (Set.Set (map LastProperState_C [Dark, Stop, Warning, Drive]));

}
