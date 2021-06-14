{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Fib(Chan(..), equal_chan, FibState_ext(..), equal_FibState_ext, y_v, x_v,
       extend, make, default_FibState_ext, y_v_update, y, x_v_update, x,
       un_out_C, out, initFib, outFib, init, fib)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Channel_Type;
import qualified Prisms;
import qualified Substitutions;
import qualified Expressions;
import qualified Lens_Laws;
import qualified ITree_Deadlock;
import qualified ITree_Divergence;
import qualified ITree_Circus;
import qualified Interaction_Trees;
import qualified ITree_CSP;
import qualified Product_Type;
import qualified Arith;
import qualified HOL;

newtype Chan = Out_C Arith.Nat deriving (Prelude.Read, Prelude.Show);

equal_chan :: Chan -> Chan -> Bool;
equal_chan (Out_C x) (Out_C ya) = Arith.equal_nat x ya;

instance Eq Chan where {
  a == b = equal_chan a b;
};

data FibState_ext a = FibState_ext Arith.Nat Arith.Nat a
  deriving (Prelude.Read, Prelude.Show);

equal_FibState_ext ::
  forall a. (Eq a) => FibState_ext a -> FibState_ext a -> Bool;
equal_FibState_ext (FibState_ext x_va y_va morea) (FibState_ext x_v y_v more) =
  Arith.equal_nat x_va x_v && Arith.equal_nat y_va y_v && morea == more;

instance (Eq a) => Eq (FibState_ext a) where {
  a == b = equal_FibState_ext a b;
};

y_v :: forall a. FibState_ext a -> Arith.Nat;
y_v (FibState_ext x_v y_v more) = y_v;

x_v :: forall a. FibState_ext a -> Arith.Nat;
x_v (FibState_ext x_v y_v more) = x_v;

extend :: forall a. FibState_ext () -> a -> FibState_ext a;
extend r more = FibState_ext (x_v r) (y_v r) more;

make :: Arith.Nat -> Arith.Nat -> FibState_ext ();
make x_v y_v = FibState_ext x_v y_v ();

default_FibState_ext :: forall a. (HOL.Default a) => FibState_ext a;
default_FibState_ext = extend (make Arith.Zero_nat Arith.Zero_nat) HOL.defaulta;

instance (HOL.Default a) => HOL.Default (FibState_ext a) where {
  defaulta = default_FibState_ext;
};

y_v_update ::
  forall a. (Arith.Nat -> Arith.Nat) -> FibState_ext a -> FibState_ext a;
y_v_update y_va (FibState_ext x_v y_v more) = FibState_ext x_v (y_va y_v) more;

y :: forall a. Lens_Laws.Lens_ext Arith.Nat (FibState_ext a) ();
y = Lens_Laws.Lens_ext y_v (\ sigma u -> y_v_update (\ _ -> u) sigma) ();

x_v_update ::
  forall a. (Arith.Nat -> Arith.Nat) -> FibState_ext a -> FibState_ext a;
x_v_update x_va (FibState_ext x_v y_v more) = FibState_ext (x_va x_v) y_v more;

x :: forall a. Lens_Laws.Lens_ext Arith.Nat (FibState_ext a) ();
x = Lens_Laws.Lens_ext x_v (\ sigma u -> x_v_update (\ _ -> u) sigma) ();

un_out_C :: Chan -> Arith.Nat;
un_out_C (Out_C x) = x;

out :: Prisms.Prism_ext Arith.Nat Chan ();
out = Channel_Type.ctor_prism Out_C (\ _ -> True) un_out_C;

initFib ::
  forall a. FibState_ext a -> Interaction_Trees.Itree Chan (FibState_ext a);
initFib =
  ITree_Circus.output out (Expressions.sexp (\ _ -> Arith.one_nat))
    (ITree_Circus.output out (Expressions.sexp (\ _ -> Arith.one_nat))
      (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
        (ITree_Circus.assigns
          (Substitutions.subst_upd Substitutions.subst_id x
            (Expressions.sexp (\ _ -> Arith.one_nat))))
        (ITree_Circus.assigns
          (Substitutions.subst_upd Substitutions.subst_id y
            (Expressions.sexp (\ _ -> Arith.one_nat))))));

outFib ::
  forall a. FibState_ext a -> Interaction_Trees.Itree Chan (FibState_ext a);
outFib =
  ITree_Circus.output out
    (Expressions.sexp
      (\ s -> Arith.plus_nat (Lens_Laws.lens_get x s) (Lens_Laws.lens_get y s)))
    (ITree_Circus.assigns
      (Substitutions.subst_upd
        (Substitutions.subst_upd Substitutions.subst_id x
          (Expressions.sexp (Lens_Laws.lens_get y)))
        y (Expressions.sexp
            (\ s ->
              Arith.plus_nat (Lens_Laws.lens_get x s)
                (Lens_Laws.lens_get y s)))));

init :: FibState_ext () -> FibState_ext ();
init =
  Substitutions.subst_upd
    (Substitutions.subst_upd Substitutions.subst_id x
      (Expressions.sexp (\ _ -> Arith.Zero_nat)))
    y (Expressions.sexp (\ _ -> Arith.Zero_nat));

fib :: Interaction_Trees.Itree Chan ();
fib = ITree_Circus.proc init
        (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree initFib
          (ITree_Divergence.while (\ _ -> True)
            (ITree_Circus.extchoice_fun outFib
              (\ _ -> ITree_Deadlock.deadlock))));

}
