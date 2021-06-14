{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ITree_Circus(skip, assigns, proc, test, output, input_in, extchoice_fun)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Set;
import qualified ITree_CSP;
import qualified Prisms;
import qualified ITree_Deadlock;
import qualified HOL;
import qualified Interaction_Trees;

skip :: forall a b. a -> Interaction_Trees.Itree b a;
skip = Interaction_Trees.Ret;

assigns :: forall a b c. (a -> b) -> a -> Interaction_Trees.Itree c b;
assigns sigma = (\ s -> Interaction_Trees.Ret (sigma s));

proc ::
  forall a b.
    (HOL.Default a) => (a -> a) ->
                         (a -> Interaction_Trees.Itree b a) ->
                           Interaction_Trees.Itree b ();
proc i a =
  Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
    (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
      (Interaction_Trees.kleisli_comp Interaction_Trees.bind_itree
        (assigns (\ _ -> HOL.defaulta)) (assigns i))
      a)
    (assigns (\ _ -> ())) ();

test :: forall a b. (a -> Bool) -> a -> Interaction_Trees.Itree b a;
test b =
  (\ s -> (if b s then Interaction_Trees.Ret s else ITree_Deadlock.deadlock));

output ::
  forall a b c.
    Prisms.Prism_ext a b () ->
      (c -> a) ->
        (c -> Interaction_Trees.Itree b c) -> c -> Interaction_Trees.Itree b c;
output c e p =
  (\ s -> Interaction_Trees.bind_itree (ITree_CSP.outp c (e s)) (\ _ -> p s));

input_in ::
  forall a b c.
    Prisms.Prism_ext a b () ->
      (c -> Set.Set a) ->
        (a -> c -> Interaction_Trees.Itree b c) ->
          c -> Interaction_Trees.Itree b c;
input_in c a p =
  (\ s ->
    Interaction_Trees.bind_itree (ITree_CSP.inp_in c (a s)) (\ x -> p x s));

extchoice_fun ::
  forall a b. (ITree_CSP.Extchoice b) => (a -> b) -> (a -> b) -> a -> b;
extchoice_fun p q = (\ s -> ITree_CSP.extchoice (p s) (q s));

}
