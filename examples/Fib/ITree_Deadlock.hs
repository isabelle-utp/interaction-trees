{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ITree_Deadlock(deadlock) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Interaction_Trees;
import qualified Partial_Fun;

deadlock :: forall a b. Interaction_Trees.Itree a b;
deadlock = Interaction_Trees.Vis Partial_Fun.zero_pfun;

}
