{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module AList(restrict) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Product_Type;
import qualified Set;

restrict :: forall a b. (Eq a) => Set.Set a -> [(a, b)] -> [(a, b)];
restrict a = filter (\ (k, _) -> Set.member k a);

}
