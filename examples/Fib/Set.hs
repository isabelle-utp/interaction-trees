{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Set(Set(..), member, uminus_set) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified List;

data Set a = Set [a] | Coset [a] deriving (Prelude.Read, Prelude.Show);

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (List.member xs x);
member x (Set xs) = List.member xs x;

uminus_set :: forall a. Set a -> Set a;
uminus_set (Coset xs) = Set xs;
uminus_set (Set xs) = Coset xs;

}
