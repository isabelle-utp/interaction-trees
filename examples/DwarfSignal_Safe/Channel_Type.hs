{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Channel_Type(ctor_prism) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Prisms;

ctor_prism ::
  forall a b. (a -> b) -> (b -> Bool) -> (b -> a) -> Prisms.Prism_ext a b ();
ctor_prism ctor disc sel =
  Prisms.Prism_ext (\ d -> (if disc d then Just (sel d) else Nothing)) ctor ();

}
