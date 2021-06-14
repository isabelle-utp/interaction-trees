{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Substitutions(subst_id, subst_upd) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Lens_Laws;

subst_id :: forall a. a -> a;
subst_id = (\ s -> s);

subst_upd ::
  forall a b c. (a -> b) -> Lens_Laws.Lens_ext c b () -> (a -> c) -> a -> b;
subst_upd sigma x e = (\ s -> Lens_Laws.lens_put x (sigma s) (e s));

}
