{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Partial_Fun(Pfun(..), pdom, pdom_res, map_pfun, plus_pfun, zero_pfun)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Product_Type;
import qualified AList;
import qualified Set;

data Pfun a b = Pfun_of_alist [(a, b)] | Pfun_of_map (a -> Maybe b);

pdom :: forall a b. Pfun a b -> Set.Set a;
pdom (Pfun_of_alist xs) = Set.Set (map fst xs);

pdom_res :: forall a b. (Eq a) => Set.Set a -> Pfun a b -> Pfun a b;
pdom_res a (Pfun_of_alist m) = Pfun_of_alist (AList.restrict a m);

map_pfun :: forall a b c. (a -> b) -> Pfun c a -> Pfun c b;
map_pfun f (Pfun_of_alist m) = Pfun_of_alist (map (\ (k, v) -> (k, f v)) m);

plus_pfun :: forall a b. Pfun a b -> Pfun a b -> Pfun a b;
plus_pfun (Pfun_of_alist f) (Pfun_of_alist g) = Pfun_of_alist (g ++ f);

zero_pfun :: forall a b. Pfun a b;
zero_pfun = Pfun_of_alist [];

}
