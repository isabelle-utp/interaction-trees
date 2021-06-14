{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Partial_Fun(Pfun(..), pdom, pfun_app, pfuse, pdom_res, map_pfun, plus_pfun,
               zero_pfun)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Product_Type;
import qualified Option;
import qualified List;
import qualified Map;
import qualified AList;
import qualified Set;

data Pfun a b = Pfun_of_alist [(a, b)] | Pfun_of_map (a -> Maybe b);

pdom :: forall a b. Pfun a b -> Set.Set a;
pdom (Pfun_of_alist xs) = Set.Set (map fst xs);

pfun_entries :: forall a b. Set.Set a -> (a -> b) -> Pfun a b;
pfun_entries (Set.Set ks) f = Pfun_of_alist (map (\ k -> (k, f k)) ks);

pfun_app :: forall a b. (Eq a) => Pfun a b -> a -> b;
pfun_app (Pfun_of_alist xs) k =
  (if List.member (map fst xs) k then Option.the (Map.map_of xs k)
    else error "undefined");

pfuse :: forall a b c. (Eq a) => Pfun a b -> Pfun a c -> Pfun a (b, c);
pfuse f g =
  pfun_entries (Set.inf_set (pdom f) (pdom g))
    (\ x -> (pfun_app f x, pfun_app g x));

pdom_res :: forall a b. (Eq a) => Set.Set a -> Pfun a b -> Pfun a b;
pdom_res a (Pfun_of_alist m) = Pfun_of_alist (AList.restrict a m);

map_pfun :: forall a b c. (a -> b) -> Pfun c a -> Pfun c b;
map_pfun f (Pfun_of_alist m) = Pfun_of_alist (map (\ (k, v) -> (k, f v)) m);

plus_pfun :: forall a b. Pfun a b -> Pfun a b -> Pfun a b;
plus_pfun (Pfun_of_alist f) (Pfun_of_alist g) = Pfun_of_alist (g ++ f);

zero_pfun :: forall a b. Pfun a b;
zero_pfun = Pfun_of_alist [];

}
