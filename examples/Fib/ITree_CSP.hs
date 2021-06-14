{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ITree_CSP(map_prod, extchoice_itree, Extchoice(..), outp) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Product_Type;
import qualified Set;
import qualified Prisms;
import qualified Partial_Fun;
import qualified Interaction_Trees;

map_prod ::
  forall a b.
    (Eq a) => Partial_Fun.Pfun a b ->
                Partial_Fun.Pfun a b -> Partial_Fun.Pfun a b;
map_prod f g =
  Partial_Fun.plus_pfun
    (Partial_Fun.pdom_res (Set.uminus_set (Partial_Fun.pdom g)) f)
    (Partial_Fun.pdom_res (Set.uminus_set (Partial_Fun.pdom f)) g);

extchoice_itree ::
  forall a b.
    (Eq a,
      Eq b) => Interaction_Trees.Itree a b ->
                 Interaction_Trees.Itree a b -> Interaction_Trees.Itree a b;
extchoice_itree p q =
  (case (p, q) of {
    (Interaction_Trees.Ret r, Interaction_Trees.Ret y) ->
      (if r == y then Interaction_Trees.Ret r
        else Interaction_Trees.Vis Partial_Fun.zero_pfun);
    (Interaction_Trees.Ret _, Interaction_Trees.Sil qa) ->
      Interaction_Trees.Sil (extchoice_itree p qa);
    (Interaction_Trees.Ret r, Interaction_Trees.Vis _) ->
      Interaction_Trees.Ret r;
    (Interaction_Trees.Sil pa, _) ->
      Interaction_Trees.Sil (extchoice_itree pa q);
    (Interaction_Trees.Vis _, Interaction_Trees.Ret a) ->
      Interaction_Trees.Ret a;
    (Interaction_Trees.Vis _, Interaction_Trees.Sil qa) ->
      Interaction_Trees.Sil (extchoice_itree p qa);
    (Interaction_Trees.Vis f, Interaction_Trees.Vis g) ->
      Interaction_Trees.Vis (map_prod f g);
  });

class Extchoice a where {
  extchoice :: a -> a -> a;
};

instance (Eq a, Eq b) => Extchoice (Interaction_Trees.Itree a b) where {
  extchoice = extchoice_itree;
};

outp ::
  forall a b. Prisms.Prism_ext a b () -> a -> Interaction_Trees.Itree b ();
outp c v =
  Interaction_Trees.Vis
    (Partial_Fun.Pfun_of_alist
      [(Prisms.prism_build c v, Interaction_Trees.Ret ())]);

}
