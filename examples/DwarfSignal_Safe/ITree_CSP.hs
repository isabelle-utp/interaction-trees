{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ITree_CSP(Extchoice(..), hide, outp, inp_in, gpar_csp) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified List;
import qualified Option;
import qualified Prisms;
import qualified ITree_Deadlock;
import qualified Finite_Set;
import qualified Arith;
import qualified Product_Type;
import qualified Partial_Fun;
import qualified Set;
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

data Andor a b = Left a | Right b | Both (a, b)
  deriving (Prelude.Read, Prelude.Show);

emerge ::
  forall a b c.
    (Eq a) => Partial_Fun.Pfun a b ->
                Set.Set a ->
                  Partial_Fun.Pfun a c -> Partial_Fun.Pfun a (Andor b c);
emerge f a g =
  Partial_Fun.plus_pfun
    (Partial_Fun.plus_pfun
      (Partial_Fun.map_pfun Both
        (Partial_Fun.pdom_res a (Partial_Fun.pfuse f g)))
      (Partial_Fun.map_pfun Left
        (Partial_Fun.pdom_res
          (Set.uminus_set (Set.sup_set a (Partial_Fun.pdom g))) f)))
    (Partial_Fun.map_pfun Right
      (Partial_Fun.pdom_res
        (Set.uminus_set (Set.sup_set a (Partial_Fun.pdom f))) g));

par ::
  forall a b c.
    (Eq a) => Interaction_Trees.Itree a b ->
                Set.Set a ->
                  Interaction_Trees.Itree a c ->
                    Interaction_Trees.Itree a (b, c);
par p a q =
  (case (p, q) of {
    (Interaction_Trees.Ret r, Interaction_Trees.Ret y) ->
      Interaction_Trees.Ret (r, y);
    (Interaction_Trees.Ret _, Interaction_Trees.Sil qa) ->
      Interaction_Trees.Sil (par p a qa);
    (Interaction_Trees.Ret r, Interaction_Trees.Vis g) ->
      Interaction_Trees.Vis
        (Partial_Fun.map_pfun (par (Interaction_Trees.Ret r) a)
          (Partial_Fun.pdom_res (Set.uminus_set a) g));
    (Interaction_Trees.Sil pa, _) -> Interaction_Trees.Sil (par pa a q);
    (Interaction_Trees.Vis pfun, Interaction_Trees.Ret v) ->
      Interaction_Trees.Vis
        (Partial_Fun.map_pfun (\ pa -> par pa a (Interaction_Trees.Ret v))
          (Partial_Fun.pdom_res (Set.uminus_set a) pfun));
    (Interaction_Trees.Vis _, Interaction_Trees.Sil qa) ->
      Interaction_Trees.Sil (par p a qa);
    (Interaction_Trees.Vis pfun, Interaction_Trees.Vis g) ->
      Interaction_Trees.Vis
        (Partial_Fun.map_pfun (\ b -> (case b of {
Left pa -> par pa a q;
Right ba -> par p a ba;
Both ba -> (case ba of {
             (pa, bb) -> par pa a bb;
           });
                                      }))
          (emerge pfun a g));
  });

hide ::
  forall a b.
    (Eq a) => Interaction_Trees.Itree a b ->
                Set.Set a -> Interaction_Trees.Itree a b;
hide p a =
  (case p of {
    Interaction_Trees.Ret aa -> Interaction_Trees.Ret aa;
    Interaction_Trees.Sil pa -> Interaction_Trees.Sil (hide pa a);
    Interaction_Trees.Vis f ->
      (if Arith.equal_nat (Finite_Set.card (Set.inf_set a (Partial_Fun.pdom f)))
            Arith.one_nat
        then Interaction_Trees.Sil
               (hide (Partial_Fun.pfun_app f
                       (Set.the_elem (Set.inf_set a (Partial_Fun.pdom f))))
                 a)
        else (if Set.is_empty (Set.inf_set a (Partial_Fun.pdom f))
               then Interaction_Trees.Vis
                      (Partial_Fun.map_pfun (\ x -> hide x a) f)
               else ITree_Deadlock.deadlock));
  });

outp ::
  forall a b. Prisms.Prism_ext a b () -> a -> Interaction_Trees.Itree b ();
outp c v =
  Interaction_Trees.Vis
    (Partial_Fun.Pfun_of_alist
      [(Prisms.prism_build c v, Interaction_Trees.Ret ())]);

inp_list ::
  forall a b. Prisms.Prism_ext a b () -> [a] -> Interaction_Trees.Itree b a;
inp_list c b =
  Interaction_Trees.Vis
    (Partial_Fun.Pfun_of_alist
      (List.map_filter
        (\ x ->
          (if not (Option.is_none
                    (Prisms.prism_match c (Prisms.prism_build c x)))
            then Just (Prisms.prism_build c x,
                        Interaction_Trees.Ret
                          (Option.the
                            (Prisms.prism_match c (Prisms.prism_build c x))))
            else Nothing))
        b));

inp_in ::
  forall a b.
    Prisms.Prism_ext a b () -> Set.Set a -> Interaction_Trees.Itree b a;
inp_in c (Set.Set b) = inp_list c b;

gpar_csp ::
  forall a b c.
    (Eq a) => Interaction_Trees.Itree a b ->
                Set.Set a ->
                  Interaction_Trees.Itree a c -> Interaction_Trees.Itree a ();
gpar_csp p cs q =
  Interaction_Trees.bind_itree (par p cs q)
    (\ (_, _) -> Interaction_Trees.Ret ());

}
