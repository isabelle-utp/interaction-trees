{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Set(Set(..), insert, member, remove, is_empty, the_elem, bot_set, inf_set,
       sup_set, equal_set, minus_set, uminus_set)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified List;

data Set a = Set [a] | Coset [a] deriving (Prelude.Read, Prelude.Show);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (List.removeAll x xs);
insert x (Set xs) = Set (List.insert x xs);

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (List.member xs x);
member x (Set xs) = List.member xs x;

remove :: forall a. (Eq a) => a -> Set a -> Set a;
remove x (Coset xs) = Coset (List.insert x xs);
remove x (Set xs) = Set (List.removeAll x xs);

is_empty :: forall a. Set a -> Bool;
is_empty (Set xs) = null xs;

the_elem :: forall a. Set a -> a;
the_elem (Set [x]) = x;

bot_set :: forall a. Set a;
bot_set = Set [];

inf_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
inf_set a (Coset xs) = List.fold remove xs a;
inf_set a (Set xs) = Set (filter (\ x -> member x a) xs);

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);
sup_set (Set xs) a = List.fold insert xs a;

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
less_eq_set (Coset []) (Set []) = False;
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;

equal_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
equal_set a b = less_eq_set a b && less_eq_set b a;

minus_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
minus_set a (Coset xs) = Set (filter (\ x -> member x a) xs);
minus_set a (Set xs) = List.fold remove xs a;

uminus_set :: forall a. Set a -> Set a;
uminus_set (Coset xs) = Set xs;
uminus_set (Set xs) = Coset xs;

}
