{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Product_Type(default_unit) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified HOL;

default_unit :: ();
default_unit = ();

instance HOL.Default () where {
  defaulta = default_unit;
};

}
