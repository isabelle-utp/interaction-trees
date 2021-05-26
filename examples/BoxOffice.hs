{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module BoxOffice(Chan, Itree, Set, BoxOffice_ext, boxOffice) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Chan = Purchase_C (Integer, String) | Return_C (Integer, String)
  deriving (Prelude.Read, Prelude.Show);

equal_chan :: Chan -> Chan -> Bool;
equal_chan (Purchase_C x1) (Return_C x2) = False;
equal_chan (Return_C x2) (Purchase_C x1) = False;
equal_chan (Return_C x2) (Return_C y2) = x2 == y2;
equal_chan (Purchase_C x1) (Purchase_C y1) = x1 == y1;

instance Eq Chan where {
  a == b = equal_chan a b;
};

default_unit :: ();
default_unit = ();

class Default a where {
  defaulta :: a;
};

instance Default () where {
  defaulta = default_unit;
};

data Pfun a b = Pfun_of_alist [(a, b)] | Pfun_of_map (a -> Maybe b);

zero_pfun :: forall a b. Pfun a b;
zero_pfun = Pfun_of_alist [];

data Itree a b = Ret b | Sil (Itree a b) | Vis (Pfun a (Itree a b));

plus_pfun :: forall a b. Pfun a b -> Pfun a b -> Pfun a b;
plus_pfun (Pfun_of_alist f) (Pfun_of_alist g) = Pfun_of_alist (g ++ f);

data Set a = Set [a] | Coset [a] deriving (Prelude.Read, Prelude.Show);

uminus_set :: forall a. Set a -> Set a;
uminus_set (Coset xs) = Set xs;
uminus_set (Set xs) = Coset xs;

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

restrict :: forall a b. (Eq a) => Set a -> [(a, b)] -> [(a, b)];
restrict a = filter (\ (k, _) -> member k a);

pdom_res :: forall a b. (Eq a) => Set a -> Pfun a b -> Pfun a b;
pdom_res a (Pfun_of_alist m) = Pfun_of_alist (restrict a m);

pdom :: forall a b. Pfun a b -> Set a;
pdom (Pfun_of_alist xs) = Set (map fst xs);

map_prod :: forall a b. (Eq a) => Pfun a b -> Pfun a b -> Pfun a b;
map_prod f g =
  plus_pfun (pdom_res (uminus_set (pdom g)) f)
    (pdom_res (uminus_set (pdom f)) g);

extchoice_itree ::
  forall a b. (Eq a, Eq b) => Itree a b -> Itree a b -> Itree a b;
extchoice_itree p q =
  (case (p, q) of {
    (Ret r, Ret y) -> (if r == y then Ret r else Vis zero_pfun);
    (Ret _, Sil qa) -> Sil (extchoice_itree p qa);
    (Ret r, Vis _) -> Ret r;
    (Sil pa, _) -> Sil (extchoice_itree pa q);
    (Vis _, Ret a) -> Ret a;
    (Vis _, Sil qa) -> Sil (extchoice_itree p qa);
    (Vis f, Vis g) -> Vis (map_prod f g);
  });

class Extchoice a where {
  extchoice :: a -> a -> a;
};

instance (Eq a, Eq b) => Extchoice (Itree a b) where {
  extchoice = extchoice_itree;
};

map_of :: forall a b. (Eq a) => [(a, b)] -> a -> Maybe b;
map_of ((l, v) : ps) k = (if l == k then Just v else map_of ps k);
map_of [] k = Nothing;

equal_pfun :: forall a b. (Eq a, Eq b) => Pfun a b -> Pfun a b -> Bool;
equal_pfun (Pfun_of_alist xs) (Pfun_of_alist ys) =
  let {
    ks = map fst xs;
    ls = map fst ys;
  } in all (membera ks) ls &&
         all (\ k -> membera ls k && map_of xs k == map_of ys k) ks;

data BoxOffice_ext a = BoxOffice_ext (Set Integer) (Pfun Integer String) a;

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
less_eq_set (Coset []) (Set []) = False;
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;

equal_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
equal_set a b = less_eq_set a b && less_eq_set b a;

equal_BoxOffice_ext ::
  forall a. (Eq a) => BoxOffice_ext a -> BoxOffice_ext a -> Bool;
equal_BoxOffice_ext (BoxOffice_ext seating_va sold_va morea)
  (BoxOffice_ext seating_v sold_v more) =
  equal_set seating_va seating_v && equal_pfun sold_va sold_v && morea == more;

instance (Eq a) => Eq (BoxOffice_ext a) where {
  a == b = equal_BoxOffice_ext a b;
};

seating_v :: forall a. BoxOffice_ext a -> Set Integer;
seating_v (BoxOffice_ext seating_v sold_v more) = seating_v;

sold_v :: forall a. BoxOffice_ext a -> Pfun Integer String;
sold_v (BoxOffice_ext seating_v sold_v more) = sold_v;

extend :: forall a. BoxOffice_ext () -> a -> BoxOffice_ext a;
extend r more = BoxOffice_ext (seating_v r) (sold_v r) more;

bot_set :: forall a. Set a;
bot_set = Set [];

make :: Set Integer -> Pfun Integer String -> BoxOffice_ext ();
make seating_v sold_v = BoxOffice_ext seating_v sold_v ();

default_BoxOffice_ext :: forall a. (Default a) => BoxOffice_ext a;
default_BoxOffice_ext = extend (make bot_set zero_pfun) defaulta;

instance (Default a) => Default (BoxOffice_ext a) where {
  defaulta = default_BoxOffice_ext;
};

data Prism_ext a b c = Prism_ext (b -> Maybe a) (a -> b) c;

data Lens_ext a b c = Lens_ext (b -> a) (b -> a -> b) c;

filtera :: forall a. (a -> Bool) -> Set a -> Set a;
filtera p (Set xs) = Set (filter p xs);

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (removeAll x xs);
insert x (Set xs) = Set (inserta x xs);

delete :: forall a b. (Eq a) => a -> [(a, b)] -> [(a, b)];
delete k = filter (\ (ka, _) -> not (k == ka));

update :: forall a b. (Eq a) => a -> b -> [(a, b)] -> [(a, b)];
update k v [] = [(k, v)];
update k v (p : ps) = (if fst p == k then (k, v) : ps else p : update k v ps);

is_none :: forall a. Maybe a -> Bool;
is_none (Just x) = False;
is_none Nothing = True;

clearjunk :: forall a b. (Eq a) => [(a, b)] -> [(a, b)];
clearjunk [] = [];
clearjunk (p : ps) = p : clearjunk (delete (fst p) ps);

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

sexp :: forall a b. (a -> b) -> a -> b;
sexp x = x;

prism_match :: forall a b c. Prism_ext a b c -> b -> Maybe a;
prism_match (Prism_ext prism_match prism_build more) = prism_match;

prism_build :: forall a b c. Prism_ext a b c -> a -> b;
prism_build (Prism_ext prism_match prism_build more) = prism_build;

the :: forall a. Maybe a -> a;
the (Just x2) = x2;

inp_list :: forall a b. Prism_ext a b () -> [a] -> Itree b a;
inp_list c b =
  Vis (Pfun_of_alist
        (map_filter
          (\ x ->
            (if not (is_none (prism_match c (prism_build c x)))
              then Just (prism_build c x,
                          Ret (the (prism_match c (prism_build c x))))
              else Nothing))
          b));

inp_in :: forall a b. Prism_ext a b () -> Set a -> Itree b a;
inp_in c (Set b) = inp_list c b;

sold_v_update ::
  forall a.
    (Pfun Integer String -> Pfun Integer String) ->
      BoxOffice_ext a -> BoxOffice_ext a;
sold_v_update sold_va (BoxOffice_ext seating_v sold_v more) =
  BoxOffice_ext seating_v (sold_va sold_v) more;

sold :: forall a. Lens_ext (Pfun Integer String) (BoxOffice_ext a) ();
sold = Lens_ext sold_v (\ sigma u -> sold_v_update (\ _ -> u) sigma) ();

lens_put :: forall a b c. Lens_ext a b c -> b -> a -> b;
lens_put (Lens_ext lens_get lens_put more) = lens_put;

subst_upd :: forall a b c. (a -> b) -> Lens_ext c b () -> (a -> c) -> a -> b;
subst_upd sigma x e = (\ s -> lens_put x (sigma s) (e s));

lens_get :: forall a b c. Lens_ext a b c -> b -> a;
lens_get (Lens_ext lens_get lens_put more) = lens_get;

subst_id :: forall a. a -> a;
subst_id = (\ s -> s);

pfun_graph :: forall a b. (Eq a) => Pfun a b -> Set (a, b);
pfun_graph (Pfun_of_alist xs) = Set (clearjunk xs);

map_pfun :: forall a b c. (a -> b) -> Pfun c a -> Pfun c b;
map_pfun f (Pfun_of_alist m) = Pfun_of_alist (map (\ (k, v) -> (k, f v)) m);

bind_itree :: forall a b c. Itree a b -> (b -> Itree a c) -> Itree a c;
bind_itree (Vis t) k = Vis (map_pfun (\ x -> bind_itree x k) t);
bind_itree (Sil t) k = Sil (bind_itree t k);
bind_itree (Ret v) k = k v;

input_in ::
  forall a b c.
    Prism_ext a b () -> (c -> Set a) -> (a -> c -> Itree b c) -> c -> Itree b c;
input_in c a p = (\ s -> bind_itree (inp_in c (a s)) (\ x -> p x s));

is_purchase_C :: Chan -> Bool;
is_purchase_C (Purchase_C x1) = True;
is_purchase_C (Return_C x2) = False;

un_return_C :: Chan -> (Integer, String);
un_return_C (Return_C x2) = x2;

ctor_prism ::
  forall a b. (a -> b) -> (b -> Bool) -> (b -> a) -> Prism_ext a b ();
ctor_prism ctor disc sel =
  Prism_ext (\ d -> (if disc d then Just (sel d) else Nothing)) ctor ();

returna :: Prism_ext (Integer, String) Chan ();
returna = ctor_prism Return_C (not . is_purchase_C) un_return_C;

assigns :: forall a b c. (a -> b) -> a -> Itree c b;
assigns sigma = (\ s -> Ret (sigma s));

return0 ::
  forall a b. a -> b -> BoxOffice_ext () -> Itree Chan (BoxOffice_ext ());
return0 seat customer =
  input_in returna (sexp (\ s -> pfun_graph (lens_get sold s)))
    (\ (s, _) ->
      assigns
        (subst_upd subst_id sold
          (sexp (\ sa ->
                  pdom_res (uminus_set (insert s bot_set))
                    (lens_get sold sa)))));

kleisli_comp :: forall a b c d. (a -> b -> c) -> (d -> a) -> b -> d -> c;
kleisli_comp bnd f g = (\ x -> bnd (f x) g);

proc :: forall a b. (Default a) => (a -> a) -> (a -> Itree b a) -> Itree b ();
proc i a =
  kleisli_comp bind_itree
    (kleisli_comp bind_itree
      (kleisli_comp bind_itree (assigns (\ _ -> defaulta)) (assigns i)) a)
    (assigns (\ _ -> ())) ();

extchoice_fun :: forall a b. (Extchoice b) => (a -> b) -> (a -> b) -> a -> b;
extchoice_fun p q = (\ s -> extchoice (p s) (q s));

seating_v_update ::
  forall a. (Set Integer -> Set Integer) -> BoxOffice_ext a -> BoxOffice_ext a;
seating_v_update seating_va (BoxOffice_ext seating_v sold_v more) =
  BoxOffice_ext (seating_va seating_v) sold_v more;

seating :: forall a. Lens_ext (Set Integer) (BoxOffice_ext a) ();
seating =
  Lens_ext seating_v (\ sigma u -> seating_v_update (\ _ -> u) sigma) ();

boxOfficeInit :: Set Integer -> BoxOffice_ext () -> BoxOffice_ext ();
boxOfficeInit initalloc =
  subst_upd (subst_upd subst_id seating (sexp (\ _ -> initalloc))) sold
    (sexp (\ _ -> zero_pfun));

while :: forall a b. (a -> Bool) -> (a -> Itree b a) -> a -> Itree b a;
while b p s = (if b s then bind_itree (p s) (Sil . while b p) else Ret s);

un_purchase_C :: Chan -> (Integer, String);
un_purchase_C (Purchase_C x1) = x1;

purchase :: Prism_ext (Integer, String) Chan ();
purchase = ctor_prism Purchase_C is_purchase_C un_purchase_C;

product :: forall a b. Set a -> Set b -> Set (a, b);
product (Set xs) (Set ys) = Set (concatMap (\ x -> map (\ a -> (x, a)) ys) xs);

pfun_upd :: forall a b. (Eq a) => Pfun a b -> a -> b -> Pfun a b;
pfun_upd (Pfun_of_alist xs) k v = Pfun_of_alist (update k v xs);

purchase0 ::
  Set Integer ->
    Set String -> BoxOffice_ext () -> Itree Chan (BoxOffice_ext ());
purchase0 seat customer =
  input_in purchase
    (sexp (\ s ->
            product
              (filtera (\ sa -> not (member sa (pdom (lens_get sold s)))) seat)
              customer))
    (\ (s, c) ->
      assigns
        (subst_upd subst_id sold
          (sexp (\ sa ->
                  plus_pfun (lens_get sold sa) (pfun_upd zero_pfun s c)))));

boxOffice :: Set Integer -> Set Integer -> Set String -> Itree Chan ();
boxOffice initalloc seat customer =
  proc (boxOfficeInit initalloc)
    (while (\ _ -> True)
      (extchoice_fun (purchase0 seat customer) (return0 seat customer)));

simulate_cnt :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Prelude.Int -> Itree e s -> Prelude.IO ();
simulate_cnt n (Ret x) = Prelude.putStrLn ("Terminated: " ++ Prelude.show x);
simulate_cnt n (Sil p) = 
  do { if (n == 0) then Prelude.putStrLn "Internal Activity..." else return ();
       if (n >= 20) then do { Prelude.putStr "Many steps (> 20); Continue? [Y/N]"; q <- Prelude.getLine; 
                              if (q == "Y") then simulate_cnt 0 p else Prelude.putStrLn "Ended early.";
                            }
                    else simulate_cnt (n + 1) p
     };
simulate_cnt n (Vis (Pfun_of_alist [])) = Prelude.putStrLn "Deadlocked.";
simulate_cnt n t@(Vis (Pfun_of_alist m)) = 
  do { Prelude.putStrLn ("Events:" ++ Prelude.concat (map (\(n, e) -> " (" ++ Prelude.show n ++ ") " ++ e ++ ";") (zip [1..] (map (Prelude.show . fst) m))));
       e <- Prelude.getLine;
       case (Prelude.reads e) of
         []       -> do { Prelude.putStrLn "No parse"; simulate_cnt n t }
         [(v, _)] -> if (v > Prelude.length m)
                       then do { Prelude.putStrLn "Rejected"; simulate_cnt n t }
                       else simulate_cnt 0 (snd (m !! (v - 1)))
     };

simulate :: (Eq e, Prelude.Show e, Prelude.Read e, Prelude.Show s) => Itree e s -> Prelude.IO ();
simulate = simulate_cnt 0;

}
