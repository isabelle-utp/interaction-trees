structure ITree =
struct

datatype ('a, 'b) pfun =
  pfun_of_map of ('a -> 'b option) |
  pfun_of_alist of ('a * 'b) list;

fun 
  map_pfun f (pfun_of_map g) 
  = pfun_of_map (fn x => case g x of SOME y => SOME (f y) | NONE => NONE) |
  map_pfun f (pfun_of_alist ps)
  = pfun_of_alist (map (fn (k, v) => (k, f v)) ps)

datatype ('e, 'r) itree = 
  Ret of 'r | 
  Sil of (unit -> ('e, 'r) itree) | 
  Vis of (unit -> ('e, ('e, 'r) itree) pfun)

fun 
  itree_bind _ (Ret x) q = q x |
  itree_bind _ (Sil p) q = Sil (fn _ => itree_bind () (p ()) q) |
  itree_bind _ (Vis f) q = Vis (fn _ => map_pfun (fn x => itree_bind () x q) (f ()));
  
fun diverge _ = Sil (fn _ => diverge ());

fun iterate b p s = (if b s then Sil (fn _ => itree_bind () (p s) (iterate b p)) else Ret s);  

end

