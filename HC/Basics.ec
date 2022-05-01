require import AllCore DBool Bool List Distr Int Aux DJoin Permutation.
require import Generic_Defs_thy.

type sbits.

require CommitmentSpecial.
clone include CommitmentSpecial with type message <- bool.


type graph = bool list.         (* n * n list representin n x n matrix *)

type hc_prob = (int * graph).
type hc_wit  = int list.
type hc_com  = commitment list.
type hc_resp = (permutation * (opening list) , hc_wit * (opening list)) sum.

op compl_graph     : int -> graph.
op compl_graph_cyc : int -> int list = range 0.

(* flatten and permute  *)
op fap (p : permutation) (g : graph) : bool list.
op prj  : hc_wit -> permutation.


op hc_align ['a] (w : hc_wit) (l : 'a list) : 'a list
 = ip (prj w) l.

axiom fap_prop1 p n  : 
 fap p (compl_graph n) = (compl_graph n).


axiom fap_prop2 p g : size (fap p g) = size g.


op hc_verify (p : hc_prob) (c : hc_com) (b : bool)  (r : hc_resp) : bool =
 with r = (Left x) => b /\ all Ver (zip (fap x.`1 p.`2) (zip c x.`2))
                         /\ size c = p.`1 * p.`1
                         /\ size p.`2 = p.`1 * p.`1
                         /\ size x.`2 = p.`1 * p.`1

 with r = (Right x) => ! b /\ uniq x.`1
                        /\ size x.`1 = p.`1
                        /\ size c = p.`1 * p.`1
                        /\ size x.`2 = p.`1
                        /\ all Ver 
                             (zip (nseq p.`1 true) 
                                    (zip (take p.`1 (hc_align x.`1 c)) x.`2))
                        /\ perm_eq x.`1 (range 0 (p.`1))
                        /\ size p.`2 = p.`1 * p.`1.


op IsHC (x : hc_prob * hc_wit) : bool 
  = let n = x.`1.`1 in
    let g = x.`1.`2 in
    let w = x.`2 in
     n = size w /\ 
     n * n = size g /\ 
     perm_eq w (range 0 n) /\ 
     nseq n true = take n (hc_align w g).

axiom compl_graph_prop n : 0 <= n => IsHC ((n, compl_graph n), compl_graph_cyc n).


clone include ZKProtocol with 
  type statement       <- hc_prob,
  type commitment      <- hc_com,  
  type witness         <- int list,
  type response        <- hc_resp,
  type challenge       <- bool,
  op challenge_set     <-  (false :: true :: []),
  op verify_transcript <- fun p (x : transcript) => hc_verify p x.`1 x.`2 x.`3,
  op soundness_relation    <- fun x y => IsHC (x, y),
  op completeness_relation <- fun x y => IsHC (x, y),
  op zk_relation           <- fun x y => IsHC (x, y).
 

require Djoinmap.
clone import Djoinmap as DJMM with type a <- bool, 
                                   type b <- commitment * opening,
                                   op   d <- Com.

(* projects the witness up-fron
   prj (1,2,3) [x11 x12 x13 x21 x22 x23 x31 x32 x33]

    project out the positions of the cycle (1,2)(2,3)(3,1)
           [x12 x23 x31] ++ [x11 x13 x21 x22 x32 x33]
*)
op HasHC (Ny : hc_prob) = exists w, IsHC (Ny, w).


op permute_wit : permutation -> hc_wit -> hc_wit = map.

axiom fap_prop3 n g perm w : 
 IsHC ((n,g), w) = IsHC ((n, fap perm g), permute_wit perm w).

axiom fap_prop4  (g : graph) (p : permutation) : 
 fap (inv p) (fap p g) = g.

axiom ishc_prop1 a : IsHC a =>
 (fst (fst a)) = size (snd a) 
    /\ size (snd (fst a)) 
         = (fst (fst a)) * (fst (fst a)).

axiom ishc_prop2 a : IsHC a => 0 < fst (fst a).

axiom ishc_prop3 a n g w : IsHC a => a = ((n,g),w) =>
  take n (ip (prj w) g) = nseq n true.

axiom ishc_prop4 a : IsHC a =>
  uniq a.`2 /\ (forall (i : int), i \in a.`2 => 0 <= i && i < a.`1.`1).



module HonestProver : HonestProver  = {
  var n : int                   (* size of the graph *)
  var g : graph                 (* n*n adj. matrix *)
  var prm : permutation         (* uniformly sampled permutation *)
  var w : hc_wit                (* hamiltonian cycle *)
  var fal : bool list           (* flattened and permuted g *)
  var pi_gwco : (commitment * opening) list
  var pi_w : hc_wit
  
  proc commitment(p_a : hc_prob, w_a : hc_wit)  = {
    (n,g) <- p_a;
    w     <- w_a;
    prm   <$ perm_d n;
    fal   <- fap prm g;
    pi_gwco <@ DJM.main5(fal);

    return map fst pi_gwco;
  }
  
  proc response(b : bool) : hc_resp = {
    pi_w <- permute_wit prm w;
    return if b then Left (prm, map snd pi_gwco) 
                else Right (pi_w, 
                        map snd (take n (ip (prj pi_w) pi_gwco)));
 } 
}.
