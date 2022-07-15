require import AllCore DBool Bool List Distr Int Aux DJoin Permutation.
require  GenericSigmaProtocol.


require CommitmentSpecial.
clone include CommitmentSpecial with type message <- bool.


type graph = bool list.         (* n * n list representin n x n matrix *)

type hc_prob = (int * graph).
type hc_wit  = int list.
type hc_com  = commitment list.
type hc_resp = (permutation * (opening list) , hc_wit * (opening list)) sum.

op compl_graph     : int -> graph.
op compl_graph_cyc : int -> int list = range 0.

op permute_graph (p : permutation) (g : graph) : graph.
op permute_witness : permutation -> hc_wit -> hc_wit = map.

(* projects the witness up-fron
   prj (1,2,3) [x11 x12 x13 x21 x22 x23 x31 x32 x33]

    project out the positions of the cycle (1,2)(2,3)(3,1)
           [x12 x23 x31] ++ [x11 x13 x21 x22 x32 x33]
*)
op prj  : hc_wit -> permutation.


op hc_align ['a] (w : hc_wit) (l : 'a list) : 'a list
 = ip (prj w) l.


op hc_verify (p : hc_prob) (c : hc_com) (b : bool)  (r : hc_resp) : bool =
 with r = (Left x) => b /\ all Ver (zip (permute_graph x.`1 p.`2) (zip c x.`2))
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


clone export GenericSigmaProtocol as BlumProtocol with 
  type statement       <- hc_prob,
  type commitment      <- hc_com,  
  type witness         <- hc_wit,
  type response        <- hc_resp,
  type challenge       <- bool,
  op challenge_set     <=  (false :: true :: []),
  op verify_transcript <= fun p (x : transcript) => hc_verify p x.`1 x.`2 x.`3,
  op soundness_relation    <= fun x y => IsHC (x, y),
  op completeness_relation <= fun x y => IsHC (x, y),
  op zk_relation           <= fun x y => IsHC (x, y).
 

require Djoinmap.
clone import Djoinmap as DJMM with type a <- bool, 
                                   type b <- commitment * opening,
                                   op   d <- Com.

op HasHC (Ny : hc_prob) = exists w, IsHC (Ny, w).





axiom permute_graph_prop1 p n  : 
 permute_graph p (compl_graph n) = (compl_graph n).

axiom permute_graph_prop4  (g : graph) (p : permutation) : 
 permute_graph (inv p) (permute_graph p g) = g.

axiom permute_graph_prop2 p g : size (permute_graph p g) = size g.

axiom permute_graph_prop3 n g perm w : 
 IsHC ((n,g), w) = IsHC ((n, permute_graph perm g), permute_witness perm w).

axiom prj_lemma (g : graph) (w : hc_wit) (perm : permutation) : 
  take (size w) (ip (prj w) g) 
  = take (size w) (ip (prj (permute_witness perm w)) (permute_graph perm g)).

axiom compl_graph_prop n : 0 <= n => IsHC ((n, compl_graph n), compl_graph_cyc n).

axiom ishc_prop1 a : IsHC a =>
 (fst (fst a)) = size (snd a) 
    /\ size (snd (fst a)) 
         = (fst (fst a)) * (fst (fst a)).

axiom ishc_prop2 a : IsHC a => 0 < fst (fst a).

axiom ishc_prop3 a n g w : IsHC a => a = ((n,g),w) =>
  take n (ip (prj w) g) = nseq n true.

axiom ishc_prop4 a : IsHC a =>
  uniq a.`2 /\ (forall (i : int), i \in a.`2 => 0 <= i && i < a.`1.`1).

axiom kjk prm n w : prm \in perm_d n =>
 uniq w => (forall i, i \in w => 0 <= i < n) =>
  size w = n => uniq (permute_witness prm w).




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
    fal   <- permute_graph prm g;
    pi_gwco <@ DJM.main5(fal);

    return map fst pi_gwco;
  }
  
  proc response(b : bool) : hc_resp = {
    pi_w <- permute_witness prm w;
    return if b then Left (prm, map snd pi_gwco) 
                else Right (pi_w, 
                        map snd (take n (ip (prj pi_w) pi_gwco)));
 } 
}.