pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.

require import Permutation.

type sbits.
type commitment, opening.

op Com  : bool -> (commitment * opening) distr.
op Ver : bool * (commitment * opening)  -> bool.

axiom Com_sound : forall (x : bool * (commitment * opening)), x.`2 \in Com x.`1 => Ver x.

type graph = bool list.         (* n * n list representin n x n matrix *)

type hc_prob = (int * graph).
type hc_wit  = int list.
type hc_com  = commitment list.
type hc_resp = (permutation * (opening list) , hc_wit * (opening list)) sum.

module type Dist = {
   proc run(s : sbits) : bool
}.

require Generic_ZK_old.
clone import Generic_ZK_old as ZK_defs with type prob  = hc_prob,
                                        type wit   = hc_wit,
                                        type chal  = bool,
                                        type com   = hc_com,
                                        type resp  = hc_resp,
                                        type sbits = sbits.


module ZKP(P : Prover, V : Verifier) = {
  proc run(Ny : hc_prob, w : hc_wit, b : bool) = {
    var c,r;
    c <- P.commit(Ny,w);
    r <- P.response(b);
    return (c,r);
  }
}.


module ZKD(P : Prover, V : Verifier, D : Dist) = {
  proc main(Ny : prob, w : wit) = {
    var c,b,r,result,rb;
    c <- P.commit(Ny,w);
    b <- V.challenge(Ny,c);
    r <- P.response(b);
    result <- V.summitup(c,r);
    rb <- D.run(result);
    return rb;
  }
}.

require Djoinmap.
clone import Djoinmap as DJMM with type a <- bool, 
                                   type b <- commitment * opening,
                                   op   d <- Com.
                                        


op compl_graph     : int -> graph.
op compl_graph_cyc : int -> int list = range 0.


(* projects the witness up-fron
   prj (1,2,3) [x11 x12 x13 x21 x22 x23 x31 x32 x33]

    project out the positions of the cycle (1,2)(2,3)(3,1)
           [x12 x23 x31] ++ [x11 x13 x21 x22 x32 x33]
*)

op prj  : hc_wit -> permutation.


op hc_align ['a] (w : hc_wit) (l : 'a list) : 'a list
 = ip (prj w) l.

op IsHC (x : hc_prob * hc_wit) : bool 
  = let n = x.`1.`1 in
    let g = x.`1.`2 in
    let w = x.`2 in
     n = size w /\ 
     n * n = size g /\ 
     perm_eq w (range 0 n) /\ 
     nseq n true = take n (hc_align w g).


op HasHC (Ny : hc_prob) = exists w, IsHC (Ny, w).

axiom ishc_prop1 a : IsHC a =>
 (fst (fst a)) = size (snd a) 
    /\ size ((snd (fst a))) 
         = (fst (fst a)) * (fst (fst a)).


axiom ishc_prop2 a : IsHC a =>
  0 < (fst (fst a)).

axiom ishc_prop3 a n g w : IsHC a => a = ((n,g),w) =>
  take n (ip (prj w) g) = nseq n true.

axiom ishc_prop4 a : IsHC a =>
  uniq a.`2 /\ (forall (i : int), i \in a.`2 => 0 <= i && i < a.`1.`1).



(* flatten and permute  *)
op fap (p : permutation) (g : graph) : bool list.

axiom fap_prop1 p n  : 
 fap p (compl_graph n) = (compl_graph n).

axiom fap_prop2 p g  : 
 size (fap p g) = size (g).

axiom fap_prop3 n g perm : 
 HasHC (n,g) = HasHC (n, fap perm g).


op permute_wit : permutation -> hc_wit -> hc_wit = map.





module HP  = {
  var n : int                   (* size of the graph *)
  var g : graph                 (* n*n adj. matrix *)
  var prm : permutation         (* uniformly sampled permutation *)
  var w : hc_wit                (* hamiltonian cycle *)
  var fal : bool list           (* flattened and permuted g *)

  var pi_gwco : (commitment * opening) list
  var pi_w : hc_wit
  
  proc commit(p_a : hc_prob, w_a : hc_wit)  = {
    (n,g) <- p_a;
    w     <- w_a;
    prm   <$ perm_d n;
    fal   <- fap prm g;

    pi_gwco <@ DJM.main5(fal);  (* map Com fal *)
    return map fst pi_gwco;
  }
  
  proc response(b : bool) : hc_resp = {
    pi_w <- permute_wit prm w;

    return if b then Left (prm, map snd pi_gwco) 
                else Right (pi_w, 
                        map snd (take n (ip (prj pi_w) pi_gwco)));
 } 
}.


op hc_verify (p : hc_prob) (c : hc_com) (b : bool)  (r : hc_resp) : bool =
 with  r = (Left x) => b /\ all Ver (zip (fap x.`1 p.`2) (zip c x.`2))
                         /\ size c = p.`1 * p.`1
                        /\ size p.`2 = p.`1 * p.`1
                         /\ size x.`2 = p.`1 * p.`1

 with r = (Right x) => ! b /\ uniq x.`1
                        /\ size x.`1 = p.`1
                        /\ size c = p.`1 * p.`1
                        /\ size x.`2 = p.`1
                        /\ all Ver 
                             (zip (nseq p.`1 true) (zip (take p.`1 (hc_align x.`1 c)) x.`2))
                        /\ perm_eq x.`1 (range 0 (p.`1))
                        /\ size p.`2 = p.`1 * p.`1.

module HV  = {
  var b : bool
  var n : int
  var g : graph
  var hc : hc_com

  proc challenge(p_a : hc_prob, c_a : hc_com) : bool = {
    (n,g) <- p_a;
    hc <- c_a;
    b <$ {0,1};
    return b;
  }
  
  proc verify(c : hc_com, r_a : hc_resp) : bool = {
    return (hc_verify (n,g) hc b r_a) ; 
 } 

  proc summitup(a : com * resp) : sbits = {
   return witness;
  }
}.
