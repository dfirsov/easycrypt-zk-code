require import AllCore DBool Bool List Distr Int Aux DJoin Permutation.
require  GenericSigmaProtocol.


require CommitmentSpecial.
clone include CommitmentSpecial with type message <- bool.


type graph = bool list.         (* n * n list representin n x n matrix *)

op K : int.
axiom K_pos : 0 < K.

type hc_prob = graph.
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
op prj_path ['a]  : hc_wit -> 'a list -> 'a list.


op hc_verify (p : hc_prob) (c : hc_com) (b : bool)  (r : hc_resp) : bool =
 with r = (Left x) => b /\ all Ver (zip (permute_graph x.`1 p) (zip c x.`2))
                         /\ size c = K * K
                         /\ size p = K * K
                         /\ size x.`2 = K * K

 with r = (Right x) => ! b /\ uniq x.`1
                        /\ size x.`1 = K
                        /\ size c = K * K
                        /\ size x.`2 = K
                        /\ all Ver 
                             (zip (nseq K true) 
                                    (zip ((prj_path x.`1 c)) x.`2))
                        /\ perm_eq x.`1 (range 0 K)
                        /\ size p = K * K.


op IsHC (x : hc_prob * hc_wit) : bool 
  = 
    let g = x.`1 in
    let w = x.`2 in
     K = size w /\ 
     K * K = size g /\ 
     perm_eq w (range 0 K) /\ 
     nseq K true = prj_path w g.


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




lemma ishc_prop3 a  g w : IsHC a => a = (g,w) => prj_path w g = nseq K true.
progress. elim H. smt.
qed.


axiom permute_graph_prop1 p n  : 
 permute_graph p (compl_graph n) = (compl_graph n).

axiom permute_graph_prop4  (g : graph) (p : permutation) :
 permute_graph (inv p) (permute_graph p g) = g.

axiom permute_graph_prop2 p g : size (permute_graph p g) = size g.

axiom permute_graph_prop3  g perm w : 
 IsHC (g, w) = IsHC (permute_graph perm g, permute_witness perm w).

axiom prj_lemma (g : graph) (w : hc_wit) (perm : permutation) : 
   prj_path w g = prj_path (permute_witness perm w) (permute_graph perm g).

axiom compl_graph_prop n : 0 <= n => IsHC ((compl_graph n), compl_graph_cyc n).

axiom kjk prm w : prm \in perm_d K => uniq w => uniq (permute_witness prm w).

axiom lemma1 ['a] : forall w (s : 'a list), size w <= size s => size (prj_path w s) = size w.

axiom lemma2 ['a 'b] (f : 'a -> 'b)  w (s : 'a list):   (prj_path  w (map f s)) = map f (prj_path  w s).

axiom lemma3 (w : hc_wit) (s : hc_prob) : completeness_relation s w => prj_path w s = nseq K true.

axiom lemma4 (w : hc_wit) (s : hc_prob) prm : completeness_relation s w => 
   completeness_relation (permute_graph prm s) (permute_witness prm w).

axiom lemma5 x w (s : 'a list) : x \in prj_path w s => x \in s.

axiom lemma6 (x : 'a) xs (y : 'b) ys : size xs = size ys => x \in xs => y \in ys => (x,y) \in zip xs ys.

axiom lemma7 w prm : perm_eq (permute_witness prm w) w.

axiom lemma8 w (x : 'a list) (y : 'b list) : zip (prj_path w x) (prj_path w y) = prj_path w (zip x y).




module HonestProver : HonestProver  = {
  var g : graph                 (* n*n adj. matrix *)
  var prm : permutation         (* uniformly sampled permutation *)
  var w : hc_wit                (* hamiltonian cycle *)
  var fal : bool list           (* flattened and permuted g *)
  var pi_gwco : (commitment * opening) list
  var pi_w : hc_wit
  
  proc commitment(p_a : hc_prob, w_a : hc_wit)  = {
    g <- p_a;
    w     <- w_a;
    prm   <$ perm_d K;
    fal   <- permute_graph prm g;
    pi_gwco <$ djoinmap Com fal; 

    return map fst pi_gwco;
  }
  
  proc response(b : bool) : hc_resp = {
    pi_w <- permute_witness prm w;
    return if b then Left (prm, map snd pi_gwco) 
                else Right (pi_w, map snd (prj_path pi_w pi_gwco));
 } 
}.
