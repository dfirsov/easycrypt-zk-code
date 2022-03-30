pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.

require import Permutation.

type sbits.
type commitment, opening.

op Com  : bool -> (commitment * opening) distr.
op Ver : bool * (commitment * opening)  -> bool.

type graph = bool list list.

type hc_prob = (int * graph).
type hc_wit  = int list.
type hc_com  = commitment list.
type hc_resp = (permutation * (opening list) , hc_wit * (opening list)) sum.

module type Dist = {
   proc run(s : sbits) : bool
}.

require ZK_General.
clone import ZK_General as ZK_defs with type prob  = hc_prob,
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
                                   type b <- (commitment * opening),
                                   op   d <- Com.
                                        


op compl_graph     : int -> graph.
op compl_graph_cyc : int -> int list = range 0.


op IsHC : hc_prob * hc_wit -> bool. 
op HasHC (Ny : hc_prob) = exists w, IsHC (Ny, w).

axiom ishc_prop1 a : IsHC a =>
 (fst (fst a)) = size (snd a) 
    /\ size (flatten (snd (fst a))) 
         = (fst (fst a)) * (fst (fst a)).


axiom ishc_prop2 a : IsHC a =>
  0 < (fst (fst a)).



(* flatten and permute  *)
op fap (p : permutation) (g : graph) : bool list
 = flatten (pi p (map (pi p) g)).

axiom fap_prop1 p n  : 
 fap p (compl_graph n) = flatten (compl_graph n).

axiom fap_prop2 p g  : 
 size (fap p g) = size (flatten g).


op permute_wit : permutation -> hc_wit -> hc_wit = map.

(* projects the witness up-fron
   prj (1,2,3) [x11 x12 x13 x21 x22 x23 x31 x32 x33]

    project out the positions of the cycle (1,2)(2,3)(3,1)
           [x12 x23 x31] ++ [x11 x13 x21 x22 x32 x33]
*)
op prj  : hc_wit -> permutation.


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


op hc_verify (p : hc_prob) (c : hc_com) (b : bool)  (r : hc_resp) : bool =
 with r = (Left x) => b /\ all Ver (zip (fap x.`1 p.`2) (zip c x.`2))
                        /\ size c = p.`1 * p.`1
 with r = (Right x) => ! b /\ uniq x.`1 /\ size x.`1 = p.`1
                        /\ size c = p.`1 * p.`1
                        /\ size x.`2 = p.`1
                        /\ all (fun x => Ver (true, x)) 
                          (zip (take p.`1 (ip (prj x.`1) c)) x.`2).


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

lemma sub_all ['a]:
   forall (p1 p2 : 'a -> bool) (s : 'a list),
     (forall (x : 'a), p1 x => p2 x) => all p1 s => all p2 s.
move => p1 p2.  elim. smt.
smt.
qed.


lemma take_zip ['a 'b] : 
   forall  (n :  int) (l1 : 'a list)(l2 : 'b list),
   zip (take n l1) (take n l2) 
  = take n (zip l1 l2).
apply ge0ind. smt.
smt.
progress.
case (l1 = []).
smt.
progress.
have f1 : exists a1 l1', l1 = (a1 :: l1').
clear H0 H.  
exists (head witness l1) (behead l1).
smt.
elim f1.
progress. 
have -> : (n + 1 <= 0) = false.
smt. simplify.
case (l2 = []).
smt.
progress. 
have f2 : exists a2 l2', l2 = (a2 :: l2').
exists (head witness l2) (behead l2).
smt.
elim f2.
progress. 
have -> : (n + 1 <= 0) = false.
smt. simplify. smt.
qed.


lemma take_const ['a 'b] (c : 'b) f : forall (l : 'a list) ,
 all (fun x => f (c, x)) l =
   all f  (zip (nseq (size l) c) l).
proof. 
elim. smt.
progress. 
have ->: 1 + size l = size l + 1. smt.
rewrite nseqS. smt.
simplify. smt.
qed.

lemma take_nseq ['a ] (c : 'a) : forall n ,
  (take n (nseq n c)) = nseq n c.
apply ge0ind. smt.
smt.
smt.
qed.

search nseq.

search zip.
lemma hc_complete pa wa  :  IsHC (pa,wa) =>
 hoare[ Correct(HP,HV).run : arg = (pa,wa) ==> res ] .
move => ishc. proc. inline*. wp. rnd. 
wp. rnd. wp. rnd. wp. skip.
progress.
case (b1 = true). 
move => h. rewrite h. simplify.
  + have ->: (zip (unzip1 x0) (unzip2 x0)) = x0. rewrite zip_unzip. auto.
split.
have : all (fun (xy : bool * (commitment * opening) ) => xy.`2 \in (Com xy.`1)) 
    (zip  (fap prm Ny{hr}.`2) x0).
have f3 :   
  size (fap prm Ny{hr}.`2) = size x0 /\
  all (fun (xy : bool * (commitment * opening)) => xy.`2 \in Com xy.`1)
    (zip (fap prm Ny{hr}.`2) x0).
apply (supp_djoinmap Com ((fap prm Ny{hr}.`2))  x0). auto.
elim f3. move => f31 f32.
auto.
move => q.
apply (sub_all (fun (xy : bool * (commitment * opening)) => xy.`2 \in Com xy.`1) Ver) .
simplify. admit. auto.
have f1 : size x0 = size (fap prm Ny{hr}.`2).
smt.
have f2 : size x0 = size (unzip1 x0).
smt.
rewrite - f2. 
rewrite f1.
rewrite fap_prop2.
smt.
move => p.

have ->: b1 = false. smt.
simplify. clear p. progress.
admit.
admit.
admit.
admit.

have ->: 
  (unzip2 (take Ny{hr}.`1 (ip (prj (permute_wit prm w{hr})) x0)))
  = ((take Ny{hr}.`1 (unzip2 (ip (prj (permute_wit prm w{hr})) x0)))).
smt.

have ->: 
  (zip (take Ny{hr}.`1 (ip (prj (permute_wit prm w{hr})) (unzip1 x0)))
     (take Ny{hr}.`1 (unzip2 (ip (prj (permute_wit prm w{hr})) x0))))
  = take Ny{hr}.`1  

     (zip ((ip (prj (permute_wit prm w{hr})) (unzip1 x0)))
          ((unzip2 (ip (prj (permute_wit prm w{hr})) x0)))).
apply take_zip.

have ->: ((ip (prj (permute_wit prm w{hr})) (unzip1 x0)))
  = (unzip1 (ip (prj (permute_wit prm w{hr})) (x0))).
rewrite map_ip. auto.

have ->: 
 (zip (unzip1 (ip (prj (permute_wit prm w{hr})) x0))
        (unzip2 (ip (prj (permute_wit prm w{hr})) x0)))
 = (ip (prj (permute_wit prm w{hr})) x0).
apply zip_unzip.

pose pi_w := (permute_wit prm w{hr}).
pose n := Ny{hr}.`1.
pose fapg := (fap prm Ny{hr}.`2). 
have ->: 
 all (fun x => Ver (true, x)) (take n (ip (prj pi_w) x0))
 = all (fun x => Ver x)
  (take n (zip (nseq n true) (ip (prj pi_w) x0))).
rewrite  take_const.
have ->: (size (take n (ip (prj pi_w) x0))) = n. admit.
rewrite - take_zip.
rewrite take_nseq. auto.

have ->: (take n (zip (nseq n true) (ip (prj pi_w) x0))) =
  (take n (zip (ip (prj pi_w) fapg) (ip (prj pi_w) x0))).
  have ->: take n (zip (nseq n true) (ip (prj pi_w) x0)) =
     (zip (nseq n true) (ip (prj pi_w) x0)). 
apply take_oversize.
rewrite size_zip.
rewrite size_nseq. 
  have ->: (max 0 n) = n.  smt(ishc_prop2). smt.
  have ->: take n (zip (ip (prj pi_w) fapg) (ip (prj pi_w) x0))
   = (zip (take n (ip (prj pi_w) fapg)) (take n (ip (prj pi_w) x0))).
   rewrite - take_zip. auto.
  have ->: (take n (ip (prj pi_w) fapg)) = nseq n true.
  admit.
admit.

have f1 : all Ver (zip fapg x0). admit.

have f2 : all Ver (zip (ip (prj pi_w) fapg)  (ip (prj pi_w) x0)).
admit.
smt.
qed.

(* 
1/ all Ver (zip fap x0)
2/ all Ver (zip (ip pi_w fap) (ip pi_w x0))
3/ take $ all Ver (zip (ip pi_w fap) (ip pi_w x0))
4/ all Ver (take $ (zip (ip pi_w fap) (ip pi_w x0))) 
5/ all Ver ((zip (take (ip pi_w fap)) (take (ip pi_w x0)))) 
  [(1...1) = take n (ip w) (flatten g) = take n (ip (prj w)) fap ) ]
6/ all Ver ((zip (1...1) (take (ip pi_w x0)))) 
7/ all (Ver (1,x)) (take (ip pi_w x0))

*)


qed.
