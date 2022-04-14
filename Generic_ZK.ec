require import AllCore.

require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.
require import Aux.

type prob, wit, chal, com, resp, sbits, event, auxiliary_input.

require While_not_b_proc.
clone import While_not_b_proc as IF with type iat <- prob * wit,
                                         type rt  <- bool.

require While_Props.
clone import While_Props as MW with type irt   <- prob,
                                    type rrt   <- event * sbits,
                                    type sbits <- sbits.
import MW.IFB.
import MW.IFB.IM.



module type Simulator = {
  proc run(Ny : prob) : event * sbits
}.

(* (statement: statement, witness: witness, aux: auxiliary_input, summary: adv_summary) *)

module type Dist = {
  proc run(_:prob * wit * auxiliary_input * event * sbits) : bool
}.


module W0(Sim1:Simulator, D : Dist) = {
  proc run(a : prob, w : wit, aux : auxiliary_input) = {
      var r, b;
      r <- Sim1.run(a);
      b <- D.run(a,w,aux,r.`1,r.`2);
      return (b, r);
  }
}.


module W1(Sim1:Simulator, D : Dist) = {
  module M = W(Sim1)
  proc run(a : (event * sbits -> bool) * prob * int * int * (event * sbits), w : wit, aux : auxiliary_input) = {
      var r, b;
      r <- M.whp(a);
      b <- D.run(a.`2,w,aux,r.`1,r.`2);
      return (b, r);
  }
}.


module Iter(Sim1 : Simulator, D : Dist)  = {
  module WI = W1(Sim1,D)
  proc run(fevent : event, Ny : prob, w : wit, aux : auxiliary_input, ea : int, E : event * sbits -> bool) = {
    var r;
    r <@ WI.run((E,Ny,1,ea,(fevent,witness)),w,aux);
    return r;
  }
}.




section.

declare module Sim1 : Simulator{DW, W}.
declare module D : Dist {Sim1}.

axiom Sim1_ll : islossless Sim1.run.
axiom D_ll    : islossless D.run.

op fevent : event.
op E : event * sbits -> bool.
axiom  Estart :  E (fevent, witness) = false.


local lemma zk_step1 &m E p eps zkp:
   `|Pr[ W0(Sim1, D).run(p) @ &m : E res.`2 /\ res.`1]
      / Pr[W0(Sim1, D).run(p) @ &m : E res.`2] 
        - zkp| <= eps
  => 0%r <= eps 
  => 0%r < Pr[W0(Sim1,D).run(p) @ &m : E res.`2]
  => exists (eps' : real),  0%r <= eps' <= eps  
  /\ `|Pr[ W0(Sim1,D).run(p) @ &m : E res.`2 /\ res.`1] 
         / Pr[W0(Sim1,D).run(p) @ &m : E res.`2] 
                - zkp| = eps'
  /\ (Pr[ W0(Sim1,D).run(p) @ &m : E res.`2 /\ res.`1] 
      = Pr[W0(Sim1,D).run(p) @ &m : E res.`2]  
        * (zkp - eps')
      \/
      Pr[ W0(Sim1,D).run(p) @ &m : E res.`2 /\ res.`1] 
      = Pr[W0(Sim1,D).run(p) @ &m : E res.`2]  
        * (zkp + eps')).
proof.
progress.
apply oip3;auto.
qed.



local lemma zk_step2 &m E p ea w aux :
  Pr[ W1(Sim1,D).run((E,p,1,ea,(fevent,witness)),w,aux) 
           @ &m : E res.`2 /\ res.`1 ]  
     = big predT
        (fun i => Pr[W0(Sim1,D).run(p,w,aux) @ &m : !E res.`2] ^ i 
         * Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\  res.`1] )
        (range 0 ea). 
admitted.


local lemma zk_step3 &m p eps ea coeff zkp (w : wit) aux:
   `|Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\ res.`1]
      / Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] 
        - zkp| <= eps
  => 0%r < Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]  
  => 0%r <= eps 
  => coeff = big predT
               (fun i => Pr[W0(Sim1,D).run(p,w,aux) @ &m : !E res.`2] ^ i 
                          * Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2])
               (range 0 ea) 
  => exists (eps' : real), 
    0%r <= eps' <= eps   /\ 
     `|Pr[ W1(Sim1,D).run((E,p,1,ea,(fevent,witness)), w, aux   ) 
           @ &m : E res.`2 /\ res.`1 ]  
         - coeff * zkp| = coeff * eps'.
proof. move => H0 H1 H2 coeffeq.
have :  exists (eps' : real),  0%r <= eps' <= eps  
  /\ `|Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\ res.`1] 
         / Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] 
                - zkp| = eps'
  /\ (Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\ res.`1] 
      = Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]  
        * (zkp - eps')
      \/
      Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\ res.`1] 
      = Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]  
        * (zkp + eps')).
apply (zk_step1 &m). assumption. assumption. assumption.
elim. move => eps' [H3 [H41 H42 ]].
exists eps'. 
split. auto.
apply oip4.
rewrite coeffeq.
have ->: Pr[W0(Sim1,D).run(p,w,aux) @ &m : ! E res.`2]
  = 1%r - Pr[W0(Sim1,D).run(p,w,aux) @ &m :  E res.`2].
  have ->: 1%r = Pr[W0(Sim1,D).run(p,w,aux) @ &m :  true].
  byphoare. 
proc. call D_ll. call Sim1_ll. auto. auto. auto.
  have ->: Pr[W0(Sim1,D).run(p,w,aux) @ &m : true] = Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]
   + Pr[W0(Sim1,D).run(p,w,aux) @ &m : !E res.`2]. rewrite Pr[mu_split E res.`2]. 
  simplify. smt. smt.
  have : 0%r <=
bigi predT
  (fun (i : int) =>
     (1%r - Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]) ^ i *
     Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]) 0 ea.
  apply (big_geq0  Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] _ ea). smt.
  smt. 
case (Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\ res.`1] 
      = Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]  
        * (zkp + eps')).
progress. rewrite /(\o).
rewrite zk_step2. 
rewrite H. simplify.
have : bigi predT
  (fun (i : int) =>
     Pr[W0(Sim1,D).run(p,w,aux) @ &m : ! E res.`2] ^ i *
     (Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] *
      (zkp + eps'))) 0 ea =
coeff * zkp + coeff * eps'.
rewrite coeffeq.
rewrite mulr_suml.
rewrite mulr_suml.
rewrite - big_split.
simplify. smt.
timeout 20. smt.
move => H5.
have : Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\ res.`1] 
        = Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]  
          * (zkp - eps').
smt.
progress. rewrite /(\o).
rewrite zk_step2. 
rewrite H. simplify.
have : bigi predT
  (fun (i : int) =>
     Pr[W0(Sim1,D).run(p,w,aux) @ &m : ! E res.`2] ^ i *
     (Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] *
      (zkp - eps'))) 0 ea =
coeff * zkp - coeff * eps'.
rewrite coeffeq.
rewrite mulr_suml.
rewrite mulr_suml.
rewrite - big_split_min.
simplify. smt.
timeout 20. smt.
qed.


local lemma zk_non_final &m p  eps ea coeff zkp w aux:
   `|Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\  res.`1] / Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] 
        - zkp| <= eps

  => 0%r < Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] 
  => 0%r <= eps                 (* not needed *)
  => coeff = big predT
               (fun i => Pr[W0(Sim1,D).run(p,w,aux) @ &m : !E res.`2] ^ i 
                          * Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2])
               (range 0 ea) 
  => `|Pr[ Iter(Sim1, D).run((fevent, p, w,aux,ea,E) ) 
           @ &m : E res.`2 /\ res.`1 ]  
              - coeff * zkp| <= eps.
proof. move => H1 H2 H3 H4. 
have ->: 
  Pr[Iter(Sim1, D).run(fevent, p, w, aux,ea, E) @ &m :
     E res.`2 /\ res.`1]
  = Pr[ W1(Sim1,D).run((E,p,1,ea,(fevent,witness)), w, aux) 
           @ &m : E res.`2 /\ res.`1 ] .  
 byequiv (_: _==> ={res}). proc*.
inline Iter(Sim1, D).run. sp. wp. 
call (_: ={glob Sim1, glob D}). simplify. sim. 
skip. smt. auto. auto.
have : coeff <= 1%r. 
rewrite H4.
have ->: Pr[W0(Sim1,D).run(p,w,aux) @ &m : ! E res.`2]
  = 1%r - Pr[W0(Sim1,D).run(p,w,aux) @ &m :  E res.`2].
  have ->: 1%r = Pr[W0(Sim1,D).run(p,w,aux) @ &m :  true].
  byphoare. proc.  call D_ll. call Sim1_ll.  auto. auto. auto.
  have ->: Pr[W0(Sim1,D).run(p,w,aux) @ &m : true] = Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]
   + Pr[W0(Sim1,D).run(p,w,aux) @ &m : !E res.`2]. rewrite Pr[mu_split E res.`2]. 
  simplify. smt. smt.
  have : 
bigi predT
  (fun (i : int) =>
     (1%r - Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]) ^ i *
     Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]) 0 ea <= 1%r.
  apply (big_leq1  Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] _ ea). smt.
  smt.
move => H6.
have : exists eps', 0%r <= eps' <= eps /\ `|Pr[W1(Sim1,D).run((E, p, 1, ea,
                 (fevent, witness)),w,aux) @ &m :
     E res.`2 /\ res.`1] -
  coeff * zkp| 
  = coeff * eps'.
apply (zk_step3 &m  p  eps ea coeff).
auto.  assumption. auto. auto. auto.
elim.
move => eps' [eps'p1 epsp2].
apply (ler_trans (coeff * eps')).
smt.
smt.
qed.


local lemma zk_almost_final &m p w eps ea coeff zkp aux:
   `|Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\ res.`1] 
        / Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] 
        - zkp| <= eps
  => 0%r < Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] 
  => coeff = big predT
               (fun i => Pr[W0(Sim1,D).run(p,w,aux) @ &m : !E res.`2] ^ i 
                         * Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2])
               (range 0 ea) 
  => `|Pr[ Iter(Sim1, D).run((fevent, p,w,aux,ea,E)) 
           @ &m : E res.`2 /\ res.`1 ]  
         - zkp| <= eps + (1%r - coeff).
proof.
move => H1 H2 H3.
have ie1 : `|Pr[ Iter(Sim1, D).run(fevent, p,w,aux,ea,E) 
           @ &m : E res.`2 /\  res.`1 ]  
         - coeff * zkp| <= eps.
apply (zk_non_final &m p eps ea coeff zkp);auto. smt.
apply ots. admit.  admit.
auto.
qed.


local lemma zk_final &m p w eps ea zkp aux:
   `|Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\ res.`1] 
        / Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] 
        - zkp| <= eps
  => 0 <= ea
  => `|Pr[ Iter(Sim1, D).run(fevent,p,w,aux,ea,E) 
           @ &m : E res.`2 /\ res.`1 ]  
         - zkp| 
           <= eps + Pr[W0(Sim1,D).run(p,w,aux) @ &m : !E res.`2] ^ ea.
proof. 
case (0%r = Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]).
move => r. rewrite - r. simplify. progress.
have <-: 1%r = Pr[W0(Sim1,D).run(p,w,aux) @ &m : ! E res.`2]. 
  have ->: 1%r = Pr[W0(Sim1,D).run(p,w,aux) @ &m : true ].  
  byphoare. proc. call D_ll. call Sim1_ll. auto. auto. auto.
  rewrite Pr[mu_split (E res.`2)]. simplify. rewrite - r. 
  simplify. auto.
have ->: 1%r ^ ea = 1%r. smt.
smt.
progress.
have f : 0%r < Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2].  smt.
have ->: Pr[W0(Sim1,D).run(p,w,aux) @ &m : !E res.`2] ^ ea
 = 1%r - (1%r - Pr[W0(Sim1,D).run(p,w,aux) @ &m : !E res.`2] ^ ea).
smt.
rewrite - big_formula_p. smt. auto. progress.
have ->: (1%r - Pr[W0(Sim1,D).run(p,w,aux) @ &m : ! E res.`2])
 = Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2].
have ->: 1%r = Pr[W0(Sim1,D).run(p,w,aux) @ &m :  true].
byphoare.
proc.  call D_ll. call Sim1_ll. auto. auto. auto.
have ->: Pr[W0(Sim1,D).run(p,w,aux) @ &m : true] = Pr[W0(Sim1,D).run(p,w,aux) @ &m : ! E res.`2]
 + Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]. rewrite Pr[mu_split ! E res.`2].
simplify. smt. smt.
apply (zk_almost_final &m);auto.
qed.


lemma zk_final_le &m p w p0 eps ea zkp aux:
   `|Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\ res.`1] 
        / Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] - zkp| <= eps
  => 0 <= ea
  => Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] >= p0
  => `|Pr[ Iter(Sim1, D).run(fevent,p,w,aux,ea,E) 
           @ &m : E res.`2 /\ res.`1 ] - zkp| 
              <= eps + (1%r-p0) ^ ea.
progress.
have fff : p0 <= 1%r. smt.
have f1 : `|Pr[ Iter(Sim1, D).run(fevent, p,w,aux,ea,E) 
           @ &m : E res.`2 /\ res.`1 ]  
         - zkp| 
      <= eps + (1%r - Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] )^ea.
have ->: (1%r - Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2] ) = 
  (Pr[W0(Sim1,D).run(p,w,aux) @ &m : !E res.`2] ). 
have ->: 1%r = Pr[W0(Sim1,D).run(p,w,aux) @ &m :  true].
byphoare. proc. call D_ll. call Sim1_ll. auto. auto. auto.
have ->: Pr[W0(Sim1,D).run(p,w,aux) @ &m : true] = Pr[W0(Sim1,D).run(p,w,aux) @ &m : ! E res.`2]
 + Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]. rewrite Pr[mu_split ! E res.`2]. 
simplify. smt. smt.
apply (zk_final &m).
have f2 : 
 (1%r - Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]) <= (1%r - p0). smt.
have f3 : (1%r - Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2]) ^ ea <= (1%r - p0) ^ ea.
apply multn2;auto. smt. auto. auto. auto. smt.
qed.
end section.
print zk_final_le.
