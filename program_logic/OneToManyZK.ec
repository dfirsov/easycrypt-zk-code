require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.
require import Aux.

type prob, wit, sbits, event, auxiliary_input.

op E : event * sbits -> bool.

require WhileCycle.
clone import WhileCycle as MW with type irt    <- prob * auxiliary_input,
                                    type rrt   <- event * sbits,
                                    type sbits <- sbits,
                                    op MyPred <- E.
import MW.IFB.
import MW.IFB.IM.



module type Dist = {
  proc guess(_:prob * wit * auxiliary_input * sbits) : bool
}.


module type Simulator1 = {
  proc run(Ny : prob, aux : auxiliary_input) : event * sbits
}.


module W0(Sim1:Simulator1,  D : Dist) = {
  module Sim1 = Sim1
  proc run(a : prob, w : wit, aux : auxiliary_input) = {
      var r, b;
      r <@ Sim1.run(a,aux);
      b <@ D.guess(a,w,aux,r.`2);
      return (b, r);
  }
}.


module W1(Sim1:Simulator1,  D : Dist) = {
  module M = W(Sim1)
  proc run(a : (event * sbits -> bool) * (prob * auxiliary_input) * int * int * (event * sbits), w : wit) = {
      var r, b;
      r <@ M.whp(a);
      b <@ D.guess(a.`2.`1,w,a.`2.`2, r.`2);
      return (b, r);
  }
}.




module Iter(Sim1 : Simulator1,  D : Dist)  = {
  module WI = W1(Sim1,D)
  proc run(fevent : event, Ny : prob, w : wit, aux : auxiliary_input, ea : int, E : event * sbits -> bool) = {
    var r;
    r <@ WI.run((E,(Ny,aux),1,ea,(fevent,witness)),w);
    return r;
  }
}.





section.
(* declare module V : MaliciousVerifier{DW,W}. *)
declare module Sim1 <: Simulator1{-DW, -W}.
declare module D <: Dist.

declare axiom Sim1_ll : islossless Sim1.run.

declare axiom Sim1_rew_ph : forall (x : (glob Sim1)),
  phoare[ Sim1.run : (glob Sim1) = x ==> !E res => (glob Sim1) = x] = 1%r.


declare axiom D_ll    : islossless D.guess.

op fevent : event.

declare axiom  Estart :  E (fevent, witness) = false.


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
  Pr[ W1(Sim1,D).run((E,(p,aux),1,ea,(fevent,witness)),w) 
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
     `|Pr[ W1(Sim1,D).run((E,(p,aux),1,ea,(fevent,witness)), w   ) 
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
proc. call D_ll. call Sim1_ll.  auto. auto. auto.
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
   `|Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\  res.`1] 
          / Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 ] 
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
  = Pr[ W1(Sim1,D).run((E,(p,aux),1,ea,(fevent,witness)), w) 
           @ &m : E res.`2 /\ res.`1 ] .  
 byequiv (_: _==> ={res}). proc*.
inline Iter(Sim1, D).run. sp. wp. 
inline W1(Sim1, D).run. sp. 
seq 1 1 :   (a0{2} = a{2} /\
  w0{2} = w{2} /\
  a{1} = (E0{1}, (Ny0{1}, aux0{1}), 1, ea0{1}, (fevent0{1}, witness)) /\
  w1{1} = w0{1} /\
  fevent0{1} = fevent{1} /\
  Ny0{1} = Ny{1} /\
  w0{1} = w{1} /\
  aux0{1} = aux{1} /\
  ea0{1} = ea{1} /\
  E0{1} = E{1} /\
  (a{2}, w{2}) = ((Top.E, (p, aux), 1, ea, (Top.fevent, witness)), w) /\
  (glob D){2} = (glob D){m} /\
  (glob Sim1){2} = (glob Sim1){m} /\
  (fevent{1}, Ny{1}, w{1}, aux{1}, ea{1}, E{1}) =
  (Top.fevent, p, w, aux, ea, Top.E) /\
  (glob D){1} = (glob D){m} /\ (glob Sim1){1} = (glob Sim1){m} /\ r1{1} = r0{2}).
admit. wp. call (_:true). skip. progress. smt. auto. auto.




(* call (_: ={glob Sim1, glob D}). simplify. sim.   *)
(* skip. smt. auto. auto. *)
have : coeff <= 1%r. 
rewrite H4.
have ->: Pr[W0(Sim1,D).run(p,w,aux) @ &m : ! E res.`2]
  = 1%r - Pr[W0(Sim1,D).run(p,w,aux) @ &m :  E res.`2].
  have ->: 1%r = Pr[W0(Sim1,D).run(p,w,aux) @ &m :  true].
  byphoare. proc.  call D_ll. call Sim1_ll. auto. auto. auto.
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
have : exists eps', 0%r <= eps' <= eps /\ `|Pr[W1(Sim1,D).run((E, (p,aux), 1, ea,
                 (fevent, witness)),w) @ &m :
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
apply ots. admit. admit.
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


local lemma zk_final_le &m p w p0 eps ea zkp aux:
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


local lemma zk_final_clean' &m p w p0 eps ea zkp aux:
     `| Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\ res.`1 ]
           / Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 ] - zkp | <= eps
  => 0  <= ea
  => p0 <= Pr[W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 ]
  => `| Pr[Iter(Sim1, D).run(fevent,p,w,aux,ea,E) @ &m : res.`1] - zkp |
              <= eps + 2%r * (1%r-p0) ^ ea.
proof. progress.
have bf :  `|Pr[ Iter(Sim1, D).run(fevent,p,w,aux,ea,E) 
           @ &m : res.`1 ] - zkp| 
              <= (eps + (1%r-p0) ^ ea ) +
(Pr[ Iter(Sim1, D).run(fevent,p,w,aux,ea,E) 
           @ &m : !E res.`2]).
have f1 : `|Pr[ Iter(Sim1, D).run(fevent,p,w,aux,ea,E) 
           @ &m : E res.`2 /\ res.`1 ] - zkp| 
              <= eps + (1%r-p0) ^ ea.
apply (zk_final_le &m p w p0 eps ea zkp aux);auto.
apply (kkk Pr[Iter(Sim1, D).run(fevent, p, w, aux, ea, E) @ &m : res.`1]
Pr[Iter(Sim1, D).run(fevent, p, w, aux, ea, E) @ &m :
         E res.`2 /\ res.`1]). smt.
rewrite Pr[mu_split E res.`2] .
have ->: Pr[Iter(Sim1, D).run(fevent, p, w, aux, ea, E) @ &m : res.`1 /\ E res.`2]
 = Pr[Iter(Sim1, D).run(fevent, p, w, aux, ea, E) @ &m : E res.`2 /\ res.`1 ].
smt.
smt.
auto.  
clear H.
have bf2 : Pr[Iter(Sim1, D).run(fevent, p, w, aux, ea, E) @ &m : ! E res.`2]
  <= (1%r - p0) ^ ea.
  have bf3: Pr[W0(Sim1, D).run(p, w, aux) @ &m : !E res.`2] <= 1%r - p0.
    have -> : 1%r = Pr[W0(Sim1, D).run(p, w, aux) @ &m : true]. byphoare.
    proc. call D_ll. call Sim1_ll. auto. auto. auto.
       have : Pr[W0(Sim1, D).run(p, w, aux) @ &m : true] 
                - Pr[W0(Sim1, D).run(p, w, aux) @ &m : !E res.`2] 
                 = Pr[W0(Sim1, D).run(p, w, aux) @ &m : E res.`2]. 
    rewrite Pr[mu_split E res.`2]. simplify. smt. smt. 

  have ->: Pr[Iter(Sim1, D).run(fevent, p, w, aux, ea, E) @ &m : ! E res.`2] 
     = Pr[ W(Sim1).whp(E,(p,aux),1,ea,(fevent,witness)) @ &m : ! E res ].
   byequiv. proc*.  inline Iter(Sim1, D).run. sp. wp. inline Iter(Sim1, D).WI.run.
 sp. wp. call {1} D_ll. 
  conseq (_: _==> r1{1} = r0{2}). smt.
call (_: ={glob Sim1}).  sim. skip. progress. auto. auto.
apply (final_zz_le (Sim1) Sim1_ll _ &m). apply Sim1_rew_ph. smt. auto. 
have ->: Pr[Sim1.run(p,aux) @ &m : ! E res] 
  = Pr[W0(Sim1, D).run(p, w, aux) @ &m : ! E res.`2].
byequiv. proc*. inline*. wp. sp. call {2} D_ll. call (_: true).
  skip. progress. auto. auto. auto.
smt. auto. auto. auto. smt.
qed.


lemma one_to_many_zk &m p w p0 eps ea zkp aux:
     `| Pr[ W0(Sim1,D).run(p,w,aux) @ &m : E res.`2 /\ res.`1 ]
           / Pr[Sim1.run(p,aux) @ &m : E res]  - zkp | <= eps
  => 0  <= ea
  => p0 <= Pr[Sim1.run(p,aux) @ &m :  E res] 
  => `| Pr[Iter(Sim1, D).run(fevent,p,w,aux,ea,E) @ &m : res.`1] - zkp |
              <= eps + 2%r * (1%r-p0) ^ ea.
have ->: Pr[Sim1.run(p,aux) @ &m : E res] 
  = Pr[W0(Sim1, D).run(p, w, aux) @ &m :  E res.`2].
byequiv. proc*. inline*. wp. sp. call {2} D_ll. call (_: true).
  skip. progress. auto. auto. auto.
progress.
smt. auto.  auto. apply (zk_final_clean' &m p w p0 eps ea zkp aux);auto.
qed.
end section.

