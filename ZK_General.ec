require import AllCore.

(* Dominique: prob to statement[in language]?


*)
type prob, wit, chal, com, resp, sbits, event.

(*  *)
module type Prover = {
  proc commit(x : prob, w : wit) : com
  proc response(ch : chal) : resp
}.

(* module type GenProver = { *)
(*   proc *init() : unit *)
(*   (* proc rounds() : int *) *)
(*   proc interact(m : msg) : msg option *)
(* }. *)

(* module type GenVerifier = { *)
(*   proc *init() : unit *)
(*   proc interact(m: msg) : msg option *)
(*   proc result(): bool *)
(* } *)

(* module 3ToGen(HV: Verifier3) = { *)
(*   proc init() = HV.init() *)
(*   proc interact(m:msg) : msg  *)
(*   if (i==0) HV.comm *)
(*   ... *)
(*   if (i==3) 3ToGen.result = HV.finalmsgreaction(m) *)
(* } *)
(* proc result()  = {return 3ToGen.result} *)
(* } *)

(* module SeqComposeP(P : GenProver) : GenProver = { ... } *)

(* If P is e-sound, then SeqComposeV(HV,n) is e^n-sound 

M(Correct(P, HV : Verifier3)) = Correct(M(P), SeqComposeV(3ToGen(HV) : GenVerifier))

(!P. M(Correct(P, HV)) <= e) = (!P. Correct(M(P), SeqComposeV(HV)) <= e) = (!P. Correct(P, SeqComposeV(HV)))

pros of new approach: more general -> proofs harder

*)

(* AProver, aux in &m of state Pr exper*)
module type AProver = {
  proc commit(x : prob) : com
  proc response(ch : chal) : resp
}.


module type RewProver = {
  proc * setState(s : sbits) : unit
  proc getState() : sbits

  proc commit(x : prob, w : wit) : com
  proc response(ch : chal) : resp
}.


module type HVerifier = {
  proc challenge(Ny : prob, c : com) : chal
  proc verify(c : com, r : resp)     : bool
}.

(* rename Verifier to AVerifier  *)
module type Verifier = {
  proc challenge(Ny : prob, c : com) : chal
  proc verify(c : com, r : resp)     : bool
  proc summitup(c : com, r : resp)   : sbits
}.


module type RewVerifier = {
  proc * setState(s : sbits) : unit
  proc getState() : sbits
  proc challenge(Ny : prob, c : com) : chal
  proc verify(c : com, r : resp)     : bool
  proc summitup(c : com, r : resp)   : sbits
}.


module type Simulator = {
  proc run(Ny : prob) : event * sbits
}.

(* Correctness

Prover  -> H..
Verifier -> H..

use for completeness only
Correct -> Completeness

*)
module Correct(P : Prover, V : Verifier) = {
  proc run(Ny:prob, w : wit) = {
    var c,b,r,result;
    c <- P.commit(Ny,w);  
    b <- V.challenge(Ny,c);
    r <- P.response(b);
    result <- V.verify(c,r);  
    return result;
  }
}.



(* either give all arguments to V queries each time or only new ones
and store the previous ones in the state *)
module Soundness(P : AProver, V : Verifier) = {
  proc run(Ny:prob) = {
    var com,ch,resp,result;
    com <- P.commit(Ny);  
    ch <- V.challenge(Ny,com);
    resp <- P.response(ch);
    result <- V.verify(com,resp);  
    return result;
  }
}.



(* ZK -> ZK_Real
Verifier -> AVerifier

 *)
module ZK(P : Prover, V : Verifier) = {
  proc main(Ny : prob, w : wit) = {
    var c,b,r,result;
    c <- P.commit(Ny,w);
    b <- V.challenge(Ny,c);
    r <- P.response(b);
    result <- V.summitup(c,r);
    return result;
  }
}.


require While_not_b_proc.
clone import While_not_b_proc as IF with type iat <- (prob * wit),
                                         type rt <- bool.



section. 
declare module P : Prover{M}.
declare module V : Verifier{M}.

axiom V_verify_ll    : islossless V.verify.
axiom V_challenge_ll : islossless V.challenge.
axiom P_commit_ll    : islossless P.commit.
axiom P_response_ll  : islossless P.response.


lemma iterated_correctness_ph (p : real) ia  :  
 (phoare[ Correct(P,V).run : arg = ia ==> res ] = p) 
   => forall e, 0 <= e =>
   phoare[ M(Correct(P,V)).whp 
         : arg = (ia,[!],1,e+1,true) 
          ==> res ] = (p ^ (e+1)).
proof. move => H1 e ep .
have fact1 : phoare[ M(Correct(P,V)).whp_if_end 
                     : arg = (ia,[!],1,e,true) 
                         ==> res ] = (p ^ (e+1)).
conseq (asdsad (Correct(P,V)) _  p  ia true [!] _ _ e ep ). 
proc. 
call V_verify_ll.
call P_response_ll.
call V_challenge_ll.
call P_commit_ll.
skip. auto.
simplify. conseq H1. auto.
conseq (whp_split_if_end' (Correct(P,V)) _ [!] ia 1 e true (p^(e+1))  
                             (fun x => x) _). 
proc.
call V_verify_ll.
call P_response_ll.
call V_challenge_ll.
call P_commit_ll.
skip. auto.
apply fact1.
qed.


lemma iterated_correctness_le_ph (p : real) ia :  
 (phoare[ Correct(P,V).run : arg = ia ==> res ] <= p) 
   => forall e, 0 <= e =>
   phoare[ M(Correct(P,V)).whp 
           : arg = (ia,[!],1,e+1,true) 
               ==> res ] <= (p ^ (e+1)).
proof. move => H1 e ep .
have fact1  : phoare[ M(Correct(P,V)).whp_if_end 
                      : arg = (ia,[!],1,e,true) ==> res ] <= (p ^ (e+1)).
conseq (asdsad_le (Correct(P,V)) _  p  ia true [!] _ _ e ep ). 
proc. 
call V_verify_ll.
call P_response_ll.
call V_challenge_ll.
call P_commit_ll.
skip. auto.
simplify. conseq H1. auto.
conseq (whp_split_if_end_le (Correct(P,V)) _ [!] ia 1 e true (p^(e+1)) 
           (fun x => x) _). 
proc.
call V_verify_ll.
call P_response_ll.
call V_challenge_ll.
call P_commit_ll.
skip. auto.
apply fact1.
qed.

end section.





require While_Props.
clone import While_Props as MW with type irt <- (prob),
                                    type rrt <- event * sbits.
import MW.IFB.
import MW.IFB.IM.

section.

require import Aux.

declare module Sim1 : Simulator{DW, W}.
declare module P : Prover.
declare module V : Verifier.

axiom Sim1_ll : islossless Sim1.run.


lemma zk_step1 &m E Q p w eps:
   `|Pr[ Sim1.run(p) @ &m : E res.`1 /\ Q res.`2]
      / Pr[Sim1.run(p) @ &m : E res.`1] 
        - Pr[ZK(P,V).main(p,w) @ &m: Q res]| <= eps
  => 0%r <= eps 
  => 0%r < Pr[Sim1.run(p) @ &m : E res.`1]
  => exists (eps' : real),  0%r <= eps' <= eps  
  /\ `|Pr[ Sim1.run(p) @ &m : E res.`1 /\ Q res.`2] 
         / Pr[Sim1.run(p) @ &m : E res.`1] 
                - Pr[ZK(P,V).main(p,w) @ &m: Q res]| = eps'
  /\ (Pr[ Sim1.run(p) @ &m : E res.`1 /\ Q res.`2] 
      = Pr[Sim1.run(p) @ &m : E res.`1]  
        * (Pr[ZK(P,V).main(p,w) @ &m: Q res] - eps')
      \/
      Pr[ Sim1.run(p) @ &m : E res.`1 /\ Q res.`2] 
      = Pr[Sim1.run(p) @ &m : E res.`1]  
        * (Pr[ZK(P,V).main(p,w) @ &m: Q res] + eps')).
proof.
progress.
apply oip3;auto.
qed.


op fevent : event.


require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.

lemma zk_step2 &m E Q p ea :
  Pr[ W(Sim1).whp((fun x => E (fst x)),p,1,ea,(fevent,witness)) 
           @ &m : E res.`1 /\ Q res.`2 ]  
     = big predT
        (fun i => Pr[Sim1.run(p) @ &m : !E res.`1] ^ i 
         * Pr[ Sim1.run(p) @ &m : E res.`1 /\ Q res.`2] )
        (range 0 ea). 
apply (whp_cap_fin_sum Sim1 _ &m (fun x => E (fst x)) (fun x => Q (snd x))).
admit.
admit.
admit.
qed.



lemma big_split_min ['a]:
  forall (P0 : 'a -> bool) (F1 F2 : 'a -> real) (s : 'a list),
    big P0 (fun (i : 'a) => F1 i - F2 i) s = big P0 F1 s - big P0 F2 s.
proof.  progress.
have ->:  - big P0 F2 s
 =  (big P0 (fun x => - (F2 x) ) s).
apply (big_ind2 (fun (x : real) y => (- x) = y) ) .
smt. smt.
progress.
apply big_split.
qed.


lemma zk_step3 &m E Q p w eps ea coeff:
   `|Pr[ Sim1.run(p) @ &m : E res.`1 /\ Q res.`2]
      / Pr[Sim1.run(p) @ &m : E res.`1] 
        - Pr[ZK(P,V).main(p,w) @ &m: Q res]| <= eps
  => 0%r < Pr[Sim1.run(p) @ &m : E res.`1]  
  => 0%r <= eps 
  => exists (eps' : real),  
     coeff = big predT
               (fun i => Pr[Sim1.run(p) @ &m : !E res.`1] ^ i 
                         * Pr[ Sim1.run(p) @ &m : E res.`1])
               (range 0 ea) 
  => 0%r <= eps' <= eps   /\ 
     `|Pr[ W(Sim1).whp(E \o fst,p,1,ea,(fevent,witness)) 
           @ &m : E res.`1 /\ Q res.`2 ]  
         - coeff * Pr[ZK(P,V).main(p,w) @ &m: Q res]| = coeff * eps'.
proof. move => H0 H1 H2.
have :  exists (eps' : real),  0%r <= eps' <= eps  
  /\ `|Pr[ Sim1.run(p) @ &m : E res.`1 /\ Q res.`2] 
         / Pr[Sim1.run(p) @ &m : E res.`1] 
                - Pr[ZK(P,V).main(p,w) @ &m: Q res]| = eps'
  /\ (Pr[ Sim1.run(p) @ &m : E res.`1 /\ Q res.`2] 
      = Pr[Sim1.run(p) @ &m : E res.`1]  
        * (Pr[ZK(P,V).main(p,w) @ &m: Q res] - eps')
      \/
      Pr[ Sim1.run(p) @ &m : E res.`1 /\ Q res.`2] 
      = Pr[Sim1.run(p) @ &m : E res.`1]  
        * (Pr[ZK(P,V).main(p,w) @ &m: Q res] + eps')).
apply (zk_step1 &m). assumption. assumption. assumption.
elim. move => eps' [H3 [H41 H42 ]].
exists eps'.  move => coeffeq.
split. auto.
apply oip4.

rewrite coeffeq.

have ->: Pr[Sim1.run(p) @ &m : ! E res.`1]
  = 1%r - Pr[Sim1.run(p) @ &m :  E res.`1].
  have ->: 1%r = Pr[Sim1.run(p) @ &m :  true].
  byphoare. apply Sim1_ll. auto. auto.
  have ->: Pr[Sim1.run(p) @ &m : true] = Pr[Sim1.run(p) @ &m : E res.`1]
   + Pr[Sim1.run(p) @ &m : !E res.`1]. rewrite Pr[mu_split E res.`1]. 
  simplify. smt. smt.
  have : 0%r <=
bigi predT
  (fun (i : int) =>
     (1%r - Pr[Sim1.run(p) @ &m : E res.`1]) ^ i *
     Pr[Sim1.run(p) @ &m : E res.`1]) 0 ea.
  apply (big_geq0  Pr[Sim1.run(p) @ &m : E res.`1] _ ea). smt.
  smt.

 
case (Pr[ Sim1.run(p) @ &m : E res.`1 /\ Q res.`2] 
      = Pr[Sim1.run(p) @ &m : E res.`1]  
        * (Pr[ZK(P,V).main(p,w) @ &m: Q res] + eps')).
progress. rewrite /(\o).
rewrite zk_step2.
rewrite H. simplify.
have : bigi predT
  (fun (i : int) =>
     Pr[Sim1.run(p) @ &m : ! E res.`1] ^ i *
     (Pr[Sim1.run(p) @ &m : E res.`1] *
      (Pr[ZK(P, V).main(p, w) @ &m : Q res] + eps'))) 0 ea =
coeff * Pr[ZK(P, V).main(p, w) @ &m : Q res] + coeff * eps'.
rewrite coeffeq.
rewrite mulr_suml.
rewrite mulr_suml.
rewrite - big_split.
simplify. smt.
timeout 20. smt.
move => H5.
have : Pr[ Sim1.run(p) @ &m : E res.`1 /\ Q res.`2] 
        = Pr[Sim1.run(p) @ &m : E res.`1]  
          * (Pr[ZK(P,V).main(p,w) @ &m: Q res] - eps').
smt.
progress. rewrite /(\o).
rewrite zk_step2.
rewrite H. simplify.
have : bigi predT
  (fun (i : int) =>
     Pr[Sim1.run(p) @ &m : ! E res.`1] ^ i *
     (Pr[Sim1.run(p) @ &m : E res.`1] *
      (Pr[ZK(P, V).main(p, w) @ &m : Q res] - eps'))) 0 ea =
coeff * Pr[ZK(P, V).main(p, w) @ &m : Q res] - coeff * eps'.
rewrite coeffeq.
rewrite mulr_suml.
rewrite mulr_suml.
rewrite - big_split_min.
simplify. smt.
timeout 20. smt.
qed.


end section.
