require import AllCore.

require import QR_Basics.
import ZK_defs.


require While_not_b_proc.
clone import While_not_b_proc as IF with type iat <- (qr_prob * qr_wit),
                                         type rt <- bool.


                                         
section.

declare module P : Prover {M,HV}.


axiom P_commit_ll   : islossless P.commit.
axiom P_response_ll : islossless P.response.

(* 
- argument order for prover and verifier
- e + 1
*)
lemma qr_iterated_soundness &m e Na ya :
  0 <= e => ! IsQR (Na, ya) =>
    Pr[ M(Correct(P,HV)).whp(((Na,ya),witness), fun x => !x, 1,e+1,true) @ &m : res ]
       <= ((1%r/2%r) ^ (e + 1)).
proof. 
progress.
have :  phoare[ M(Correct(P,HV)).whp : arg = (((Na,ya),witness), fun x => !x, 1,e+1,true) ==> res ] <= ((1%r/2%r) ^ (e+1)).
conseq (asdsadq_le (Correct(P,HV)) _ (1%r/2%r) ((Na,ya),witness) [!] true _ _ e _) .
proc. inline*. wp.  call P_response_ll. wp.  rnd. wp. call P_commit_ll. skip.  smt.
simplify.
conseq (qr_sound_ph P _ _ Na ya H0). smt.
apply P_commit_ll.
apply P_response_ll.
auto.
assumption.
progress.
byphoare (_: arg = (((Na, ya), witness), [!], 1, e + 1, true) ==> _).
conseq H1. auto.  auto.
qed.


lemma qr_iterated_completeness &m e Na ya wa :
  IsSqRoot (Na, ya) wa /\ invertible Na ya =>
   0 <= e =>
     Pr[ M(Correct(HP,HV)).whp(((Na,ya),wa), fun x => !x, 1,e+1,true) @ &m : res ]
        = 1%r.
proof. 
progress.
  have :  phoare[ M(Correct(HP,HV)).whp : arg = (((Na,ya),wa), fun x => !x, 1,e+1,true) ==> res ]
    = ((1%r) ^ (e+1)).
conseq (asdsadq (Correct(HP,HV)) _ (1%r) ((Na,ya),wa) [!] true _ _ e _).
proc. inline*. wp.  simplify. rnd. wp. rnd.  simplify.  wp.  skip.  smt.
simplify.
conseq (qr_complete_ph  Na ya wa _). smt. auto.
auto.
assumption.
progress.
byphoare (_: arg = (((Na, ya), wa), [!], 1, e + 1, true) ==> _).
conseq H2. auto.  auto. smt.  smt.  auto.
qed.
    
end section.



lemma zk_base_def_1 (a r b c : real) : 
  `| a/r - b | <= c => a/r >= b - c .
smt.
qed.




lemma zk_base_def_2 (a r b c : real) : 
  r > 0%r =>
  `| a/r - b | <= c => a >= (b - c) * r .
have fact : forall (a r b : real),    r > 0%r =>  a / r >= b => a >= b * r.
smt.
smt.  
qed.




