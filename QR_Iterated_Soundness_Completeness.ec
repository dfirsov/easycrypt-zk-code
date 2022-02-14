require import AllCore.
require import QR_Basics.



require Iterated_Failure.
clone import Iterated_Failure as IF with type irt <- (qr_c * qr_w),
                                         type rrt <- bool,
                                         type sbits <- sbits.


module type RewProver = {
  proc commit(Ny : qr_c, w : int) : int
  proc response(b : bool) : int
  proc getState() : sbits
  proc * setState(b : sbits) : unit 
}.

                                         
section.

declare module P : RewProver {W,HV,Correct}.



axiom P_commit_ll   : islossless P.commit.
axiom P_response_ll : islossless P.response.

module A(P : RewProver) = {
  module C = Correct(P,HV)
  proc getState() : sbits = {
    return witness;
  }

  proc setState(s : sbits) : unit = {
    (Correct.c,Correct.b,Correct.r, Correct.result,HV.n,HV.y) <- (witness, witness, witness, witness, witness, witness);
    P.setState(s);
  }

  proc run(i : qr_c * qr_w) : bool = {
    var r;
    r <- C.main(i.`1, i.`2);
    return r;
  }
  
}.

local lemma A_run_ll : islossless A(P).run. admitted.
local lemma AHP_run_ll : islossless A(HP).run. admitted.

local lemma RewPropA :
  exists (f : glob A(P) -> sbits),
  injective f /\
  (forall &m, Pr[ A(P).getState() @ &m : (glob A(P)) = ((glob A(P)){m})
                                   /\ res = f ((glob A(P)){m} ) ] = 1%r) /\
  (forall &m b (x: glob A(P)), b = f x =>
    Pr[A(P).setState(b) @ &m : glob A(P) = x] = 1%r) /\
  islossless A(P).setState.
admitted.

local lemma RewPropAHP :
  exists (f : glob A(HP) -> sbits),
  injective f /\
  (forall &m, Pr[ A(HP).getState() @ &m : (glob A(HP)) = ((glob A(HP)){m})
                                   /\ res = f ((glob A(HP)){m} ) ] = 1%r) /\
  (forall &m b (x: glob A(HP)), b = f x =>
    Pr[A(HP).setState(b) @ &m : glob A(HP) = x] = 1%r) /\
  islossless A(HP).setState.
admitted.
  
local lemma qr_iterated_soundness &m e Na ya :
  0 <= e =>
      ! IsQR (Na, ya) =>
  Pr[ W(A(P)).whp_A(fun x => !x, ((Na,ya),witness), 1,e,true) @ &m : res ] <= ((1%r/2%r) ^ e).
proof. 
progress.
have :   Pr[W(A(P)).whp_A(fun x => !x, ((Na, ya), witness), 1, e, true) @ &m : !!res] <=
  (1%r / 2%r) ^ e. 
apply (final_zz_le (A(P)) A_run_ll RewPropA &m (1%r/2%r) (fun x => !x) ((Na, ya),witness) e true).
auto.  auto.
simplify.
have ->: Pr[A(P).run((Na, ya), witness) @ &m : res]
 = Pr[Correct(P,HV).main((Na,ya),witness) @ &m : res].
byequiv (_: ={glob P,glob HV,arg} ==> _). proc*.
inline A(P).run. wp. sp. sim. auto.  auto.
byphoare (_: arg = ((Na, ya), witness) ==> _).
print qr_sound_ph.
conseq (qr_sound_ph P P_commit_ll P_response_ll Na ya H0).
auto. auto. simplify. auto.
qed.


local lemma qr_iterated_completeness wa &m e Na ya :
    IsSqRoot (Na, ya) wa =>
    invertible Na ya =>
    0 <= e =>
  Pr[ W(A(HP)).whp_A(fun x => !x, ((Na,ya),wa), 1,e,true) @ &m : res ] = 1%r.
progress.
have : Pr[W(A(HP)).whp_A(fun x => !x, ((Na, ya), wa), 1, e, true) @ &m : !!res] = 1%r ^ e. 
apply (final_zz (A(HP)) AHP_run_ll RewPropAHP &m (1%r) (fun x => !x) ((Na, ya),wa) e true).
auto.  auto.
simplify.
have ->: Pr[A(HP).run((Na, ya), wa) @ &m : res]
 = Pr[Correct(HP,HV).main((Na,ya),wa) @ &m : res].
byequiv (_: ={glob HP,glob HV,arg} ==> _). proc*.
inline A(HP).run. wp. sp. simplify. sim. auto.  auto.
byphoare (_: arg = ((Na, ya), wa) ==> _).
conseq (qr_complete_ph Na ya wa H H0 ).
auto. auto. smt.
qed.
