require import AllCore.
require import QR_Basics.



require Iterated_Failure.
clone import Iterated_Failure as IF with type irt <- (qr_c * qr_w),
                                         type rrt <- bool,
                                         op MyP <- (fun x => x).


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



local module A = {
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

local lemma A_run_ll : islossless A.run. admitted.


local lemma RewPropA :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.
admitted.
    
local lemma qr_iterated_soundness &m e Na ya :
  0 <= e =>

      ! IsQR (Na, ya) =>
  Pr[ W(A).whp_A(((Na,ya),witness), 1,e,false) @ &m : ! res ] <= ((1%r/2%r) ^ e).
proof. 
progress.
have :   Pr[W(A).whp_A(((Na, ya), witness), 1, e, false) @ &m : !res] <=
  (1%r / 2%r) ^ e. 
apply (final_zz_le A A_run_ll RewPropA &m ((Na, ya),witness) e false).
auto.  auto.
admit.
auto.
qed.
