require import AllCore List.
require import QR_Basics.


require Iterated_Failure.
clone import Iterated_Failure as IF with type irt <- (qr_c * qr_w),
                                         type rrt <- bool * bool list,
                                         type sbits <- sbits.



require Mywhile.
clone import Mywhile as MW with type irt <- (qr_c * qr_w),
                                         type rrt <- bool * bool list.


require RewBasics.
clone import RewBasics as RW with type sbits <- sbits,
                                  type iat   <- iat,
                                  type iat2  <- (qr_c * qr_w),
                                  type rrt   <- bool * bool list,
                                  type irt   <- (qr_c * qr_w),
                                  op pair_sbits <- pair_sbits,
                                  op unpair <- unpair.
                                         

module type RewVerifierA = {
  proc challenge(Ny : qr_c, c : int) : bool 
  proc summitup(c : int, b : bool, r : int) : bool list 
  proc getState() : sbits
  proc * setState(b : sbits) : unit 
}.


module A(V : RewVerifierA) = {
  module S = Sim1(V)
  proc getState() : sbits = {
    return witness;
  }
  proc setState(s : sbits) = {
    V.setState(s);
    Sim1.result <- witness;
  }

  proc run(i : qr_c * qr_w) : bool * bool list = {
    var r; 
    r <- S.simulate(fst i);
    return r;
  }

}.



section.
declare module V : RewVerifierA {HP,WW,W}.




axiom A_ll : islossless GetRunSet(A(V)).main.
axiom A_ll2 :   islossless A(V).run.
local lemma qrp_zk2_pr (e ja : int) q &m Na ya (wa : qr_w) : 
    0 <= ja - 2 =>
  ja <= e + 1 =>
    IsSqRoot (Na, ya) wa =>
    Pr[ W(A(V)).whp_A(fst, ((Na,ya),wa), 1,e,(false,[])) @ &m :
       W.c = ja /\ (fst res) /\ q (snd res) ]
        = (1%r/2%r)^(ja - 2) * ((1%r/2%r) * Pr[ZK(HP, V).main(Na,ya,wa) @ &m : q res ]).
move => jap1 jap2 isr.

have <-: Pr[ WW(GetRunSet(A(V))).whp(fst,((Na,ya),wa),1,e,(false,[])) @ &m : WW.c = ja /\ fst res /\ q (snd res) ]  
  = Pr[W(A(V)).whp_A(fst, ((Na, ya), wa), 1, e,
      (false, [])) @ &m : W.c = ja /\ res.`1 /\ q res.`2].
byequiv (_: ={glob A, glob V,arg} ==> WW.c{1} = W.c{2} /\ ={res}).
proc. sp.  sim. auto. auto.

apply (whp_cap_fin (GetRunSet(A(V))) A_ll &m fst (fun x => q (snd x)) ((Na,ya),wa) e (false,[]) ja (1%r / 2%r * Pr[ZK(HP, V).main(Na, ya, wa) @ &m : q res]) (fun x => (1%r/2%r)^x)  )  .
auto. auto. auto. simplify.

bypr. progress.   admit.

progress. bypr.
move => &n. elim.  move => ap ge. rewrite ap. simplify.
have ->: Pr[WW(GetRunSet(A(V))).whp(fst, ((Na,ya),wa), 1, ea, (false,[])) @ &n : ! fst res]
 = Pr[W(A(V)).whp_A(fst, ((Na,ya),wa), 1, ea, (false,[])) @ &m : ! fst res].
byequiv (_: ={glob A, glob V,arg} ==> ={res}).
proc. sp. sim. auto. 
auto.

apply (final_zz (A(V)) A_ll2 _ &m) .
admit. 
auto. auto. simplify. 
byphoare. 
proc.

call (simnres V).
admit.
skip. auto. auto. auto. 
admit.
qed.
