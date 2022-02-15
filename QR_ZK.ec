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
declare module V : RewVerifierA {HP,WW,W,Sim1}.

lemma RewPropV :  (exists (f : (glob A(V)) -> sbits),
       injective f /\
       (forall &m,
          Pr[A(V).getState() @ &m :
             (glob A(V)) = (glob A(V)){m} /\ res = f (glob A(V)){m}] =
          1%r) /\
       (forall &m (b : sbits) (x : (glob A(V))),
          b = f x => Pr[A(V).setState(b) @ &m : (glob A(V)) = x] = 1%r) /\
       islossless A(V).setState). admitted.



axiom A_ll : islossless GetRunSet(A(V)).main.
axiom A_ll2 :   islossless A(V).run.
axiom V_summitup_ll : islossless V.summitup.

lemma qrp_zk2_pr (e ja : int) q &m Na ya (wa : qr_w) : 
    0 <= ja - 2 =>
  ja <= e + 1 =>
    IsSqRoot (Na, ya) wa => invertible Na ya =>
    Pr[ W(A(V)).whp_A(fst, ((Na,ya),wa), 1,e,(false,[])) @ &m :
       W.c = ja /\ (fst res) /\ q (snd res) ]
    = (1%r/2%r)^(ja - 2) * ((1%r/2%r) * Pr[ZK(HP, V).main(Na,ya,wa) @ &m : q res ]).
    


move => jap1 jap2 isr invr.

have <-: Pr[ WW(GetRunSet(A(V))).whp(fst,((Na,ya),wa),1,e,(false,[])) @ &m : WW.c = ja /\ fst res /\ q (snd res) ]  
  = Pr[W(A(V)).whp_A(fst, ((Na, ya), wa), 1, e,
      (false, [])) @ &m : W.c = ja /\ res.`1 /\ q res.`2].
byequiv (_: ={glob A, glob V,arg} ==> WW.c{1} = W.c{2} /\ ={res}).
proc. sp.  sim. auto. auto.

apply (whp_cap_fin (GetRunSet(A(V))) A_ll &m fst (fun x => q (snd x)) ((Na,ya),wa) e (false,[]) ja (1%r / 2%r * Pr[ZK(HP, V).main(Na, ya, wa) @ &m : q res]) (fun x => (1%r/2%r)^x)  )  .
auto. auto. auto. simplify.

bypr. progress.   
have <-: 
 Pr[A(V).run(z{m0}) @ &m0 : res.`1 /\ q res.`2] = Pr[GetRunSet(A(V)).main(z{m0}) @ &m0 : res.`1 /\ q res.`2].
byequiv (_: ={glob V, glob A, arg} ==>_).

conseq (GetRunSetRewRes (A(V)) RewPropV A_ll2).  progress. smt. auto. auto.
rewrite H.
have ->: Pr[A(V).run(((Na, ya), wa)) @ &m0 : res.`1 /\ q res.`2] 
 = Pr[Sim1(V).simulate(((Na, ya))) @ &m0 : res.`1 /\ q res.`2] .
byequiv.   proc*. inline A(V).run. sp. wp.  
conseq (_: ={glob V} /\ i0.`1{1} = (N,y){2} ==> r0{1} = r{2}). smt. auto.
sim. 
inline*. sim. wp.  skip. progress. smt. smt.  auto. auto.

have ->: 
  Pr[Sim1(V).simulate(Na, ya) @ &m0 : res.`1 /\ q res.`2]
  = Pr[Sim1(V).simulate(Na, ya) @ &m : res.`1 /\ q res.`2].
byequiv (_: ={arg, glob V, glob Sim1} ==> ={glob Sim1, glob V, res} ). sim. auto. auto.

print sim1zk.
apply (sim1zk V).   apply V_summitup_ll. auto. auto.
 
progress. bypr.
move => &n. elim.  move => ap ge. rewrite ap. simplify.
have ->: Pr[WW(GetRunSet(A(V))).whp(fst, ((Na,ya),wa), 1, ea, (false,[])) @ &n : ! fst res]
 = Pr[W(A(V)).whp_A(fst, ((Na,ya),wa), 1, ea, (false,[])) @ &m : ! fst res].
byequiv (_: ={glob A, glob V,arg} ==> ={res}).
proc. sp. sim. auto. 
auto.

apply (final_zz (A(V)) A_ll2 _ &m) .
apply RewPropV.
auto. auto. simplify. 
byphoare. 
proc.

call (simnres V).
apply V_summitup_ll.
skip. auto. auto. auto. 
conseq (dbl1 (A(V)) _  (fun x => true) (glob GetRunSet(A(V))){m} (1%r) _).
apply RewPropV. simplify. conseq A_ll2.

qed.
