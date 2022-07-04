pragma Goals:printall.
require import AllCore DBool Bool List Distr Aux RealExp.
require import Basics.

clone import OneShotSimulator as OSS with op zk_error <= (fun x z => 0%r).



(* one-time simulator  *)


module Sim1(V : RewMaliciousVerifier)  = {

  proc sinit(y : qr_prob) : bool * zmod * zmod = {
    var r,rr,bb;
    (r,rr)  <$ ZNS_dist;    
    bb <$ {0,1};
    return (bb,(rr * if bb then (inv y) else one),r);
  }

  proc run(Ny : qr_prob) : bool * adv_summary  = {
    var r,z,b',b,result, vstat;
    vstat <@ V.getState();
    (b',z,r) <@ sinit(Ny);
    b  <@ V.challenge(Ny,z);
    result <@ V.summitup(Ny,r);
    if(b <> b'){
      V.setState(vstat);
    }
    return (b = b', result);
  }
}.


section.

declare module V <: RewMaliciousVerifier {-HP}.


declare axiom V_summitup_ll : islossless V.summitup.
declare axiom V_challenge_ll : islossless V.challenge.


declare axiom rewindable_V_plus : 
  exists (f : glob V -> sbits),
  injective f /\
  (forall (x : glob V),
    phoare[ V.getState : (glob V) = x ==> (glob V) = x  /\ res = f x ] = 1%r) /\
  (forall (x : glob V),
    hoare[ V.getState : (glob V) = x ==> (glob V) = x  /\ res = f x ]) /\
  islossless V.getState /\
  (forall (x: glob V),
    phoare[V.setState: b = f x ==> glob V = x] = 1%r) /\
  (forall (x: glob V),
    hoare[V.setState: b = f x ==> glob V = x]) /\
  islossless V.setState.

  
lemma sim1_rew_ph : forall (x : (glob V) * (glob Sim1)),
    phoare[ Sim1(V).run :
             ((glob V), (glob Sim1)) = x
                 ==> ! res.`1 => ((glob V), (glob Sim1)) = x] = 1%r.
proof. progress.
exists* (glob V). elim* => V_v.
progress.
elim rewindable_V_plus.
move => fA [s1 [s2 [s3]]] [s4 [ s5 [s6 s7]]].
proc.
seq 1 : (V_v = (glob V) /\ vstat = fA V_v /\
  ((glob V),tt) =
  x).
call (_: true ==> true). auto. skip. auto.
call (s2 V_v).
skip. progress.
wp.
seq 3 : (vstat = fA V_v /\ x.`1 = V_v) 1%r.
call (_:true).  call (_:true). call (_:true). rnd. rnd. skip. auto. skip. auto.
simplify. call V_summitup_ll. call V_challenge_ll.
inline*.  wp. rnd. rnd. wp. skip.  smt.
case (b = b').
rcondf 1. skip. auto. skip. auto.
rcondt 1. skip. auto. call (s5 V_v). skip. auto. 
progress. 
have -> : tt = x.`2. smt.
smt.
hoare. simplify.
call (_:true). call (_:true). call (_:true). rnd. rnd. skip. auto.
skip. auto. auto.  hoare. simplify. 
call (s3 V_v). skip. progress. auto.
qed.




end section.


section.

declare module V <: RewMaliciousVerifier {-HP}.
declare module D <: ZKDistinguisher.

declare axiom rewindable_V_plus2 : 
  exists (f : glob V -> sbits),
  injective f /\
  (forall (x : glob V),
    phoare[ V.getState : (glob V) = x ==> (glob V) = x  /\ res = f x ] = 1%r) /\
  (forall (x : glob V),
    hoare[ V.getState : (glob V) = x ==> (glob V) = x  /\ res = f x ]) /\
  islossless V.getState /\
  (forall (x: glob V),
    phoare[V.setState: b = f x ==> glob V = x] = 1%r) /\
  (forall (x: glob V),
    hoare[V.setState: b = f x ==> glob V = x]) /\
  islossless V.setState.

declare axiom summitup_ll  :  islossless V.summitup.
declare axiom challenge_ll :  islossless V.challenge.
declare axiom D_guess_ll : islossless D.guess.


(* transformed simulator with independent coin flip *)
local module Sim1'  = {
  var result : bool list

  proc sinit() : bool * zmod * zmod  = {
    var r,rr,bb;

    (r,rr)  <$ ZNS_dist;    
    bb <$ {0,1};
    return (bb,rr,r);
  }
    
  proc run(Ny : qr_prob, w : qr_wit) : bool * bool  = {
    var z,r,b',b,ryb,result, rd;
    (b',z,r) <@ sinit();
    b  <@ V.challenge(Ny,z);
    ryb  <- (r * if b then w else one);
    result <@ V.summitup(Ny,ryb);
    rd <@ D.guess(Ny, w, result);    
    return (b = b', rd);
  }

 proc allinone(Ny : qr_prob, w : qr_wit) = {
    var z,r,bb,rr,b',b,ryb,result, rd;
    (r,rr)  <$ ZNS_dist;    
    bb <$ {0,1};
    b' <- bb;
    z <- rr ;
    b  <@ V.challenge(Ny,z);
    ryb  <- (r * if b then w else one);
    result <@ V.summitup(Ny,ryb);
    rd <@ D.guess(Ny, w, result);
    return (b = b', rd);
  }
}.



axiom jk : equiv [ D.guess ~ D.guess : ={arg, glob V} ==> ={res} ].

local lemma qrp_zk2_eq ya wa  : IsSqRoot ya wa =>
  equiv [ZKReal(HP, V, D).run ~ Sim1'.run
         : ={arg, glob V} /\ arg{1} = (ya, wa)
          ==> res{1} = res{2}.`2 ].
move => isqr. proc.
call jk.
inline*. sp.
call (_:true).  simplify.  
wp. simplify. call (_:true).
wp. swap {2} 2 -1.
 rnd . rnd{2}.    skip. progress .
qed.


local lemma exss ya wa : IsSqRoot ya wa /\ unit ya =>
 equiv[ Sim1(V).sinit ~ Sim1'.sinit
   : arg{1} = (ya) /\ ={glob V} ==>
    ={glob V} /\  (res{1}.`1, res{1}.`2) = (res{2}.`1, res{2}.`2)
        /\ (res{1}.`1 = true  => res{1}.`2 = res{1}.`3 * res{1}.`3 * (inv ya) 
                /\ res{1}.`3 * (inv wa)   = res{2}.`3)
        /\ (res{1}.`1 = false => res{1}.`2= res{1}.`3 * res{1}.`3
                /\ res{1}.`2  = res{2}.`2 
                /\ res{1}.`3  = res{2}.`3 ) ].
proof. 
move => [isqr invrtbl]. proc. swap 2 -1.
seq 1 1 : (={bb} /\ (y{1}) = (ya) /\ ={glob V}). rnd.    skip. progress. 
exists* bb{1}. elim*. progress.
wp. case (bb_L = true).     
rnd (fun (x : zmod * zmod) => (x.`1 * inv wa, x.`2 * (inv y{1}) ))
      (fun (x : zmod * zmod) => (x.`1 * wa, x.`2 * y{1} )). skip. progress.
have ->: rrrR = (rrrR.`1, rrrR.`2). smt.
simplify. split. 
  have : unit wa.  smt.
move => iwa.  
have ->:  rrrR.`1 * wa * inv wa
 =  (rrrR.`1  * wa  * inv wa) . smt.
have ->: rrrR.`1 * wa * inv wa = rrrR.`1 * (wa * inv wa).
smt.
smt. 
have ->:  rrrR.`2 * y{1} * inv y{1} 
 =  (rrrR.`2  * y{1}  * inv  y{1}). smt.
have ->: rrrR.`2 * y{1} * inv y{1} = rrrR.`2 * (y{1} * inv y{1}).
smt.
smt. 
apply (d_prop0). auto.
apply (d_prop3).
 have ->: rrrR.`1 * wa * (rrrR.`1 * wa) =
(rrrR.`1 * rrrR.`1) * (wa *  wa). smt.
 have ->: (rrrR.`1 * rrrR.`1) * (wa *  wa)
 = (rrrR.`1 * rrrR.`1) * (wa *  wa). 
smt. 
 have ->: (rrrR.`1 * rrrR.`1)  = (rrrR.`2).
  smt.
have ->: rrrR.`2 * ( wa *  wa)
 = (wa *  wa) * rrrR.`2. 
smt. 
rewrite - isqr. 
smt. 
apply d_prop3. 
have f1 : unit wa. smt.
clear H H0.
 have ->: rrrL.`1 * inv wa * (rrrL.`1 * inv  wa) =
(rrrL.`1 * rrrL.`1) * (inv wa * inv wa). smt.
 have ->: (rrrL.`1 * rrrL.`1) * (inv wa * inv wa)
 = (rrrL.`1 * rrrL.`1) * (inv wa * inv wa). 
smt.
 have ->: (rrrL.`1 * rrrL.`1) = (rrrL.`2).
  smt.
have ->: rrrL.`2  * (inv  wa * inv wa) 
 = (inv wa * inv wa) * rrrL.`2.
smt.
have ->: inv wa * inv wa = inv y{1}. smt.
smt.
have ->: rrrL = (rrrL.`1, rrrL.`2). smt.
simplify. split. 
  have : unit wa. smt.
move => iwa. 
have ->:  rrrL.`1 *  inv wa  * wa
 =  (rrrL.`1  * inv  wa * wa ).
smt.
have ->: rrrL.`1 * inv wa * wa = rrrL.`1 * (wa * inv wa).
smt.
smt.
have ->:  rrrL.`2 * inv y{1} * y{1}
 =  (rrrL.`2  * inv y{1} * y{1}).
smt.
have ->: rrrL.`2 * inv y{1} * y{1} = rrrL.`2 * (y{1} * inv y{1}).
smt.
smt.
smt.
rnd. skip. progress. smt. smt. smt.
smt. 
smt.
qed.

import OMZK.

local lemma qkok ya wa P : IsSqRoot  ya wa /\ unit ya =>
  equiv [ W0(Sim1(V),D).run ~ Sim1'.run
   :   ={glob V,arg} /\  (ya,wa) = (Ny{2},w{2})
       ==>  (fst res{1}.`2) /\ P res{1}.`1 <=> (res{2}.`1 /\ P res{2}.`2) ].
move => [isqr invrtbl]. proc.
inline Sim1(V).run. sp.
seq 2 1 : (={glob V,b',z, Ny,w} 

         /\ Ny{1} = a{1}
         /\ (b'{1} = true => z{1} = r0{1} * r0{1} * (inv ya)
                     /\ r0{1} * (inv wa) = r{2} )
         /\ (b'{2} = false => z{1} = r0{1} * r0{1} /\ r0{1} = r{2})
         /\ ((ya),wa) = (Ny{2},w{2})).
call (exss ya wa). 
elim rewindable_V_plus2.
move => fA [s1 [s2 [s3]]] [s4 [ s5 [s6 s7]]]. 
exists* (glob V){1}. elim*. progress.
call {1} (s2 V_L).
skip. progress. smt.  smt.  
seq 1 1 : (={glob V,b',z,Ny,w} 
         /\ Ny{1} = a{1}
         /\ b0{1} = b{2}
         /\ (b'{1} = true => z{1} = r0{1} * r0{1} * (inv ya)
                     /\ r0{1} * (inv wa) = r{2} )
         /\ (b'{2} = false => z{1} = r0{1} * r0{1} /\ r0{1} = r{2})
         /\ ((ya),wa) = (Ny{2},w{2}) ).
call (_:true). skip. progress. 
sp. simplify.
exists* b'{1}. elim*. progress.
case (b'_L = true).
exists* b0{1}. elim*. progress.
case (b0_L = true). 
call jk. 
wp.  simplify.
case (b0{1} = b'{1}). 
rcondf {1} 2. progress. call (_:true). skip. auto.
call (_:true). skip. progress. smt.
rcondt {1} 2. progress. call (_:true). skip. auto.
conseq (_: b0{1} <> b'{1} ==> true ). smt. smt.
elim rewindable_V_plus2.
move => fA [s1 [s2 [s3]]] [s4 [ s5 [s6 s7]]].  
call {1} s7.
call {1} summitup_ll.
call {2} summitup_ll. skip. auto.
conseq (_: b0{1} <> b'{1} ==> !r{1}.`1 ). smt. smt.
call {1} (_: true ==> true). apply D_guess_ll.
wp. 
call {2} (_: true ==> true). apply D_guess_ll. simplify.
seq 1 1 : (b0{1} <> b'{1}).
call {1} (_: true ==> true). apply summitup_ll.
call {2} (_: true ==> true). apply summitup_ll.  simplify. 
skip. auto.
if{1}.
elim rewindable_V_plus2.
move => fA [s1 [s2 [s3]]] [s4 [ s5 [s6 s7]]].  call {1} s7. skip. auto.
skip. smt.
exists* b0{1}. elim*. progress.
case (b0_L = false).
 call jk. wp.  simplify.
rcondf {1} 2. progress. call (_:true). skip. smt.
call (_:true). skip. progress. smt.
conseq (_: b0{1} <> b'{1} ==>  !r{1}.`1 ). smt. smt.
call {1} D_guess_ll.
call {2} D_guess_ll. wp. simplify.
rcondt {1} 2. progress. call (_:true). skip. auto.
call {1} (_: true ==> true). 
elim rewindable_V_plus2.
move => fA [s1 [s2 [s3]]] [s4 [ s5 [s6 s7]]].  auto.
call {1} summitup_ll.
call {2} summitup_ll.
skip. progress. 
qed.


local lemma ssim ya wa  : IsSqRoot ya wa /\ unit ya =>
 equiv [ W0(Sim1(V),D).run ~ Sim1'.run : ={glob V, glob D, arg} 
           /\  ((ya),wa) = (Ny{2},w{2}) 
       ==> (fst res{1}.`2) = res.`1{2} ].
move => ii.
conseq (qkok ya wa (fun x => true) ii). smt.
progress. smt.
qed.


local lemma sim1'not &m ya wa  : 
     Pr[Sim1'.run(ya, wa) @ &m : ! res.`1] = 1%r/2%r.
proof.
have ->: Pr[Sim1'.run(ya, wa) @ &m : ! res.`1] = Pr[Sim1'.allinone(ya, wa) @ &m : ! res.`1]. 
byequiv. proc. 
call jk. progress.
call (_:true). wp.  simplify.
call (_:true). inline*. wp.  rnd.  rnd. skip. progress. smt. auto. auto.
byphoare. proc. inline*. simplify. 
swap [2..3] 5. wp.
seq 6 : true (1%r) (1%r/2%r) 1%r 0%r.
auto. call D_guess_ll.
call summitup_ll. wp. 
call challenge_ll. wp. rnd.  skip. smt. 
rnd. skip. progress. smt. 
exfalso. auto. auto.  auto. auto.
qed.

local lemma sim1'notnot &m ya wa: 
     Pr[Sim1'.run(ya, wa) @ &m :  res.`1] = 1%r/2%r.
proof.
have ->: Pr[Sim1'.run(ya, wa) @ &m :  res.`1] = Pr[Sim1'.allinone(ya, wa) @ &m :  res.`1].
byequiv. proc.
call jk. progress.
call (_:true). wp.  simplify.
call (_:true). inline*. wp.  rnd.  rnd. skip. progress. smt. auto. auto.
byphoare. proc. inline*. simplify.
swap [2..3] 5. wp.
seq 6 : true (1%r) (1%r/2%r) 1%r 0%r.
auto. call D_guess_ll.
call summitup_ll. wp.
call challenge_ll. wp. rnd. skip. smt.
rnd. skip. progress.
case (b{hr}). smt.
smt.
exfalso. auto. auto.  auto. auto.
qed.



lemma simnres ya wa : IsSqRoot ya wa /\ unit ya =>
  phoare[ W0(Sim1(V),D).run : arg = (ya, wa) ==> ! (fst res.`2) ] = (1%r/2%r).
move => ii.
bypr. progress.
rewrite H. clear H.
have <-: Pr[Sim1'.run(ya,wa) @ &m : ! res.`1] = inv 2%r.
apply sim1'not.
byequiv (_: _ ==> (fst res.`2){1} = res.`1{2}). 
conseq (ssim ya wa ii). auto. auto. auto. 
smt.  auto. smt.
qed.

lemma simnresnotnot ya wa : IsSqRoot ya wa /\ unit ya =>
  phoare[ W0(Sim1(V),D).run : arg = (ya, wa) ==>  (fst res.`2) ] = (1%r/2%r).
move => ii.
bypr. progress.
rewrite H. clear H.
have <-: Pr[Sim1'.run(ya,wa) @ &m :  res.`1] = inv 2%r.
apply sim1'notnot.
byequiv (_: _ ==> (fst res.`2){1} = res.`1{2}). 
conseq (ssim ya wa ii). auto. auto. auto. 
smt.  auto. smt.
qed.

  
    
local lemma qrp_zk2_pr_l &m ya wa : IsSqRoot ya wa =>
    Pr[ZKReal(HP, V,D).run(ya,wa) @ &m : res  ] = Pr[ Sim1'.run(ya,wa) @ &m : res.`2  ].
proof. move => isqr. byequiv.
conseq (_: _ ==> res{1} = res{2}.`2). progress.
conseq (qrp_zk2_eq ya wa  _). auto. auto. auto. auto.
smt. auto. auto. auto.
qed.



local lemma sd &m ya wa  : 
     Pr[ Sim1'.run(ya,wa) @ &m : res.`1 /\ res.`2 ]
    = (1%r/2%r) * Pr[ Sim1'.run(ya,wa) @ &m : res.`2 ].
have : Pr[ Sim1'.run(ya,wa) @ &m : res.`1 /\ res.`2 ]
 = Pr[ Sim1'.run(ya,wa) @ &m : !res.`1 /\ res.`2 ].
byequiv (_: ={glob Sim1',arg} ==> _).  
proc.  inline*.
call jk. wp. 
call (_:true). wp. 
call (_:true). wp. 
rnd (fun x => !x). rnd. wp. skip. progress.
smt. smt. auto. auto.
have ->: Pr[Sim1'.run(ya, wa) @ &m : res.`2] =
 Pr[Sim1'.run(ya, wa) @ &m : res.`1 /\ res.`2] +
   Pr[Sim1'.run(ya, wa) @ &m : ! res.`1 /\ res.`2].
rewrite Pr[mu_split res.`1]. 
have ->: Pr[Sim1'.run(ya, wa) @ &m : res.`2 /\ res.`1]
 = Pr[Sim1'.run(ya, wa) @ &m : res.`1 /\ res.`2]. smt.
have ->: Pr[Sim1'.run(ya, wa) @ &m : res.`2 /\ !res.`1]
 = Pr[Sim1'.run(ya, wa) @ &m : !res.`1 /\ res.`2]. smt.
auto.
move => q.
rewrite - q. smt.
qed.
 


lemma sim1zk &m ya wa :
  IsSqRoot ya wa /\ unit ya =>
    Pr[W0(Sim1(V), D).run(ya, wa) @ &m : fst res.`2 /\ res.`1]
     = Pr[ZKReal(HP, V, D).run(ya, wa) @ &m : res] / 2%r.
proof.     
move => ii.
have ->:     Pr[W0(Sim1(V), D).run(ya, wa) @ &m : fst res.`2 /\ res.`1]
 = Pr[Sim1'.run(ya,wa) @ &m : res.`1 /\ res.`2].
byequiv. 
conseq (qkok ya wa (fun x => x) _). progress;smt. auto. auto.
auto. rewrite (sd &m ya wa).
rewrite (qrp_zk2_pr_l &m ya wa). smt. auto.
qed.
    

lemma sim1assc &m stat (w : qr_wit) : 
 IsSqRoot stat w /\ unit stat =>
 Pr[Sim1(V).run(stat) @ &m : res.`1] = 1%r/2%r.
proof. progress.
have ->: Pr[Sim1(V).run(stat) @ &m : res.`1] 
  = Pr[W0(Sim1(V), D).run(stat, w) @ &m : (fst res.`2) ].
byequiv (_: _ ==> (fst res{1} = fst res.`2{2})).
proc. simplify.
 inline*. 
call {2} D_guess_ll. wp. simplify.
sim. auto.  smt.   smt. smt.
byphoare (_: arg = (stat, w) ==> _). 
conseq (simnresnotnot stat w  _). auto. auto.  auto.
qed.

lemma sim1_prop &m (p : qr_prob) (w : qr_wit) :
   IsSqRoot p w /\ unit p =>  
    `|Pr[W0(Sim1(V), D).run(p, w) @ &m : fst res.`2 /\ res.`1] /
         Pr[Sim1(V).run(p) @ &m : fst res] 
              - Pr[ ZKD(HP,V,D).main(p,w) @ &m : res ]| = 0%r. 
progress.
rewrite sim1zk.  auto.
rewrite (sim1assc &m p w). auto.
simplify.
have ->: Pr[ZKReal(HP, V, D).run(p, w) @ &m : res] * 2%r / 2%r
 = Pr[ZKReal(HP, V, D).run(p, w) @ &m : res].
smt.
have : Pr[ZKReal(HP, V, D).run(p, w) @ &m : res] =
  Pr[ZKD(HP, V, D).main(p, w) @ &m : res] .
byequiv. proc. call jk. sim. smt. smt.  auto. smt.
qed.


end section.

