pragma Goals:printall.
require import AllCore DBool Bool List Distr Int IntDiv Aux.

require import Generic_Defs_thy.

(* https://crypto.stanford.edu/pbc/notes/numbertheory/qr.html *)


(*  
replace IsQR with IsSqRoot ((N, y), w)
add invertability assumption into qr_prop7
*)


(* QR theory  *)

require import ZModP.
clone include ZModRing.         (* in ZModField it is efficiently computable *)

type qr_prob = zmod.
type qr_wit  = zmod.
type qr_com  = zmod.
type qr_resp = zmod.


op IsSqRoot (Ny : qr_prob) (w : qr_wit) = Ny  = (w * w).
op IsQR (Ny : qr_prob) = exists w, IsSqRoot Ny w /\ unit Ny.


op ZNS_dist :  (zmod * zmod) distr.



axiom d_prop0  : is_uniform (ZNS_dist).
axiom d_prop1 r rr :  (r, rr) \in ZNS_dist => r * r = rr.
axiom d_prop3 (r rr : zmod) :  r * r = rr => (r, rr) \in ZNS_dist.
axiom d_prop4  r rr :  (r, rr) \in ZNS_dist => unit rr.
axiom d_prop5 : weight (ZNS_dist) = 1%r.


axiom qr_prop1 (x : zmod) : unit  x => x * (inv x)  = one.
axiom qr_prop2 (x y w : zmod) : unit y => IsSqRoot (y) w => unit w.
axiom qr_prop3 (w : zmod) : unit  w => inv  (w * w) = (inv w) * (inv w).
axiom qr_prop5 (x y r : zmod) : IsQR x => unit x => !IsQR y => unit y => x * y  <> r * r.

axiom qr_prop11 (x : zmod) : unit x => (inv x) * x = one.


(* Honest Vrifier  *)
op qr_verify (p : qr_prob) (c : qr_com) (b : bool) (r : qr_resp) : bool =
  if b then unit c /\ unit p /\ c * p = r * r 
  else unit c /\ c = r * r.

op verify_transcript = fun p (x : qr_com * bool * qr_resp) => qr_verify p x.`1 x.`2 x.`3.
op soundness_relation    = fun Ny w => IsSqRoot Ny w /\ unit Ny.
op completeness_relation = fun Ny w => IsSqRoot Ny w /\ unit Ny.
op zk_relation           = fun Ny w => IsSqRoot Ny w /\ unit Ny.

clone include ZKProtocol with 
  type statement       <- qr_prob,
  type commitment      <- qr_com,  
  type witness         <- qr_wit,
  type response        <- qr_resp,
  type challenge       <- bool,
  op challenge_set     <-  (false :: true :: []),
  op verify_transcript <- verify_transcript,
  op soundness_relation    <- soundness_relation,
  op completeness_relation <- completeness_relation,
  op zk_relation           <- zk_relation.


(* Honest Prover  *)
module HonestProver : HonestProver = {
  var r,rr, y, w : zmod

  proc commitment(Ny1 : qr_prob, w1 : qr_wit) : zmod = {  
    (y,w) <- (Ny1, w1);
    (r,rr) <$ ZNS_dist;
    return rr;
  }

  proc response(b : bool) : qr_resp = {
    return (r * (if b then w else one));
 } 
}.





(* local lemma qr_sound_ph_loc Na ya : *)
(*  !IsQR (Na, ya) => phoare [ CorrectL(P,HV).run : arg = ((Na,ya),witness) ==> res ] <= (1%r/2%r). *)
(* proof. move => qra. *)
(* proc. inline*.  *)
(* wp. *)
(* seq 4 : ((Ny) = (Na,ya) /\ HV.y = Ny.`2 /\ HV.n = Ny.`1) (1%r) (1%r/2%r) (0%r) (1%r).  auto. *)
(* auto. *)
(* exists* CorrectL.c. elim*. move => cv. *)
(* case (!IsQR (Na, cv)). *)
(* seq 1 : (!HV.b) (1%r/2%r) (0%r) (1%r/2%r) (1%r) (cv = CorrectL.c /\ Ny = (Na,ya) /\ HV.y = Ny.`2 /\ HV.n = Ny.`1 /\ !IsQR (Na, cv)). *)
(* rnd.  skip. auto. *)
(* hoare. call (_:true ==> true). auto. *)
(* wp. auto. progress. rewrite H0. simplify.    *)
(* have : forall (w : int), CorrectL.c{hr} %% HV.n{hr} <> w * w %% HV.n{hr}. clear qra H0.  *)
(*    move => w.   *)
(*   case (CorrectL.c{hr} %% HV.n{hr} = w * w %% HV.n{hr}). move => ass. *)
(*   simplify. apply H. rewrite /IsQR. exists w. rewrite /IsSqRoot. apply ass. auto. *)
(* progress. smt.  *)
(* simplify. *)
(* rnd. skip. smt. *)
(* conseq (_: _ ==> true). call (_: true ==> true). auto.  *)
(* wp. skip. auto. auto. *)
(*   simplify. *)
(* seq 1 : (HV.b) (1%r/2%r) (0%r) (1%r/2%r) (1%r) (cv = CorrectL.c /\ (Ny) = (Na,ya) /\ IsQR (Na, cv) /\ HV.y = Ny.`2 /\ HV.n = Ny.`1).  *)
(* rnd. skip. auto. *)
(* hoare.  *)
(* call (_:true ==> true). auto.   *)
(* wp. skip. progress. rewrite H0. simplify.  *)
(* smt (qr_prop5). *)
(* rnd. skip. progress. smt. *)
(* conseq (_: _ ==> true). call (_:true ==> true). auto. *)
(* wp. skip. auto. auto. *)
(* hoare. *)
(* simplify. auto. call (_ : true ==> true).  auto. skip. auto. auto. *)
(* qed. *)

(* lemma qr_sound_ph Na ya : *)
(*  !IsQR (Na, ya) => phoare [ Correct(P,HV).run : arg = ((Na,ya),witness) ==> res ] <= (1%r/2%r). *)
(* progress. *)
(* bypr. progress. rewrite H0. simplify. *)
(* clear H0. *)
(* have ->: Pr[Correct(P, HV).run((Na, ya), witness) @ &m : res] *)
(*  = Pr[CorrectL(P, HV).run((Na, ya), witness) @ &m : res]. *)
(* byequiv. sim. auto. smt. auto. auto. *)
(* byphoare (_: arg = ((Na, ya), witness) ==> _). *)
(* apply (qr_sound_ph_loc Na ya). auto. auto. auto. *)
(* qed. *)



(* end section. *)


(* (* one-time simulator  *) *)
(* module Sim1(V : Verifier)  = { *)


(*   proc sinit(N : int, y : int) : bool * int * int = { *)
(*     var r,rr,bb; *)
(*     (r,rr)  <$ ZNS_dist N;     *)
(*     bb <$ {0,1}; *)
(*     return (bb,(rr * if bb then (inv N y) else 1) %% N,r); *)
(*   } *)

(*   proc simulate(Ny : int * int) : bool * sbits  = { *)
(*     var r,z,b',b,ryb,result; *)
(*     (b',z,r) <- sinit(Ny); *)
(*     b  <- V.challenge(Ny,z);    *)
(*     ryb  <- r %% Ny.`1; *)
(*     result <- V.summitup(z,ryb);  *)
(*     return (b = b', result);     *)
(*   } *)
(* }. *)


(* section. *)

(* declare module V : Verifier {HP}. *)

(* axiom summitup_ll  :  islossless V.summitup. *)
(* axiom challenge_ll :  islossless V.challenge. *)

(* (* transformed simulator with independent coin flip *) *)
(* local module Sim1'  = { *)
(*   var result : bool list *)

(*   proc sinit(N : int, y : int) : bool * int * int  = { *)
(*     var r,rr,bb; *)
(*     (r,rr)  <$ ZNS_dist N;     *)
(*     bb <$ {0,1}; *)
(*     return (bb,rr %% N,r); *)
(*   } *)
    
(*   proc simulate(Ny : int * int, w : int) : bool * sbits  = { *)
(*     var z,r,b',b,ryb,result; *)
(*     (b',z,r) <- sinit(Ny); *)
(*     b  <- V.challenge(Ny,z); *)
(*     ryb  <- (r * if b then w else 1) %% Ny.`1; *)
(*     result <- V.summitup(z,ryb); *)
(*     return (b = b', result); *)
(*   } *)

(*  proc allinone(Ny : int * int, w : int) = { *)
(*     var z,r,bb,rr,b',b,ryb,result; *)
(*     (r,rr)  <$ ZNS_dist Ny.`1;     *)
(*     bb <$ {0,1}; *)
(*     b' <- bb; *)
(*     z <- rr %%Ny.`1; *)
(*     b  <- V.challenge(Ny,z); *)
(*     ryb  <- (r * if b then w else 1) %% Ny.`1; *)
(*     result <- V.summitup(z,ryb); *)
(*     return (b = b', result); *)
(*   } *)
(* }. *)



(* local lemma qrp_zk2_eq Na ya wa : IsSqRoot (Na, ya) wa => *)
(*   equiv [ZK(HP, V).main ~ Sim1'.simulate *)
(*          : ={arg, glob V} /\ arg{1} = ((Na, ya), wa) *)
(*           ==> res{1} = res{2}.`2 ]. *)
(* move => isqr. proc. *)
(* inline*. sp. *)
(* call (_:true). *)
(* wp. call (_:true). *)
(* wp. swap {2} 2 -1. *)
(* rnd. rnd {2}. skip. progress.  *)
(* smt (d_prop2). *)
(* qed. *)



(* local lemma exss Na ya wa : IsSqRoot (Na, ya) wa /\ invertible Na ya => *)
(*  equiv[ Sim1(V).sinit ~ Sim1'.sinit *)
(*    : ={arg} /\ arg{1} = (Na,ya) ==> *)
(*        (res{1}.`1, res{1}.`2) = (res{2}.`1, res{2}.`2) *)
(*         /\ (res{1}.`1 = true  => res{1}.`2 %% Na = res{1}.`3 * res{1}.`3 * (inv Na ya) %% Na *)
(*                 /\ res{1}.`3 * (inv Na wa) %% Na  = res{2}.`3 %% Na ) *)
(*         /\ (res{1}.`1 = false => res{1}.`2 %% Na = res{1}.`3 * res{1}.`3 %% Na *)
(*                 /\ res{1}.`2  = res{2}.`2  *)
(*                 /\ res{1}.`3  = res{2}.`3 ) ]. *)
(* move => [isqr invrtbl]. proc. swap 2 -1. *)
(* seq 1 1 : (={N,y,bb} /\ (N{1},y{1}) = (Na,ya)). rnd. skip. auto. *)
(* exists* bb{1}. elim*. progress. *)
(* wp. case (bb_L = true).      *)
(* rnd (fun (x : int * int) => (x.`1 * inv N{1} wa %% N{1}, x.`2 * (inv N{1} y{1}) %% N{1} )) *)
(*       (fun (x : int * int) => (x.`1 * wa %% N{1}, x.`2 * y{1} %% N{1})). skip. progress. *)
(* have ->: rrrR = (rrrR.`1 %% N{2}, rrrR.`2 %% N{2}). smt (d_prop2). *)
(* simplify. split.  *)
(*   have : invertible N{2} wa.  smt. *)
(* move => iwa.  *)
(* have ->:  rrrR.`1 %% N{2} * wa %% N{2} * inv N{2} wa %% N{2} *)
(*  =  (rrrR.`1  * wa  * inv N{2} wa) %% N{2}. *)
(* smt (modzMml modzMmr modzMm). *)
(* have ->: rrrR.`1 * wa * inv N{2} wa = rrrR.`1 * (wa * inv N{2} wa). *)
(* smt. *)
(* smt (modzMml modzMmr modzMm qr_prop1). *)
(* have ->:  rrrR.`2 %% N{2} * y{2} %% N{2} * inv N{2} y{2} %% N{2} *)
(*  =  (rrrR.`2  * y{2}  * inv N{2} y{2}) %% N{2}. *)
(* smt (modzMml modzMmr modzMm). *)
(* have ->: rrrR.`2 * y{2} * inv N{2} y{2} = rrrR.`2 * (y{2} * inv N{2} y{2}). *)
(* smt. *)
(* smt (modzMml modzMmr modzMm qr_prop1). *)
(* apply (d_prop0 N{2}). auto. *)
(* apply (d_prop3 N{2}). *)
(*  have ->: rrrR.`1 * wa * (rrrR.`1 * wa) = *)
(* (rrrR.`1 * rrrR.`1) * (wa *  wa). smt. *)
(*  have ->: (rrrR.`1 * rrrR.`1) * (wa *  wa) %%N{2} *)
(*  = (rrrR.`1 * rrrR.`1) %%N{2} * ( wa *  wa) %%N{2}.  *)
(* smt (modzMml modzMmr modzMm). *)
(*  have ->: (rrrR.`1 * rrrR.`1) %%N{2} = (rrrR.`2) %%N{2}. *)
(*   smt. *)
(* have ->: rrrR.`2 %% N{2} * ( wa *  wa) %% N{2} *)
(*  = ( wa *  wa) %% N{2} * rrrR.`2 %% N{2}.  *)
(* smt (modzMml modzMmr modzMm). *)
(* rewrite - isqr.  *)
(* smt (modzMml modzMmr modzMm). *)
(* apply d_prop3.  *)
(* have f1 : invertible N{2} wa. smt. *)
(* clear H H0. *)
(*  have ->: rrrL.`1 * inv N{2} wa * (rrrL.`1 * inv N{2} wa) = *)
(* (rrrL.`1 * rrrL.`1) * (inv N{2} wa * inv N{2} wa). smt. *)
(*  have ->: (rrrL.`1 * rrrL.`1) * (inv N{2} wa * inv N{2} wa) %%N{2} *)
(*  = (rrrL.`1 * rrrL.`1) %%N{2} * (inv N{2} wa * inv N{2} wa) %%N{2}.  *)
(* smt (modzMml modzMmr modzMm). *)
(*  have ->: (rrrL.`1 * rrrL.`1) %%N{2} = (rrrL.`2) %%N{2}. *)
(*   smt. *)
(* have ->: rrrL.`2 %% N{2} * (inv N{2} wa * inv N{2} wa) %% N{2} *)
(*  = (inv N{2} wa * inv N{2} wa) %% N{2} * rrrL.`2 %% N{2}. *)
(* smt (modzMml modzMmr modzMm). *)
(* have ->: inv N{2} wa * inv N{2} wa %% N{2} *)
(*  = inv N{2} y{2} %% N{2}.  *)
(* rewrite -  (qr_prop3 N{2} y{2} wa).    auto. *)
(* auto. rewrite - isqr. smt (qr_prop4).  *)
(* smt (modzMml modzMmr modzMm). *)
(* have ->: rrrL = (rrrL.`1 %% N{2}, rrrL.`2 %% N{2}). smt (d_prop2). *)
(* simplify. split.  *)
(*   have : invertible N{2} wa.  smt. *)
(* move => iwa.  *)
(* have ->:  rrrL.`1 %% N{2} *  inv N{2} wa %% N{2} * wa %% N{2} *)
(*  =  (rrrL.`1  * inv N{2} wa * wa ) %% N{2}. *)
(* smt (modzMml modzMmr modzMm). *)
(* have ->: rrrL.`1 * inv N{2} wa * wa = rrrL.`1 * (wa * inv N{2} wa). *)
(* smt. *)
(* smt (modzMml modzMmr modzMm qr_prop1). *)
(* have ->:  rrrL.`2 %% N{2} *  inv N{2} y{2} %% N{2} * y{2} %% N{2} *)
(*  =  (rrrL.`2  * inv N{2} y{2} * y{2} ) %% N{2}. *)
(* smt (modzMml modzMmr modzMm). *)
(* have ->: rrrL.`2 * inv N{2} y{2} * y{2} = rrrL.`2 * (y{2} * inv N{2} y{2}). *)
(* smt. *)
(* smt (modzMml modzMmr modzMm qr_prop1). *)
(* smt. *)
(* have ->: rrrL.`2 * inv N{2} y{2} %% N{2} %% N{2}  *)
(*   = rrrL.`2 * inv N{2} y{2} %% N{2} . smt. *)
(* have ->:  rrrL.`2 * inv N{2} y{2} %% N{2} *)
(*      = rrrL.`2 %%N{2} * inv N{2} y{2} %% N{2}. smt.   *)
(* have <-: rrrL.`1 * rrrL.`1 %%N{2} = rrrL.`2 %%N{2} . smt.   *)
(* smt (modzMml modzMmr modzMm d_prop1). *)
(* smt.  *)
(* rnd. skip. progress. smt. smt. smt. *)
(* have ->: rrrL.`2  %% N{2} %% N{2}  *)
(*   = rrrL.`2  %% N{2} . smt. *)
(* smt (d_prop1). *)
(* qed. *)


(* local lemma qkok Na ya wa P : IsSqRoot (Na, ya) wa /\ invertible Na ya => *)
(*   equiv [ Sim1(V).simulate ~ Sim1'.simulate *)
(*    :   ={glob V} /\ (Na,ya) = (Ny{1}) /\ ((Na,ya),wa) = (Ny{2},w{2}) *)
(*        ==> (res{1}.`1 /\ P res{1}.`2) <=> (res{2}.`1 /\ P res{2}.`2) ]. *)
(* move => [isqr invrtbl]. proc. *)
(* seq 1 1 : (={Ny,glob V,b',z}  *)
(*          /\ (b'{1} = true => z{1} %% Na = r{1} * r{1} * (inv Na ya) %% Na *)
(*                      /\ r{1} * (inv Na wa) %% Na = r{2} %% Na ) *)
(*          /\ (b'{2} = false => z{1} %% Na = r{1} * r{1} %% Na /\ r{1} = r{2}) *)
(*          /\ ((Na, ya),wa) = (Ny{2},w{2}) ). *)
(* call (exss Na ya wa). skip. progress. smt.  smt.      *)
(* seq 1 1 : (={b,Ny,glob V,b',z}  *)
(*          /\ (b'{1} = true => z{1} %% Na = r{1} * r{1} * (inv Na ya) %% Na *)
(*                      /\ r{1} * (inv Na wa) %% Na = r{2} %% Na ) *)
(*          /\ (b'{2} = false => z{1} %% Na = r{1} * r{1} %% Na /\ r{1} = r{2}) *)
(*          /\ ((Na, ya),wa) = (Ny{2},w{2}) ). *)
(* call (_:true). skip. progress. *)
(* exists* b'{1}. elim*. progress. *)
(* case (b'_L = true). *)
(* exists* b{1}. elim*. progress. *)
(* case (b_L = true).     *)
(* seq 1 1 : (={ryb,b,Ny,glob V,b',z}  *)
(*          /\ (b'{1} = true => z{1} %% Na = r{1} * r{1} * (inv Na ya) %% Na *)
(*                      /\ r{1} * (inv Na wa) %% Na = r{2} %% Na ) *)
(*          /\ (b'{2} = false => z{1} %% Na = r{1} * r{1} %% Na /\ r{1} = r{2}) *)
(*          /\ ((Na, ya),wa) = (Ny{2},w{2}) ). *)
(* wp. skip. progress.     *)
(* have : r{1} * inv Na w{2} %% Na = r{2} %% Na.  smt. *)
(* move => qq. clear H H0.  *)
(* have : r{1} * inv Na w{2} %% Na * w{2} = r{2} %% Na * w{2}. *)
(* smt. clear qq. move => qq.  *)
(* have : r{1} * inv Na w{2} %% Na * w{2} %% Na = r{2} %% Na * w{2} %% Na. *)
(* smt. clear qq. move => qq. *)
(* have : invertible Na w{2}. smt. *)
(* move => iwa. *)
(* have <-: r{1} * inv Na w{2} %% Na * w{2} %% Na = r{1} %% Na. *)
(*   have ->: r{1} * inv Na w{2} %% Na * w{2} %% Na *)
(*           = r{1} * inv Na w{2} * w{2} %% Na. *)
(* smt (modzMml modzMmr modzMm qr_prop1). *)
(*   have ->: r{1} * inv Na w{2} * w{2} = r{1} * (inv Na w{2} * w{2}). *)
(*   smt . *)
(*       smt (modzMml modzMmr modzMm qr_prop11). *)
(*       smt (modzMml modzMmr modzMm ). *)
(*          smt. smt. *)
(* auto. call (_:true). skip. progress. sp. *)
(* conseq (_: b{1} <> b'{1} ==> b{1} <> b'{1}). smt. smt. *)
(* call {1}  (_: true ==> true). apply summitup_ll.  *)
(* call {2}  (_: true ==> true). apply summitup_ll.  *)
(* skip. auto. *)
(* exists* b{1}. elim*. progress. *)
(* case (b_L = false). *)
(* sp. call (_:true). skip. progress. smt. *)
(* conseq (_: b{1} <> b'{1} ==> b{1} <> b'{1}). smt. smt. *)
(* call {1} (_: true ==> true). apply summitup_ll.  *)
(* call {2} (_: true ==> true). apply summitup_ll.  *)
(* wp. skip. auto. *)
(* qed. *)


(* local lemma ssim Na ya wa  : IsSqRoot (Na, ya) wa /\ invertible Na ya => *)
(*  equiv [ Sim1(V).simulate ~ Sim1'.simulate : ={glob V} /\ (Na,ya) = (Ny{1}) /\ ((Na,ya),wa) = (Ny{2},w{2}) ==> res.`1{1} = res.`1{2} ]. *)
(* move => ii. *)
(* conseq (qkok Na ya wa (fun x => true) ii). smt. *)
(* qed. *)

(* local lemma sim1'not &m Na ya wa :  *)
(*      Pr[Sim1'.simulate((Na, ya), wa) @ &m : ! res.`1] = inv 2%r. *)
(* proof. *)
(* have ->: Pr[Sim1'.simulate((Na, ya), wa) @ &m : ! res.`1] = Pr[Sim1'.allinone((Na, ya), wa) @ &m : ! res.`1]. byequiv. proc. *)
(* sim. wp.  inline*.  wp. rnd.  rnd.  wp. skip. progress. auto. auto. *)
(* byphoare. proc. inline*. simplify.  *)
(* swap [2..3] 4. wp. *)
(* seq 5 : true (1%r) (1%r/2%r) 1%r 0%r. *)
(* auto. *)
(* call summitup_ll. wp.  *)
(* call challenge_ll. wp. rnd. skip. smt. rnd. skip. progress. *)
(* smt. exfalso. auto. auto.  auto. auto. *)
(* qed. *)


(* lemma simnres Na ya wa : IsSqRoot (Na, ya) wa /\ invertible Na ya => *)
(*   phoare[ Sim1(V).simulate : arg = (Na,ya) ==> !res.`1 ] = (1%r/2%r). *)
(* move => ii. *)
(* bypr. progress. *)
(* rewrite H. clear H. *)
(* have <-: Pr[Sim1'.simulate((Na, ya),wa) @ &m : ! res.`1] = inv 2%r. *)
(* apply sim1'not. *)
(* byequiv (_: _ ==> res.`1{1} = res.`1{2}).  *)

(* conseq (ssim Na ya wa ii). *)
(* smt. progress. smt. *)
(* qed. *)
  
    

(* local lemma qrp_zk2_pr_l &m Na ya wa q : IsSqRoot (Na, ya) wa => *)
(*     Pr[ZK(HP, V).main((Na,ya),wa) @ &m : q res  ]  *)
(*      = Pr[ Sim1'.simulate((Na,ya),wa) @ &m : q res.`2  ]. *)
(* proof. move => isqr. byequiv. *)
(* conseq (_: _ ==> res{1} = res{2}.`2). progress. *)
(* conseq (qrp_zk2_eq Na ya wa isqr).  progress. smt. smt.  auto. auto. *)
(* qed. *)



(* local lemma sd &m (P : sbits -> bool) Na ya wa :  *)
(*      Pr[ Sim1'.simulate((Na,ya),wa) @ &m : res.`1 /\ P res.`2 ] *)
(*     = (1%r/2%r) * Pr[ Sim1'.simulate((Na,ya),wa) @ &m : P res.`2 ]. *)
(* have : Pr[ Sim1'.simulate((Na,ya),wa) @ &m : res.`1 /\ P res.`2 ] *)
(*  = Pr[ Sim1'.simulate((Na,ya),wa) @ &m : !res.`1 /\ P res.`2 ]. *)
(* byequiv (_: ={glob Sim1',arg} ==> _).   *)
(* proc.  inline*. *)
(* call (_:true). wp.  *)
(* call (_:true). wp.  *)
(* rnd (fun x => !x). rnd. wp. skip. progress. *)
(* smt. smt. auto. auto. *)
(* have ->: Pr[Sim1'.simulate((Na, ya), wa) @ &m : P res.`2] = *)
(*  Pr[Sim1'.simulate((Na, ya), wa) @ &m : res.`1 /\ P res.`2] + *)
(*    Pr[Sim1'.simulate((Na, ya), wa) @ &m : ! res.`1 /\ P res.`2]. *)
(* rewrite Pr[mu_split res.`1].  *)
(* have ->: Pr[Sim1'.simulate((Na, ya), wa) @ &m : P res.`2 /\ res.`1] *)
(*  = Pr[Sim1'.simulate((Na, ya), wa) @ &m : res.`1 /\ P res.`2]. smt. *)
(* have ->: Pr[Sim1'.simulate((Na, ya), wa) @ &m : P res.`2 /\ !res.`1] *)
(*  = Pr[Sim1'.simulate((Na, ya), wa) @ &m : !res.`1 /\ P res.`2]. smt. *)
(* auto. *)
(* move => q. *)
(* rewrite - q. smt. *)
(* qed. *)
 


(* lemma sim1zk &m Na ya wa q : *)
(*   IsSqRoot (Na, ya) wa /\ invertible Na ya => *)
(*     Pr[Sim1(V).simulate(Na, ya) @ &m : res.`1 /\ q res.`2] *)
(*      = Pr[ZK(HP, V).main((Na, ya), wa) @ &m : q res] / 2%r. *)
    
(* move => ii. *)
(* have ->: Pr[Sim1(V).simulate(Na, ya) @ &m : res.`1 /\ q res.`2] *)
(*  = Pr[Sim1'.simulate((Na,ya),wa) @ &m : res.`1 /\ q res.`2]. *)
(* byequiv.  *)
(* conseq (qkok Na ya wa q ii). progress;smt. auto. auto. *)
(* rewrite (sd &m q Na ya wa). *)
(* rewrite (qrp_zk2_pr_l &m Na ya wa q). smt. auto. *)
(* qed. *)

    
(* end section. *)

