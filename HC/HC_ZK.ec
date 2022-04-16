pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.

require import Permutation HC_Basics.
import ZK_defs DJMM.

module HP'  = {
  var n : int 
  var g : graph
  var prm : permutation
  var w : hc_wit
  var fal : bool list      

  var zpd_g, zpd_w : bool list
  var pi_gco, pi_wco : (commitment * opening) list
  var pi_gwco : (commitment * opening) list
  var pi_w : hc_wit
  
  proc commit(p_a : hc_prob, w_a : hc_wit) : hc_com = {   
    (n,g) <- p_a;
    w <- w_a;
    prm <$ perm_d n; 
    fal <- fap prm g;
    pi_w <- permute_wit prm w;
    (zpd_g, zpd_w) <- (drop n (ip (prj pi_w) fal), 
                            take n (ip (prj pi_w) fal));
    (pi_wco, pi_gco) <@ DJM.main1(zpd_w, zpd_g);
    pi_gwco <-(pi (prj pi_w)) (pi_wco ++ pi_gco);

    return (map fst pi_gwco);    
  }
    
  proc response(b : bool) : hc_resp = {
    return if b then Left (prm, map snd pi_gwco) 
          else Right (pi_w, map snd pi_wco);
 } 
}.


section.
declare module V : Verifier {HP,HP'}.
declare module D : Dist {V,HP,HP'}.

axiom D_run_ll : islossless D.run.
axiom V_summitup_ll : islossless V.summitup.


lemma zkp_hp'_hp (a : hc_prob * hc_wit):  IsHC a =>
  equiv [ ZKP(HP, V).run ~ ZKP(HP',V).run : (arg{2}.`1, arg{2}.`2) = a  /\ ={arg, glob V} ==> ={res} ].
proof. move => ishc. proc.
seq 1 1 : (={Ny, c, glob V,b} 
    /\ HP.pi_gwco{1} = HP'.pi_gwco{2}
    /\ a = ((HP'.n, HP'.g), HP'.w){2}
    /\ HP'.pi_w{2} = permute_wit HP'.prm{2} HP'.w{2}
  /\ HP'.fal{2} = fap HP'.prm{2} HP'.g{2}
  /\  (HP'.zpd_g){2} = drop HP'.n{2} (ip (prj HP'.pi_w) HP'.fal){2}
  /\  (HP'.zpd_w){2} = take HP'.n{2} (ip (prj HP'.pi_w) HP'.fal){2}
    /\   (pi ((prj HP'.pi_w{2})) 
            (HP'.pi_wco ++ HP'.pi_gco)){2} = HP.pi_gwco{1}
  /\ HP.w{1} = HP'.w{2}
  /\ HP.prm{1} = HP'.prm{2}
  /\ HP.g{1} = HP'.g{2}  
  /\ HP.n{1} = HP'.n{2}  
  /\ HP.fal{1} = HP'.fal{2}
  /\ size HP'.pi_wco{2} = size HP'.w{2}
).
inline HP.commit HP'.commit. wp.
seq 6 6 : (={Ny, glob V,b} 
  /\ HP.fal{1} = HP'.fal{2}  
    /\ a = ((HP'.n, HP'.g), HP'.w){2}
  /\ HP.g{1} = HP'.g{2}
  /\ HP.w{1} = HP'.w{2}
  /\ HP.prm{1} = HP'.prm{2}
  /\ HP.n{1} = HP'.n{2}
  /\ ={w_a, p_a}
  /\ HP'.fal{2} = fap HP'.prm{2} HP'.g{2}).
wp. rnd. wp. skip. progress.  smt. sp.
exists* HP'.pi_w{2}.
elim*. progress.
simplify.
exists* HP'.zpd_w{2}, HP'.zpd_g{2}.
elim*. progress.
call (djm_main511 (prj pi_w_R ) (zpd_w_R, zpd_g_R) ).
skip. progress. smt.
have : size result_R.`1 = HP'.n{2}.
  have : HP'.n{2} <= size (ip (prj (permute_wit HP'.prm{2} HP'.w{2}))
            (fap HP'.prm{2} HP'.g{2})).
rewrite /permute_wit.  
rewrite size_ip. rewrite fap_prop2. 
smt.
smt. 
smt. auto.
seq 2 2 : (={glob V, r ,c} ).
inline*.
wp.  simplify. 
skip. progress. 
case (b{2} = true).
move => h.  rewrite h.
simplify. auto.
move => h.
have : b{2} = false.
smt. clear h. move => h. rewrite h. simplify.
progress.
rewrite   ippi. 
smt. skip. progress.
qed.

    
    
(* one-time simulator  *)



local module Sim1_0(V : Verifier) = {
  module ZKP_HP = ZKP(HP,V)
  module ZKP_HP' = ZKP(HP',V)
  proc sinit(p_a : hc_prob) : bool * (hc_com * hc_resp) = {
    var n, g,bb,r;
    (n,g) <- (p_a.`1, p_a.`2);

    bb <$ {0,1};

    if (bb) {
       r <- ZKP_HP.run(p_a, witness, bb);
    }else{
       r <- ZKP_HP'.run((n, compl_graph n), (compl_graph_cyc n), bb);
    }
    return (bb, r);
  }

  proc simulate(pa : hc_prob) : bool * bool  = {
    var b',b,zryb,result, rb;
    (b',zryb) <- sinit(pa);
    b <- V.challenge(pa, fst zryb);
    result <- V.summitup(zryb);
    rb <- D.run(result);
    return (b = b', rb);
  }

}.


local module Sim1_1(V : Verifier) = {
  module ZKP_HP = ZKP(HP,V)
  module ZKP_HP' = ZKP(HP',V)
  proc sinit(p_a : hc_prob, w_a : hc_wit) = {
    var n, g,bb,r;
    (n,g) <- (p_a.`1, p_a.`2);

    bb <$ {0,1};

    if (bb) {
       r <- ZKP_HP.run(p_a, w_a, bb);
    }else{
        r <- ZKP_HP'.run((n, compl_graph n), w_a, bb);
        (* 
Alternative:

r <- aux1(n, w_a);
 *)
    }
    return (bb, r);
  }

(* 

(Here or in diff. module)
proc aux1(n, w_a) = {
g <- compl_graph n;
    w <- w_a;
    prm <$ perm_d n; 
    fal <- fap prm g;
    pi_w <- permute_wit prm w;
    (zpd_g, zpd_w) <- (drop n (ip (prj pi_w) fal), 
                            take n (ip (prj pi_w) fal));
    (pi_wco, pi_gco) <@ DJM.main1(zpd_w, zpd_g);
    pi_gwco <-(pi (prj pi_w)) (pi_wco ++ pi_gco);

    return (map fst pi_gwco, Right (pi_w, map snd pi_wco));
}
 *)

  
  proc simulate(pa : hc_prob, wa : hc_wit) : bool * bool  = {
    var b',b,zryb,result, rb;
    (b',zryb) <- sinit(pa,wa);
    b <- V.challenge(pa, fst zryb);
    result <- V.summitup(zryb);
    rb <- D.run(result);
    return (b = b', rb);
  }

}.

(*



ZKDB ~ Sim1  
(ZKDB is like ZKD, but outputs additionally a random bit, and if this random bit is "fail", outputs a fixed value)
(I assume Sim1, when outputting failure, outputs a fixed value)

*)

local lemma sim_0_1 a:  (fst (fst a)) = size (snd a) =>
  equiv [ Sim1_0(V).simulate ~ Sim1_1(V).simulate : 
               a = arg{2} /\ arg{1} = arg{2}.`1 /\ ={glob V, glob D} ==> ={res} ].
proof. move => sas. proc.
inline Sim1_0(V).sinit.
inline Sim1_1(V).sinit.
sp.
seq 1 1 : (p_a{2} = pa{2} /\ a = (pa,wa){2} /\
  w_a{2} = wa{2} /\
  g{2} = p_a{2}.`2 /\
  n{2} = p_a{2}.`1 /\
  p_a{1} = pa{1} /\
  g{1} = p_a{1}.`2 /\
  n{1} = p_a{1}.`1 /\ 
  pa{1} = pa{2} /\ ={glob V, glob D} /\ bb{1} = bb{2}).
rnd. skip. progress. 
if. auto. 
call (_:true).
call (_:true).
wp. inline*. wp.  call (_:true).
 wp.  rnd.  wp. rnd. wp. skip. progress.
rewrite H. simplify. auto.
seq 1 1 : (={r,bb, glob V,glob D,pa} /\ !bb{1}).
inline*. 
seq  10 10 : (HP'.pi_w{1} = HP'.pi_w{2} /\ HP'.fal{1} = HP'.fal{2}
  /\ !b0{1} /\ b0{1} = b0{2} /\ ={bb, glob V, glob D, pa} /\ !bb{1}
  /\ HP'.n{1} = HP'.n{2}).
sp. wp.
rnd (fun (f : permutation) => compose f (mk_perm_list_fun w{2})) 
 (fun (f : permutation) => compose f (inv (mk_perm_list_fun w{2}))).
skip. progress.  rewrite /compose.  smt (inv_prop2). 
rewrite /compose.  smt. rewrite /compose. smt.
rewrite /compose. smt (inv_prop1). 
rewrite /permute_wit /compose. 
have ->: pa{2}.`1 = size (wa{2}). smt.
rewrite /compl_graph_cyc.
rewrite -  invop. 
rewrite map_comp. auto. 
smt (fap_prop1).
wp.  rnd. rnd.  wp.  skip. progress.
rewrite H. simplify. auto.
call (_:true).
call (_:true).
call (_:true).
wp. skip. progress.
qed.



local module Sim1_2(V : Verifier) = {
  module ZKP_HP = ZKP(HP,V)
  module ZKP_HP' = ZKP(HP',V)
  proc sinit(p_a : hc_prob, w_a : hc_wit) = {
    var n, g, bb, r;
    (n,g) <- p_a;

    bb <$ {0,1};
    if (bb) {
       r <- ZKP_HP.run(p_a, w_a, bb);
    }else{
       r <- ZKP_HP'.run(p_a, w_a, bb);
    }
    return (bb, r);
  }

  proc simulate(pa : hc_prob, wa : hc_wit) : bool * bool  = {
    var b',b,zryb,result, rb;
    (b',zryb) <- sinit(pa,wa);
    b <- V.challenge(pa, fst zryb);
    result <- V.summitup(zryb);
    rb <- D.run(result);
    return (b = b', rb);
  }
}.



(* hiding props  *)
op negl, negl2 : real.
axiom negl2_prop : 0%r <= negl2 < 1%r/4%r.


local lemma sim_1_2 &m pa wa: 
   `|Pr[ Sim1_1(V).simulate(pa,wa) @ &m : res.`1 /\ res.`2 ]
      - Pr[ Sim1_2(V).simulate(pa,wa) @ &m : res.`1 /\ res.`2 ]| 
   <= negl.
admitted.

(**

Currently: AND(res) is indist. etbween Sim11, Sim12.

Instead: (success, D-output) is indist. between them

local lemma sim_1_2 &m pa wa pred: 
   `|Pr[ Sim1_1(V).simulate(pa,wa) @ &m : pred res ]
      - Pr[ Sim1_2(V).simulate(pa,wa) @ &m : pred res ]| 
   <= negl.
admitted.

Instead: (success, result) is indist. between them (* Here: maybe not easiest *)

*)


    
local lemma  sim1ass &m pa :
  `|Pr[Sim1_0(V).simulate(pa) @ &m : res.`1] -  1%r/2%r| <= negl2.
  (* 
Using sim_1_2, but for Sim1, Sim1_9 (but discard rb if fails)
Instantiate with pred := fst
Gives: |Pr[Sim1(V).simulate(pa) @ &m : res.`1] - Pr[Sim1_9 @ &m : res.`1] | <= negl2.
The second probability is =1/2 by simple phoare analysis.
 *)
admitted.


local module Sim1_3(V : Verifier) = {
  module ZKP_HP = ZKP(HP,V)
  module ZKP_HP' = ZKP(HP',V)
  proc sinit(p_a : hc_prob, w_a : hc_wit) = {
    var n, g,bb,r;
    (n,g) <- (p_a.`1, p_a.`2);
    bb <$ {0,1};
    r <- ZKP_HP.run(p_a, w_a, bb);
    return (bb, r);
  }

  proc simulate(pa : hc_prob, wa : hc_wit) : bool * bool  = {
    var b',b,zryb,result,rb;
    (b',zryb) <- sinit(pa,wa);
    b <- V.challenge(pa, fst zryb);
    result <- V.summitup(zryb);
    rb <@ D.run(result);
    return (b = b', rb);
  }
}.


local lemma sim_2_3 a: IsHC a =>
  equiv [ Sim1_2(V).simulate ~ Sim1_3(V).simulate : 
               arg{1} = a /\ arg{1} = arg{2} /\ ={glob V, glob D} ==> ={res} ].
move => ishc.
proc.
inline Sim1_2(V).sinit.
inline Sim1_3(V).sinit.
sp.
seq 1 1 : (p_a{2} = pa{2} /\
  w_a{2} = wa{2} /\
  a = (pa{2},wa{2}) /\
  g{2} = p_a{2}.`2 /\
  n{2} = p_a{2}.`1 /\
  p_a{1} = pa{1} /\
  w_a{1} = wa{1} /\
  g{1} = p_a{1}.`2 /\
  n{1} = p_a{1}.`1 /\ (pa{1}, wa{1}) = (pa{2}, wa{2}) /\ ={glob V, glob D} /\ bb{1} = bb{2}).
rnd. skip. progress.
case (bb{1} = true).
rcondt {1} 1. progress. sim.
rcondf {1} 1. progress. skip. smt.
seq 1 1 : (p_a{2} = pa{2} /\
  w_a{2} = wa{2} /\
  g{2} = p_a{2}.`2 /\
  n{2} = p_a{2}.`1 /\
  p_a{1} = pa{1} /\
  w_a{1} = wa{1} /\
  g{1} = p_a{1}.`2 /\
  n{1} = p_a{1}.`1 /\ (pa{1}, wa{1}) = (pa{2}, wa{2}) /\ ={glob V, glob D} /\ bb{1} = bb{2} /\ r{1} = r{2}).
symmetry.
call (zkp_hp'_hp a ). simplify. skip. progress.
sim.
qed.


local module Sim1_4(V : Verifier) = {
  module ZKP_HP = ZKP(HP,V)
  proc simulate(pa : hc_prob, wa : hc_wit) : bool * bool  = {
    var b,result,r,n,g,bb,rb;
    (n,g) <- (pa.`1, pa.`2);
    bb <$ {0,1};
    r <- ZKP_HP.run(pa, wa, bb);
    b <- V.challenge(pa, fst r);
    result <- V.summitup(r);
    rb <@ D.run(result);
    return (b = bb, rb);
  }
}.


local lemma sim_3_4:
  equiv [ Sim1_3(V).simulate ~ Sim1_4(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob D} ==> ={res} ].
proc. sim. 
inline*. sp. wp. rnd. wp. rnd. wp.  rnd. skip. progress.
qed.


local module Sim1_5(V : Verifier) = {
  proc simulate(pa : hc_prob, wa : hc_wit) : bool * bool  = {
    var b,result,r1,r2,n,g,bb,rb;
    (n,g) <- (pa.`1, pa.`2);
    bb <$ {0,1};
    r1 <- HP.commit(pa,wa);
    r2 <- HP.response(bb);
    b <- V.challenge(pa, r1);
    result <- V.summitup(r1,r2);
    rb <@ D.run(result);
    return (b = bb, rb);
  }
}.


local lemma sim_4_5: 
  equiv [ Sim1_4(V).simulate ~ Sim1_5(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob D} ==> ={res} ].
proc. sim. 
inline*. sp. wp. call (_:true). 
call (_:true).  wp. rnd. wp. rnd.  wp. rnd. skip.
progress.
qed.


local module Sim1_6(V : Verifier) = {
  proc simulate(pa : hc_prob, wa : hc_wit) : bool * bool  = {
    var b,result,r1,r2,n,g,bb,rb;
    (n,g) <- (pa.`1, pa.`2);
    r1 <- HP.commit(pa,wa);
    bb <$ {0,1};
    b <- V.challenge(pa, r1);
    r2 <- HP.response(bb);
    result <- V.summitup(r1,r2);
    rb <@ D.run(result);
    return (b = bb, rb);
  }
}.


local lemma sim_5_6: 
  equiv [ Sim1_5(V).simulate ~ Sim1_6(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob D} ==> ={res} ].
proc. swap {1} 5 -1. sim. swap {2} 3 -1. sim. qed.


local module Sim1_7(V : Verifier) = {
  proc simulate(pa : hc_prob, wa : hc_wit) : bool * bool  = {
    var b,result,r1,r2,n,g,bb,rb;
    (n,g) <- (pa.`1, pa.`2);
    r1 <- HP.commit(pa,wa);
    bb <$ {0,1};
    b <- V.challenge(pa, r1);
    r2 <- HP.response(b);
    result <- V.summitup(r1,r2);
    rb <@ D.run(result);
    return (b = bb, rb);
  }
}.


local lemma sim_6_7: 
  equiv [ Sim1_6(V).simulate ~ Sim1_7(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
   res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2} ].
proc. sp. 
seq 3 3 : (={b,bb,r1, glob V, glob D, glob HP}).
call (_:true). rnd. simplify.
inline*. wp.  rnd. wp.  rnd. wp.  skip. progress.
case (b{1} <> bb{1}).
call {1} (_:true ==> true). apply D_run_ll. 
call {2} (_:true ==> true). apply D_run_ll. 
call {1} (_:true ==> true). apply V_summitup_ll. 
call {2} (_:true ==> true). apply V_summitup_ll. 
call {1} (_:true ==> true). proc. wp. skip. auto.
call {2} (_:true ==> true). proc. wp. skip. auto.
skip.  smt.
sim. progress. smt.
qed.


local module Sim1_8(V : Verifier) = {
  proc simulate(pa : hc_prob, wa : hc_wit) : bool * bool  = {
    var b,result,r1,r2,n,g,bb,rb;
    (n,g) <- (pa.`1, pa.`2);
    r1 <- HP.commit(pa,wa);
    b <- V.challenge(pa, r1);
    r2 <- HP.response(b);
    result <- V.summitup(r1,r2);
    rb <@ D.run(result);
    bb <$ {0,1};
    return (bb, rb);
  }
}.


local lemma sim_7_8: 
  equiv [ Sim1_7(V).simulate ~ Sim1_8(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob D} ==> ={res} ].
proc. swap {1} 3 4.
seq 6 6 : (={rb}). sim. 
exists* b{1}. elim*. progress.
rnd (fun b => b ^^ !b_L).
skip. progress. smt. smt.
smt.
qed.


local module Sim1_9(V : Verifier) = {
  module ZKD = ZKD(HP,V,D)
  proc simulate(pa : hc_prob, wa : hc_wit) : bool * bool  = {
    var bb,rb;
    rb <- ZKD.main(pa,wa);
    bb <$ {0,1};
    return (bb, rb);
  }
}.


local lemma sim_8_9: 
  equiv [ Sim1_8(V).simulate ~ Sim1_9(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> ={res} ].
proc. inline*. sim.
qed.


local lemma sim_2_9 a: IsHC a =>
  equiv [ Sim1_2(V).simulate ~ Sim1_9(V).simulate : 
               a = arg{1} /\ arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2} ].
move => ishc.
transitivity Sim1_3(V).simulate 
(a = arg{1} /\ arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}) (arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}). progress. smt. smt.
conseq (sim_2_3 a ishc). auto. auto.
transitivity Sim1_4(V).simulate 
(arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}) (arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}). progress. smt. smt.
conseq sim_3_4. auto. auto.
transitivity Sim1_5(V).simulate 
(arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}) (arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}). progress. smt. smt.
conseq sim_4_5. auto. auto.
transitivity Sim1_6(V).simulate 
(arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}) (arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}). progress. smt. smt.
conseq sim_5_6. auto. auto.
transitivity Sim1_7(V).simulate 
(arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}) (arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}). progress. smt. smt.
conseq sim_6_7. auto. auto.
transitivity Sim1_8(V).simulate 
(arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}) (arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 
  res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2}). progress. smt. smt.
conseq sim_7_8. auto. auto.
conseq sim_8_9. auto.
qed.


local lemma sim_9_10: 
  equiv [ Sim1_9(V).simulate ~ ZKD(HP,V,D).main : 
               arg{1} = arg{2} /\ ={glob V, glob D, glob HP} 
                  ==> res.`2{1} = res{2} ].
proc*.  
inline Sim1_9(V).simulate.
wp . rnd {1}.
simplify. sp.  sim.
inline*. sim. wp.  skip. progress.
qed.


local lemma sim_9_pr1 &m pa wa: 
   Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 ]
   =  Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 /\ res.`1 ]
   + Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 /\ !res.`1 ].
proof. rewrite Pr[mu_split res.`1]. auto. 
qed.


local lemma sim_9_pr2 &m pa wa: 
   Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 /\ res.`1 ]
   = Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 /\ !res.`1  ].
proof. byequiv.
proc. seq 1 1 : (={rb}). sim. rnd (fun x => !x). 
skip. progress. auto. auto.
qed.


local lemma sim_9_pr3 &m pa wa: 
   Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 ]
   = 2%r * Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 /\ res.`1  ].
smt (sim_9_pr1 sim_9_pr2).
qed.


require import Pr_arg.  
require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.
import BRM.


local lemma sim1_main &m pa wa:  IsHC (pa,wa) =>
   `|Pr[ Sim1_0(V).simulate(pa) @ &m : res.`1 /\ res.`2 ]

      / Pr[ Sim1_0(V).simulate(pa) @ &m : res.`1 ]

         - Pr[ ZKD(HP,V,D).main(pa,wa) @ &m : res ]| 

  <= 2%r * negl + 20%r * negl2.
proof. move => ishc.
have ->: 
  Pr[ ZKD(HP,V,D).main(pa,wa) @ &m : res ]
  = Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 ]. 
 byequiv (_: arg{1} = arg{2} /\ ={glob V, glob D, glob HP}  ==> _). 
 symmetry. conseq sim_9_10. progress;auto. auto. auto. auto.
have ->: 
   Pr[Sim1_0(V).simulate(pa) @ &m : res.`1 /\ res.`2]
    = Pr[ Sim1_1(V).simulate(pa,wa) @ &m : res.`1 /\ res.`2 ].
   byequiv. 
conseq (sim_0_1 (pa,wa) _ ). smt.  simplify. smt. auto. auto.
have h: 
   Pr[Sim1_0(V).simulate(pa) @ &m : res.`1]
    = Pr[ Sim1_1(V).simulate(pa,wa) @ &m : res.`1].
   byequiv. conseq (sim_0_1 (pa,wa) _). smt. auto. auto. auto.
smt. auto. auto.
rewrite sim_9_pr3.
apply (ler_trans (2%r * 
    `|Pr[Sim1_1(V).simulate(pa, wa) @ &m : res.`1 /\ res.`2] -
        Pr[Sim1_9(V).simulate(pa, wa) @ &m : res.`2 /\ res.`1]| 
           + 20%r * negl2)).
apply main_fin. smt. smt. smt. smt (negl2_prop). 
rewrite h. rewrite Pr[mu_sub]. auto. auto.
apply pr_e1. smt.  
apply sim1ass.
apply pr_e2. smt.
apply sim1ass.
have ->: Pr[Sim1_9(V).simulate(pa, wa) @ &m : res.`2 /\ res.`1] =
 Pr[Sim1_2(V).simulate(pa, wa) @ &m : res.`1 /\ res.`2].
byequiv (_: (pa, wa) = arg{1} /\ arg{1} = arg{2} 
 /\ ={glob V, glob D, glob HP} ==> _). 
symmetry. conseq (sim_2_9 (pa,wa) ishc). smt. smt. auto. auto.
smt (sim_1_2).
qed.    
