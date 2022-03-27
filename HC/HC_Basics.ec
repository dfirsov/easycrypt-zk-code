pragma Goals:printall.
require import AllCore DBool Bool List Distr Int IntDiv Aux FSet DJoin.

require import Permutation.

type commitment, opening.
type edge = int * int * bool.


op Com  : bool -> (commitment * opening) distr.
op Open : commitment * opening -> edge option.

type graph.


op compl_graph     : int -> graph.
op compl_graph_cyc : int -> int list.


type hc_prob = (int * graph).
type hc_wit  = int list.
type hc_com  = commitment list.
type hc_resp = ((opening list) ,
                     (hc_wit * (opening list))) sum.
                   

type sbits.

module type Dist = {
   proc run(s : sbits) : bool
}.

require ZK_General.
clone import ZK_General as ZK_defs with type prob  = hc_prob,
                                        type wit   = hc_wit,
                                        type chal  = bool,
                                        type com   = hc_com,
                                        type resp  = hc_resp,
                                        type sbits = sbits.


module ZKP(P : Prover, V : Verifier, D : Dist) = {
  proc run(Ny : hc_prob, w : hc_wit, b : bool) = {
    var c,r;
    c <- P.commit(Ny,w);
    r <- P.response(b);
    return (c,r);
  }
}.




module ZKD(P : Prover, V : Verifier, D : Dist) = {
  proc main(Ny : prob, w : wit) = {
    var c,b,r,result,rb;
    c <- P.commit(Ny,w);
    b <- V.challenge(Ny,c);
    r <- P.response(b);
    result <- V.summitup(c,r);
    rb <- D.run(result);
    return rb;
  }
}.



require DjoinMap.
clone import DjoinMap as DJMM with type a <- bool, 
                           type b <- (commitment * opening),
                           op d <- Com.
                                        

op IsHC : hc_prob ->  hc_wit -> bool. 
op HasHC (Ny : hc_prob) = exists w, IsHC Ny w.

op perm_d : int -> permutation distr.


op flatten_and_permute : permutation -> graph-> bool list.
op permute_wit : permutation -> hc_wit -> hc_wit.
op split_edge_list ['a] : 'a list -> hc_wit -> 'a list * 'a list.


module HP  = {

  var n : int
  var g : graph
  var prm : permutation
  var w : hc_wit
  var fal : bool list           (* flattened adj. graph *)

  var zpd_g, zpd_w : bool list
  var pi_gco, pi_wco : (commitment * opening) list
  var pi_gwco : (commitment * opening) list
  var pi_w : hc_wit
  
  proc commit(p_a : hc_prob, w_a : hc_wit)  = {
    (n,g) <- p_a;
    w <- w_a;
    prm <$ perm_d n;
    fal <- flatten_and_permute prm g;

    pi_gwco <@ DJM.main5(fal);
    return map fst pi_gwco;
  }

  
  proc response(b : bool) : hc_resp = {
    pi_w <- permute_wit prm w;
    (zpd_g, zpd_w) <- split_edge_list fal pi_w;
         
    return if b then Left (map snd pi_gwco) 
                else Right (pi_w, map snd (drop n (ip (mk_perm (zpd_g ++ zpd_w) fal) pi_gwco)));
 } 
}.


module HP'  = {

  var n : int
  var g : graph
  var prm : permutation
  var w : hc_wit
  var fal : bool list           (* flattened adj. graph *)

  var zpd_g, zpd_w : bool list
  var pi_gco, pi_wco : (commitment * opening) list
  var pi_gwco : (commitment * opening) list
  var pi_w : hc_wit
  
  proc commit(p_a : hc_prob, w_a : hc_wit) : hc_com = {   
    (n,g) <- p_a;
    w <- w_a;
    prm <$ perm_d n; 
    fal <- flatten_and_permute prm g;
    pi_w <- permute_wit prm w;
    (zpd_g, zpd_w) <- split_edge_list fal pi_w;
    
    (pi_gco, pi_wco) <@ DJM.main1(zpd_g, zpd_w);
    pi_gwco <-(pi (mk_perm (zpd_g ++ zpd_w) fal)) (pi_gco ++ pi_wco);

    return (map fst pi_gwco);    
  }
  
  
  proc response(b : bool) : hc_resp = {
    return if b then Left (map snd pi_gwco) 
          else Right (pi_w, map snd pi_wco);
 } 
}.



section.
declare module V : Verifier {HP,HP'}.
lemma zk_hp_hp': 
  equiv [ ZK(HP, V).main ~ ZK(HP', V).main : ={arg, glob V} ==> ={res} ].
proof. proc.
seq 1 1 : (={Ny, c, glob V} 
    /\ HP.pi_gwco{1} = HP'.pi_gwco{2}
    /\ HP'.pi_w{2} = permute_wit HP'.prm{2} HP'.w{2}
  /\ HP'.fal{2} = flatten_and_permute HP'.prm{2} HP'.g{2}
  /\  (HP'.zpd_g){2} = (split_edge_list HP'.fal{2} HP'.pi_w{2}).`1
  /\  (HP'.zpd_w){2} = (split_edge_list HP'.fal{2} HP'.pi_w{2}).`2
    /\   (pi (mk_perm (HP'.zpd_g ++ HP'.zpd_w) HP'.fal) 
            (HP'.pi_gco ++ HP'.pi_wco)){2} = HP.pi_gwco{1}
  /\ HP.w{1} = HP'.w{2}
  /\ HP.prm{1} = HP'.prm{2}
  /\ HP.g{1} = HP'.g{2}  
  /\ HP.n{1} = HP'.n{2}  
  /\ HP.fal{1} = HP'.fal{2}
).
inline HP.commit HP'.commit. wp.
seq 6 6 : (={Ny, glob V} 
  /\ HP.fal{1} = HP'.fal{2}  
  /\ HP.g{1} = HP'.g{2}
  /\ HP.w{1} = HP'.w{2}
  /\ HP.prm{1} = HP'.prm{2}
  /\ HP.n{1} = HP'.n{2}
  /\ ={w_a, p_a}
  /\ HP'.fal{2} = flatten_and_permute HP'.prm{2} HP'.g{2}).
wp. rnd. wp. skip. progress.  sp.
exists* HP'.zpd_g{2}, HP'.zpd_w{2}, HP.fal{1}.
elim*. progress.
simplify.
call (djm_main511 (mk_perm (zpd_g_R ++ zpd_w_R) fal_L)).
skip. progress. rewrite mk_perm_ip.  admit. auto. 
smt. smt.
seq 2 2 : (={glob V, r ,c}).
inline*.
wp.  simplify. call (_:true).
skip. progress.
case (result_R = true).
move => h. rewrite h.
simplify. auto.
move => h.
have : result_R = false.
smt. clear h. move => h. rewrite h. simplify.
progress.
rewrite   ippi. admit.
call (_:true). skip. progress.
qed.
end section.

section.
declare module V : Verifier {HP,HP'}.
declare module D : Dist {V,HP,HP'}.
lemma zkp_hp_hp': 
  equiv [ ZKP(HP, V,D).run ~ ZKP(HP',V,D).run : ={arg, glob V} ==> ={res} ].
admitted.

lemma zkp_hp'_hp: 
  equiv [ ZKP(HP', V,D).run ~ ZKP(HP,V,D).run : ={arg, glob V} ==> ={res} ].
admitted.


(* one-time simulator  *)
local module Sim1(V : Verifier) = {
  module ZKP_HP = ZKP(HP,V,D)
  module ZKP_HP' = ZKP(HP',V,D)
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
  module ZKP_HP = ZKP(HP,V,D)
  module ZKP_HP' = ZKP(HP',V,D)
  proc sinit(p_a : hc_prob, w_a : hc_wit) = {
    var n, g,bb,r;
    (n,g) <- (p_a.`1, p_a.`2);

    bb <$ {0,1};

    if (bb) {
       r <- ZKP_HP.run(p_a, w_a, bb);
    }else{
       r <- ZKP_HP'.run((n, compl_graph n), w_a, bb);
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



local lemma zkp_sim1_sim1': 
  equiv [ Sim1(V).simulate ~ Sim1_1(V).simulate : 
               arg{1} = arg{2}.`1 /\ ={glob V, glob D} ==> ={res} ].
proof. proc.
inline Sim1(V).sinit.
inline Sim1_1(V).sinit.
sp.
seq 1 1 : (p_a{2} = pa{2} /\
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
  /\ !b0{1} /\ b0{1} = b0{2} /\ ={bb, glob V, glob D, pa} /\ !bb{1} ).
sp. wp.
rnd (fun (f : permutation) => compose f (mk_perm_list_fun w{2} w{1})) 
  (fun (f : permutation) => compose f (inv (mk_perm_list_fun w{2} w{1}))) .
skip. progress. admit. admit. admit. admit. admit. admit.
wp.  rnd. rnd.  wp.  skip. progress.
call (_:true).
call (_:true).
call (_:true).
wp. skip. progress.
qed.



local module Sim1_2(V : Verifier) = {
  module ZKP_HP = ZKP(HP,V,D)
  module ZKP_HP' = ZKP(HP',V,D)
  proc sinit(p_a : hc_prob, w_a : hc_wit) = {
    var n, g,bb,r;
    (n,g) <- (p_a.`1, p_a.`2);

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


local module Sim1_3(V : Verifier) = {
  module ZKP_HP = ZKP(HP,V,D)
  module ZKP_HP' = ZKP(HP',V,D)
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


local lemma zkp_sim1''_sim1''': 
  equiv [ Sim1_2(V).simulate ~ Sim1_3(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob D} ==> ={res} ].
proc.
inline Sim1_2(V).sinit.
inline Sim1_3(V).sinit.
sp.
seq 1 1 : (p_a{2} = pa{2} /\
  w_a{2} = wa{2} /\
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
call zkp_hp'_hp. skip. progress.
sim.
qed.


local module Sim1_4(V : Verifier) = {
  module ZKP_HP = ZKP(HP,V,D)

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

local lemma zkp_sim1''_sim1_4: 
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


local lemma zkp_sim_4_sim1_5: 
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



local lemma zkp_sim_5_sim1_6: 
  equiv [ Sim1_5(V).simulate ~ Sim1_6(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob D} ==> ={res} ].
proc. swap {1} 5 -1.  sim. swap {2} 3 -1. sim.
qed.


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


local lemma zkp_sim_6_sim1_7: 
  equiv [ Sim1_6(V).simulate ~ Sim1_7(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> 

   res.`1{1} /\ res.`2{1} <=>  res.`1{2} /\ res.`2{2} ].
proc. sp. 
seq 3 3 : (={b,bb,r1, glob V, glob D, glob HP}).
call (_:true). rnd. simplify.
inline*. wp.  rnd. wp.  rnd. wp.  skip. progress.
case (b{1} <> bb{1}).
call {1} (_:true ==> true).  admit.
call {2} (_:true ==> true).  admit.
call {1} (_:true ==> true).  admit.
call {2} (_:true ==> true).  admit.
call {1} (_:true ==> true).  admit.
call {2} (_:true ==> true).  admit. skip. 
smt.
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



local lemma zkp_sim_7_sim1_8: 
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


local lemma zkp_sim_8_sim1_9: 
  equiv [ Sim1_8(V).simulate ~ Sim1_9(V).simulate : 
               arg{1} = arg{2} /\ ={glob V, glob D, glob HP} ==> ={res} ].
proc. inline*.
sim.
qed.



local lemma zkp_sim_9_zkd: 
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
   +    Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 /\ !res.`1  ].
proof. rewrite Pr[mu_split res.`1].
auto.
qed.


local lemma sim_9_pr2 &m pa wa: 
   Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 /\ res.`1 ]
   = Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 /\ !res.`1  ].
proof. byequiv.
proc. seq 1 1 : (={rb}). sim. rnd (fun x => !x). 
skip. progress.  auto. auto.
qed.

local lemma sim_9_pr3 &m pa wa: 
   Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 ]
   = 2%r * Pr[ Sim1_9(V).simulate(pa,wa) @ &m : res.`2 /\ res.`1  ].
smt (sim_9_pr1 sim_9_pr2).
qed.
