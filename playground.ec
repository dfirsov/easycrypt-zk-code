require import AllCore DBool Bool.



(* independence and group op *)
module Exp = {
  var b1, b2 : bool
  proc main1() = {
   b1 <$ {0,1};
   b2 <$ {0,1};
   return (b1, b2);
  }

  proc main2() = {
   b1 <$ {0,1};
   b2 <$ {0,1};
   return (b1 ^^  b2, b2);
  }
  
}.


lemma exp_lemma : equiv[ Exp.main1 ~ Exp.main2 : true ==> ={res} ].
proof. proc. swap 1 1.
rnd (fun x => x ^^ Exp.b2{1}). rnd. 
skip. progress;smt.
qed.


lemma exp_lemma_add_info : 
  equiv[ Exp.main1 ~ Exp.main2 : true ==> ={res} /\ (res{2}.`2 = false => res{1}.`1 = res{2}.`1) ].
proof. proc. swap 1 1.
rnd (fun x => x ^^ Exp.b2{1}). rnd. 
skip. progress;smt.
qed.




local module Inits = {
    
  proc init1(N : int, y : int) = {
    var z,c,b;
    b <$ {0,1};
    z  <$ sqDist N;    
    c  <- z * if b then y else 1;
    return (b, z);
  }

  proc init1_t(N : int, y : int) = {
    var z,c;
    z  <$ sqDist N;    
    c  <- z * if true then y else 1;
    return (true, c);
  }

  proc init1_f(N : int, y : int) = {
    var z,c;
    z  <$ sqDist N;    
    c  <- z * if false then y else 1;
    return (false, c);
  }
  
  
  proc init2(N : int, y : int) = {
    var z,b;
    b <$ {0,1};
    z  <$ sqDist N;    
    return (b, z);
  }  

  proc init2_t(N : int, y : int) = {
    var z;
    z  <$ sqDist N;    
    return (true, z);
  }    

  proc init2_f(N : int, y : int) = {
    var z;
    z  <$ sqDist N;    
    return (false, z);
  }    
  
}.


local lemma init_lemma_f :
 equiv[ Inits.init1_f ~ Inits.init2_f : ={arg} ==> ={res} ].
proof. proc. simplify.
wp.
rnd.
skip. progress;smt.
qed.


local lemma init_lemma_t :
 equiv[ Inits.init1_t ~ Inits.init2_t : ={arg} ==> ={res} ].
proof. proc. simplify.
wp. simplify.
rnd (fun x => x * y{1}) (fun x => x * (inv N{1} y{1})). 
skip. progress;admit.
qed.
