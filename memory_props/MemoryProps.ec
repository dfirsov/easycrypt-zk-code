require import AllCore Distr DBool.



require import Reflection ReflectionComp.

clone import ReflComp with type at1 <- unit,
                           type at2 <- unit,
                           type rt1 <- unit.




section.
declare module A : RewEx1Ex2.
axiom A_run_ll : islossless A.ex1.    
lemma  qq &m : phoare[ A.ex1 :  (glob A) = (glob A){m} ==> exists &n, (glob A) = (glob A){n} ]=  1%r.
proc*.
seq 1 : true. auto.
call A_run_ll. auto. skip.
progress. exists &hr. auto.
hoare. auto. auto.   
qed.

lemma rl  &m : Pr[ A.ex1() @ &m : exists &n, (glob A) = (glob A){n} ] =  1%r.
byphoare (_: (glob A) = (glob A){m} ==> _). apply (qq &m). auto. auto.
qed.






require import RandomFacts RealSeries List.

axiom ler_trans1 (a b c : real) : a < b => b <= c => a < c.




lemma www &m p :   
    exists (D1 : unit -> (glob A) -> (unit * (glob A)) distr)
      (D2 : unit -> unit * (glob A) -> (glob A) Distr.distr),
      (forall &m (M : unit * (glob A) -> bool),
         mu (D1 tt (glob A){m}) M = Pr[A.ex1() @ &m : M (res, (glob A))]) /\
      (forall &m (M : (glob A) -> bool) (r1 i2 : unit),
         mu (D2 i2 (r1, (glob A){m})) M =
         Pr[A.ex2(i2, r1) @ &m : M (glob A)]) /\
      (forall &m (M : (glob A) -> bool) (i1 i2 : unit),
        mu ((dlet (D1 i1 (glob A){m}) (D2 i2))) M =
        Pr[RCR(A).main(i1, i2) @ &m : M (glob A)]) 

   /\ forall (M :  (glob A) -> bool), 
       p <= Pr[ RCR(A).main(tt,tt) @ &m : M (glob A) ]  =>
       0%r < p =>
   exists g, 0%r < mu1 (D1 tt (glob A){m}) (tt,g)  /\ mu (D2 tt ((tt,g))) M >= p.
proof.  elim (refl_comp_simple A). progress.
exists D1 D2. progress. rewrite H. auto.
pose g0 := (glob A){m}.

case (exists (g : (glob A)),
  0%r < mu1 (D1 tt g0) (tt, g) /\ p <= mu (D2 tt (tt, g)) M).
auto.
move => G.
have: (forall (g : (glob A)),
     ! (0%r < mu1 (D1 tt g0) (tt, g) /\ p <= mu (D2 tt (tt, g)) M)).
smt.
clear G.
move => G.
have q : forall (g : glob A),  mu1 (D1 tt g0) (tt,g) > 0%r => mu (D2 tt (tt,g)) M < p .
smt.

have q2 : exists g, 0%r < mu1 (D1 tt g0) (tt, g).
case (exists (g : (glob A)), 0%r < mu1 (D1 tt g0) (tt, g)). auto.
move => q21.
have q22  : forall (g : (glob A)), 0%r = mu1 (D1 tt g0) (tt, g).
smt. clear q21.
have : Pr[RCR(A).main(tt, tt) @ &m : true ] = 0%r.
rewrite -  (H1 &m predT). 
rewrite dlet_mu_main. 
apply sum0_eq. progress. 
 have -> : x = (tt, x.`2). smt.
rewrite - q22. smt. smt.




elim q2. move => g gp.

have : mu (dlet (D1 tt (glob A){m}) (D2 tt)) M < p.
rewrite  dlet_mu_main.
print sum_split.
rewrite (sum_split _ (pred1 (tt, g))). 
have ->: (fun (a : unit * (glob A)) => mu1 (D1 tt (glob A){m}) a * mu (D2 tt a) M)
  = (fun (a : unit * (glob A)) => mass (D1 tt (glob A){m}) a * mu (D2 tt a) M).
apply fun_ext.  move => x. smt.

apply (summable_mass_wght ((D1 tt (glob A){m})) (fun x => mu (D2 tt x) M)   _) .
smt.

simplify.
have -> : sum
  (fun (x : unit * (glob A)) =>
     if  pred1 (tt, g) x then mu1 (D1 tt (glob A){m}) x * mu (D2 tt x) M
     else 0%r) = mu1 (D1 tt (glob A){m}) (tt,g) * mu (D2 tt (tt,g)) M.
  have ->: (fun (x : unit * (glob A)) =>
     if  pred1 (tt, g) x then mu1 (D1 tt (glob A){m}) x * mu (D2 tt x) M
     else 0%r) = (fun (x : unit * (glob A)) => mu1 (D1 tt (glob A){m}) (tt,g) * mu (D2 tt (tt,g)) M *
     if  pred1 (tt, g) x then (mass (duniform [(tt,g)]) x)
     else 0%r).
apply fun_ext. move => x.  
case (pred1 (tt, g) x). simplify. progress.
rewrite H4. 
have -> : mass (duniform [(tt, g)]) (tt, g) = 1%r. smt. smt.
smt.

rewrite sumZ. 


rewrite - muE. progress.
have ->: mu1 (duniform [(tt, g)]) (tt, g) = 1%r. smt. smt.

have zzz : sum
  (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 tt (glob A){m}) x * mu (D2 tt x) M
     else 0%r) <= sum
  (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 tt (glob A){m}) x * p
     else 0%r).
apply ler_sum. progress. 
case (pred1 (tt, g) x). simplify. auto. simplify. progress.
have ->: x = (tt,x.`2). smt.
case (mu1 (D1 tt (glob A){m}) (tt, x.`2) = 0%r). 
smt.
smt.

have ->: (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 tt (glob A){m}) x * mu (D2 tt x) M
     else 0%r) = (fun (x : unit * (glob A)) => mass (D1 tt (glob A){m}) x * 
     if ! pred1 (tt, g) x then mu (D2 tt x) M
     else 0%r).
apply fun_ext. move => x. smt.
apply summable_mass_wght. progress. smt. smt.
have -> : (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 tt (glob A){m}) x * p else 0%r)
 = (fun (x : unit * (glob A)) => p *
     if ! pred1 (tt, g) x then mass (D1 tt (glob A){m}) x else 0%r).
apply fun_ext. move => x. smt.
apply summableZ.
have ->: (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mass (D1 tt (glob A){m}) x else 0%r)
 = (fun (x : unit * (glob A)) => mass (D1 tt (glob A){m}) x *
     if ! pred1 (tt, g) x then 1%r else 0%r).
smt.
apply summable_mass_wght. progress. smt. smt.
have : mu1 (D1 tt (glob A){m}) (tt, g) * mu (D2 tt (tt, g)) M +
sum
  (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 tt (glob A){m}) x * p
     else 0%r) < p.


apply (ler_trans1 _ (mu1 (D1 tt (glob A){m}) (tt, g) * p +
sum
  (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 tt (glob A){m}) x * p else 0%r) )  p _ _).
clear zzz G H H0 H1. 

have : mu (D2 tt (tt, g)) M
 <  p.
smt.
smt.


have ->: mu1 (D1 tt (glob A){m}) (tt, g) * p +
 sum
  (fun (x : unit * (glob A)) =>
     if ! pred1 (tt, g) x then mu1 (D1 tt (glob A){m}) x * p else 0%r)
  = sum
  (fun (x : unit * (glob A)) =>
      mu1 (D1 tt (glob A){m}) x * p).
search sum.
print sumD1.
rewrite (sumD1 (fun (x : unit * (glob A)) => mu1 (D1 tt (glob A){m}) x * p) (tt,g)). 
have ->: (fun (x : unit * (glob A)) => mu1 (D1 tt (glob A){m}) x * p) 
 = (fun (x : unit * (glob A)) => p * mu1 (D1 tt (glob A){m}) x ).
smt.
apply summableZ.
apply summable_mu1.


simplify. auto.



have ->: sum (fun (x : unit * (glob A)) => mu1 (D1 tt (glob A){m}) x * p)
 = p * sum (fun (x : unit * (glob A)) => mu1 (D1 tt (glob A){m}) x).
rewrite - sumZ.  smt.
 have ->: (fun (x : unit * (glob A)) => mu1 (D1 tt (glob A){m}) x) 
 = (fun (x : unit * (glob A)) => if predT x then mass (D1 tt (glob A){m}) x else 0%r).
smt.
rewrite - muE. 



smt.
smt.


rewrite H1. smt.

qed.

lemma ZzZ &m M i1 i2 p: 
       p <= Pr[ RCR(A).main(i1,i2) @ &m : M (glob A) ] 
   => 0%r < p
   => exists &n, p <= Pr[ A.ex2(tt, tt) @ &n  : M (glob A)] .
elim (www &m p). progress.
elim (H2 M _ _);auto. smt. progress.
have f1 : Pr[A.ex1() @ &m : glob A = g] > 0%r.
have f2 : mu (D1 tt (glob A){m}) (fun x => snd x = g)  = Pr[A.ex1() @ &m : (glob A) = g].
rewrite (H &m ). auto. smt. 
have f3: exists &n, g = (glob A){n}.
  have  f31: Pr[A.ex1() @ &m : (glob A) = g /\ (exists &n, (glob A) = (glob A){n}) ] = Pr[A.ex1() @ &m : (glob A) = g].
  have <- : Pr[A.ex1() @ &m : (glob A) = g] = Pr[A.ex1() @ &m : (glob A) = g /\ exists &n, (glob A) = (glob A){n}].
  rewrite Pr[mu_split exists &n, (glob A) = (glob A){n}].
  have : Pr[A.ex1() @ &m : (glob A) = g /\ ! (exists &n, (glob A) = (glob A){n})] = 0%r. smt. smt. auto.
  have f32 : Pr[A.ex1() @ &m : (glob A) = g /\ exists &n, g = (glob A){n}] =
     Pr[A.ex1() @ &m : (glob A) = g].
  rewrite - f31. rewrite Pr[mu_eq]. progress. auto.
  have f33 : Pr[A.ex1() @ &m : exists &n, g = (glob A){n}] > 0%r.
         have f331 : Pr[A.ex1() @ &m : (glob A) = g /\ exists &n, (glob A) = (glob A){n}] 
                         <= Pr[A.ex1() @ &m : (glob A) = g]. smt.
       smt.
  clear f32 f31 f1    H2 H1 H0 H. 
  case (exists &n, g = (glob A){n}). auto.
  move => q. 
   have : Pr[A.ex1() @ &m : exists &n, g = (glob A){n}] = Pr[A.ex1() @ &m : false]. 
   rewrite Pr[mu_eq]. progress. auto. smt.
elim f3. progress.
exists &n.
rewrite -  (H0 &n M tt tt). auto.
qed.



module type IR1R2 = {
  proc init() : unit
  proc run1() : bool
  proc run2() : bool
}.

module P(A : IR1R2) = {
  proc main1() = {
    var r : bool;
    A.init();
    r <- A.run1();
    return r;
  }

  proc main2() = {
    var r : bool;
    A.init();
    r <- A.run2();
    return r;
  }

  proc init_main12() = {
   var b, r', r : bool;

   A.init();
   b <$ {0,1};
   
   if(b){
     r <@ A.run1();
   }else{
     r' <@ A.run2();
     r  <- !r;
   }
   return r;
  }

  proc main12() = {
   var b, r', r : bool;
   b <$ {0,1};
   
   if(b){
     r <@ A.run1();
   }else{
     r' <@ A.run2();
     r  <- !r;
   }
   return r;
  }


}.

section.

declare module A : IR1R2.

op f (x : real) : real = 1%r/2%r * (1%r + x).
op fop (x : real) : real = 2%r * x - 1%r.

lemma f_pr1 (a b : real) : a <= b => f a <= f b.
smt.
qed.


lemma f_pr2 (a b : real) : f a <= f b => a <= b.
smt.
qed.

lemma f_pr3 (a  : real) : f (fop a) = a.
smt.
qed.

lemma f_pr4 (a  : real) : fop (f a) = a.
smt.
qed.


lemma f_pr5 (a b : real) : a <= b => fop a <= fop b.
smt.
qed.

lemma f_pr6 (a b : real) : fop a <= fop b =>  a <= b.
smt.
qed.



lemma d_b1 &m : Pr[ P(A).init_main12() @ &m : res ] 
  = f (Pr[ P(A).main1() @ &m : res ] - Pr[ P(A).main2() @ &m : res ]) .
admitted.

lemma d_b2 &m : Pr[ P(A).main12() @ &m : res ] 
  = f (Pr[ A.run1() @ &m : res ] - Pr[ A.run2() @ &m : res ]) .
admitted.


lemma d_b3 &m p : p <= Pr[ P(A).init_main12() @ &m : res ] 
   => exists &n, p <= Pr[ P(A).main12() @ &n : res ].
admitted.


lemma o_o &m p: 
       p <=  Pr[ P(A).main1() @ &m : res ]  - 
               Pr[ P(A).main2() @ &m : res ]
   => exists &n, p <= Pr[ A.run1() @ &n : res ] - Pr[ A.run2() @ &n : res ].
progress.
have f1 : Pr[P(A).main1() @ &m : res] - Pr[P(A).main2() @ &m : res]
  = fop (Pr[ P(A).init_main12() @ &m : res ] ).
rewrite d_b1. smt.
have f2 : p <= fop Pr[P(A).init_main12() @ &m : res].
smt.
have f3 : f p <= Pr[P(A).init_main12() @ &m : res]. smt.
have f4 : exists &n,  f p <= Pr[ P(A).main12() @ &n : res ].
apply (d_b3 &m (f p)). auto.
elim f4. progress.
exists &n.
smt.
qed.
  


   
