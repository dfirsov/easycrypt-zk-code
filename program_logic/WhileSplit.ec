require import AllCore.

type sbits, iat, rrt, irt.

module type HasRun = {
  proc run(z : irt) : rrt {}
}.


module W(A : HasRun) = {
  var c : int



  proc whp(p : rrt -> bool, i : irt, s : int, e : int, r : rrt) = {
    c <- s;
    while(c <= e /\ !p r){
     r <- A.run(i);
     c <- c + 1;
    }
    return r;
  }


  proc if_whp(p : rrt -> bool, i : irt, s : int, e : int, r : rrt) = {
    c <- s;
    if(c <= e /\ !p r){
     r <- A.run(i);
     c <- c + 1;
    }
    r <- whp(p,i,W.c,e,r);
    return r;
  }

  proc whp_if(p : rrt -> bool, i : irt, s : int, e : int, r : rrt) = {
    var ri;
    c <- s;
    ri <- whp(p,i,s,e-1,r);
    if(c <= e /\ !p ri){
     ri <- A.run(i);
     c <- c + 1;
    }
    return ri;
  }

  proc whp_split(p : rrt -> bool, i : irt, s : int, m : int, e : int, r : rrt) = {
    c <- s;
    r <- whp(p,i,s,m,r);
    r <- whp(p,i,W.c,e,r);
    return r;
  }
  
}.
