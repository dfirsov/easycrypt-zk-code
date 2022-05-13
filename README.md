
Generic definitions
====================

+ ZK (stat/comp)
+ Completeness (stat)
+ Special soundness (stat/comp)
+ Soundness (stat/comp)
+ PoK (stat/comp)


- Amplified variants of the defs

Generic Results
================

+ 1-time sim => ZK   (for small "challenge_set", OneToManyZK.ec)
   + stat
   + comp
 

+ Special soundness => extractability (Generic_KE.ec)
  + perf special soundness => stat extra
  + comp


+ extractability => soundness (stat/comp)
  + stat
  + comp


- Amplification
  - completeness (not an amplification but a lack of degradation)
  - soundness
  - ZK (not an amplification but a lack of degradation)
  - PoK
  

- perfect => statistical => computational (Maybe not, runtime? (likely not))


Concrete Results
================

+ QR:
  + Completeness
  + Special soundness (perfect)
  + soundness (stat)
  + Sim1 stuff (perfect)
  + auto-derived ZK (stat)
  + auto-derived extractability (stat)


+ DL:
  + Completeness
  + Special soundness (perfect)
  + auto-derived extractability (stat)
  + NO soundness (meaningless)
  + NO ZK 


- HC (stat hiding / comp binding):
  + Completeness
  + Special soundness (comp)
  + Sim1 
  + auto-derived ZK (stat)
  + auto-derived extractability (comp)
  + auto-derived soundness (comp)



