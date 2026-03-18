Foundational: precision loss of D                                                                       
   
  1. D_mod_determined — D(a) ≡ D(b) mod 2^N whenever a ≡ b mod 2^(N+1). One bit consumed per step.        
  2. D_mod_exact — The loss is exact: if the inputs agree mod 2^(N+1) but disagree mod 2^(N+2), the     
  outputs agree mod 2^N but disagree mod 2^(N+1). (Because D(a)-D(b) = 3(a-b)/2 and 3 is odd.)            
                                                                                                        
  Iterated versions                                                                                       
                                                                                                        
  3. Diter_mod_determined — k applications of D consume exactly k bits: Diter k a ≡ Diter k b mod 2^N when
   a ≡ b mod 2^(N+k).
  4. Diter_mod_exact — Exact iterated version: the disagreement bit propagates downward at one bit per    
  step. This IS the 2-adic expansion property.                                                            
   
  Orbit structure                                                                                         
                                                                                                        
  5. Diter_7_strictMono — The orbit is strictly increasing (since D(n) > n for n ≥ 1).                    
  6. Diter_7_injective — The orbit never revisits a value. (Derived from strictMono, not sorry.)
                                                                                                          
  Pigeonhole consequences                                                                                 
                                                                                                          
  7. Diter_mod_periodic_finite_stretch — For any N and stretch L, pigeonhole yields M, T with mod 2^N     
  periodicity for L steps. (Choose precision P = N+L, find collision in first 2^P+1 values.)            
  8. Diter_mod_agreement_degrades — The self-limiting property: a collision with L bits of surplus        
  precision yields at most ⌊L/T⌋ periods of mod 2^N agreement before the expansion eats through the       
  surplus and periodicity breaks.
                                                                                                          
  How these connect to non-periodicity                                                                    
   
  The chain for proving not_Diter_mod_eventually_periodic WITHOUT K37_irrational:                         
  - Lemma 7 shows pigeonhole gives finite stretches of periodicity                                      
  - Lemma 8 shows these stretches inevitably expire (due to 2-adic expansion, Lemma 4)                    
  - Together they explain WHY infinite periodicity can't arise from finite-state arguments              
  - To actually prove non-periodicity, one still needs either K37 irrationality or a direct argument      
  showing no collision is "self-reinforcing"         
