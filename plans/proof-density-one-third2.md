Plan for density_one_third_all_odd_contradiction                                                        
   
  Given (from the sorry stub's hypotheses + the restored stub):                                           
  - hS_inf: S is infinite
  - hM: all S-elements ≥ M have Diter odd                                                                 
  - Diter_mod_eventually_periodic: orbit mod 2^N is eventually periodic
                                                                                                          
  Goal: False                                                                                             
                                                                                                          
  Step 1: Parity eventually periodic                                                                      
                  
  Instantiate Diter_mod_eventually_periodic with N=1. Get period T > 0 and offset M₀ such that Diter(k+T, 
  7) % 2 = Diter(k, 7) % 2 for all k ≥ M₀.
                                                                                                          
  Helper: parity_eventually_periodic (trivial wrapper)                                                    
   
  Step 2: Density converges to average over one period                                                    
                  
  Since parities repeat with period T past M₀, OddCount(n) grows like (n · ρ_T) where ρ_T = (# odd bits in
   one period) / T. Standard Cesàro argument: OddCount(n)/n → ρ_T.
                                                                                                          
  Helper: density_converges_of_eventually_periodic (T M₀ : ℕ) (hT : T > 0) (h_per : ...) : Tendsto (fun n 
  => (OddCount n : ℝ) / n) atTop (𝓝 ρ_T) — sorry stub
                                                                                                          
  Step 3: ρ_T = 1/3

  S infinite means OddCount(mᵢ)/mᵢ = 1/3 for mᵢ → ∞. A convergent sequence that hits 1/3 on a subsequence 
  tending to ∞ must have limit 1/3. So ρ_T = 1/3, meaning exactly T/3 bits in one period are odd (and 3 ∣
  T).                                                                                                     
                  
  Helper: density_limit_eq_one_third (hS_inf : ...) (h_conv : Tendsto ... (𝓝 ρ)) : ρ = 1/3 — sorry stub   
   
  Step 4: h is eventually periodic, S becomes periodic                                                    
                  
  h(n) = 3·OddCount(n) - n has net change 0 per period (since density = 1/3). So h is eventually periodic 
  with period T. The S-elements (multiples of 3 where h = 0) form a periodic pattern. In the tail, there
  is a fixed set of positions within each period where S-elements occur.                                  
                  
  Helper: h_eventually_periodic — sorry stub                                                              
   
  Step 5: Equidistribution forces density ≠ 1/3 (the deep step)                                           
                  
  This is the core. The orbit mod 2^N is eventually periodic. By mul3_order_ZMod_pow2, the element 3 has  
  order 2^(N-2) in (Z/2^N Z)×. The D-map acts approximately as ×(3/2), so the orbit visits residue classes
   with frequencies governed by this group action. For large N, approximately half the residues give odd  
  D-values, forcing density → 1/2.

  Combined with "all S-elements odd" (which removes the only mechanism that could distort the density away
   from 1/2), the density must be 1/2. But Step 3 gives 1/3. Contradiction.
                                                                                                          
  Helper: equidist_density_one_half_of_all_odd (h_per : parities periodic) (hM : all large S-elements odd)
   : ρ_T = 1/2 — sorry stub, the hardest lemma
                                                                                                          
  Step 6: Contradiction                                                                                   
   
  Steps 3 and 5: ρ_T = 1/3 and ρ_T = 1/2. linarith or norm_num.                                           
                  
  ---                                                                                                     
  Dependency graph
                                                                                                          
  Diter_mod_eventually_periodic (sorry)
    → parity_eventually_periodic                                                                          
      → density_converges_of_eventually_periodic (sorry)
        → density_limit_eq_one_third (sorry)                                                              
      → h_eventually_periodic (sorry)                                                                     
                                                                                                          
  mul3_order_ZMod_pow2 (proved)                                                                           
  mul3_bijective_ZMod_pow2 (proved)                                                                       
    → equidist_density_one_half_of_all_odd (sorry, hardest)                                               
                                                                                                          
  density_limit_eq_one_third + equidist_density_one_half_of_all_odd → False
                                                                                                          
  Risk assessment                                                                                         
   
  - Steps 1-4 are standard real analysis / combinatorics — moderately hard to formalize but conceptually  
  clear           
  - Step 5 is the crux: the equidistribution argument bridging mul3_order to density = 1/2 is the deepest 
  part. It needs a formalization of how the D-map distributes residue classes, which is nontrivial given  
  D_not_well_defined_mod_pow2
                                    
