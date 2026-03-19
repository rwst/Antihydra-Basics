New Plan for density_one_third_all_odd_contradiction                                                    
                  
  Strategy: "All S-elements odd" forces parity eventual periodicity, contradicting                        
  parity_not_eventually_periodic.
                                                                                                          
  Step 1: Gap structure

  Let m₁ < m₂ < ... be the (infinite) S-elements beyond M, all with Diter odd. Let gᵢ = mᵢ₊₁ - mᵢ (each a 
  positive multiple of 3). Between mᵢ and mᵢ₊₁, exactly gᵢ/3 of the parity bits are 1.
                                                                                                          
  Helper: OddCount_gap (m d : ℕ) (hm : m ∈ S) (hmd : m + d ∈ S) : OddCount(m + d) - OddCount(m) = d / 3   
   
  Step 2: Show gaps are bounded                                                                           
                  
  This is the key technical step. The deficit h(n) = 3·OddCount(n) - n walks with steps +2 (odd) or -1    
  (even). At each S-element: h = 0, next step is +2.
                                                                                                          
  Claim: Gaps are bounded by some B depending only on the orbit.                                          
   
  Argument: At S-element m, Diter(m) is odd and ≡ 1 mod 4 (forced by next-step parity if gap = 3) or ≡ 3  
  mod 4 (if gap > 3). The subsequent parity bits are determined by the orbit values, which grow as
  ~K·(3/2)^k. After a bounded number of D-applications, the orbit values mod 2^N cycle through all        
  residues with the specific structure from mul3_order_ZMod_pow2. This forces h to return to 0 within
  bounded time.

  Open question: This step is the hardest. It requires showing that the D-recurrence's mixing properties  
  (order of 3 in (Z/2^N)×) prevent h from staying away from 0 for too long when Diter is always odd at
  S-elements.                                                                                             
                  
  Helper: gap_bounded (M : ℕ) (hM : ∀ m ≥ M, m ∈ S → Odd (Diter m 7)) : ∃ B, ∀ consecutive m m' ∈ S with m
   ≥ M, m' - m ≤ B
                                                                                                          
  Step 3: Bounded gaps → eventual periodicity of parities                                                 
   
  With gaps bounded by B, the parity block between consecutive S-elements has length ≤ B. The block's     
  content is determined by Diter(mᵢ) mod 2^N for N = f(B). Since Diter(mᵢ) mod 2^N takes finitely many
  values, by pigeonhole the block types eventually cycle → the full parity sequence is eventually         
  periodic.       

  Helper: parity_block_determined (m : ℕ) (N : ℕ) : ...  (the parity of Diter(m+j) for j < B is determined
   by Diter(m) mod 2^N)
                                                                                                          
  Caution: D is NOT well-defined mod 2^N (D_not_well_defined_mod_pow2). But for the specific orbit        
  starting at 7, consecutive values are related by D, and D(x) mod 2 = (x/2) mod 2. So parity IS
  determined by higher bits. We need Diter(m) mod 2^(N+1) to determine Diter(m+1) mod 2^N, etc. After j   
  steps, we need Diter(m) mod 2^(N+j).

  So for a block of length B, we need Diter(mᵢ) mod 2^(N+B). The set of possible values is still finite → 
  pigeonhole still works.
                                                                                                          
  Helper: D_mod_shift (n N : ℕ) : D(n) mod 2^N is determined by n mod 2^(N+1)                             
   
  Step 4: Contradiction                                                                                   
                  
  Apply parity_not_eventually_periodic to the eventual periodicity from Step 3.                           
   
  Summary of required helper lemmas (sorry stubs):                                                        
                  
  1. D_mod_determined (n a b : ℕ) (N : ℕ) (h : a % 2^(N+1) = b % 2^(N+1)) : D a % 2^N = D b % 2^N         
  2. gap_bounded_of_all_odd — gaps between consecutive S-elements are bounded when all are odd
  3. all_odd_implies_parity_eventually_periodic — combining steps 2 and 3                                 
                                                                                                          
  Main risk                                                                                               
                                                                                                          
  Step 2 (gap boundedness) is the hardest part and may require a different argument. An alternative is to 
  bypass gap boundedness entirely and argue more directly about the series for K(3,7), showing that the
  "all odd at S-elements" constraint forces enough structure in the parity sequence to make K(3,7)        
  rational.       

