Detailed Plan for Diter_mod_eventually_periodic

  Statement

  ∀ N ≥ 1, ∃ T > 0, ∃ M, ∀ k ≥ M, Diter(k+T, 7) % 2^N = Diter(k, 7) % 2^N

  Step 1: D_mod_step — precision loss lemma (provable)

  Statement: D a % 2^N = D b % 2^N whenever a % 2^(N+1) = b % 2^(N+1).

  Proof sketch: a ≡ b mod 2^(N+1) implies same parity. Both cases:
  - Even: D(a) = 3(a/2), D(b) = 3(b/2). Since a/2 ≡ b/2 mod 2^N, multiply by 3.
  - Odd: D(a) = (3a+1)/2, D(b) = (3b+1)/2. Since 3a+1 ≡ 3b+1 mod 2^(N+1) and both even, divide by 2.

  Clean omega-level proof after case split.

  Step 2: D_iter_mod_step — iterated precision loss (provable)

  Statement: Diter k a % 2^N = Diter k b % 2^N whenever a % 2^(N+k) = b % 2^(N+k).

  Proof: Induction on k, applying Step 1 at each stage.

  Step 3: Pigeonhole collision (provable)

  Among Diter(0, 7), ..., Diter(2^L, 7), two agree mod 2^L by pigeonhole. Combined with Step 2, this
  gives:

  For any L: ∃ M T, T > 0 ∧ ∀ m ≤ L - T, Diter(M+m+T, 7) % 2^(L-T-m) = Diter(M+m, 7) % 2^(L-T-m)

  Setting L = N + T + R gives periodicity mod 2^N for a finite stretch of length R.

  Step 4: Extend to all k (the gap)

  This is where the proof breaks down. Here's why:

  D is 2-adically expanding. The map D acts as x ↦ (3x + ε)/2 where ε ∈ {0,1}. The iterated map D^T acts
  as:

  D^T(x) = (3^T · x + c) / 2^T

  for some constant c depending on the parity pattern. The "Lipschitz constant" in the 2-adic metric is:

  |D^T(x) - D^T(y)|₂ = |3^T/2^T|₂ · |x - y|₂ = 2^T · |x - y|₂

  Since |3|₂ = 1 (unit) and |1/2|₂ = 2, the map expands distances by a factor of 2^T. Orbits diverge from
  fixed points rather than converging to them.

  Fixed points are negative. A period-T orbit satisfies D^T(x*) = x*, giving x* = c/(2^T - 3^T). Since 3^T
   > 2^T for T ≥ 1, the denominator is negative, so x* < 0 (for c > 0). The orbit Diter(k, 7) consists of
  positive naturals growing exponentially — it never reaches a periodic point.

  Finite-stretch periodicity doesn't bootstrap. After a collision mod 2^L gives periodicity mod 2^N for R
  steps, the agreement at mod 2^(N+T) (needed to continue) has already been consumed. Each "period" costs
  T bits of precision that cannot be recovered.

  Assessment

  The 2-adic analysis strongly suggests Diter_mod_eventually_periodic is false:

  ┌───────────────────────────────────────────────────┬─────────────────────┐
  │                     Evidence                      │      Direction      │
  ├───────────────────────────────────────────────────┼─────────────────────┤
  │ D is 2-adically expanding (factor 2^T per period) │ Against periodicity │
  ├───────────────────────────────────────────────────┼─────────────────────┤
  │ All periodic points of D in Z₂ are negative       │ Against periodicity │
  ├───────────────────────────────────────────────────┼─────────────────────┤
  │ D_not_well_defined_mod_pow2 (already proved)      │ Against periodicity │
  ├───────────────────────────────────────────────────┼─────────────────────┤
  │ parity_not_eventually_periodic (modulo K37 sorry) │ Against periodicity │
  ├───────────────────────────────────────────────────┼─────────────────────┤
  │ Pigeonhole only gives finite stretches            │ Neutral             │
  └───────────────────────────────────────────────────┴─────────────────────┘

  Recommendation

  Don't add Diter_mod_eventually_periodic as a sorry stub. It is almost certainly false, and building on
  it would produce a vacuously valid but mathematically unsound proof chain.


