Instead, for density_one_third_all_odd_contradiction, consider:

  1. Direct approach without periodicity: Show "all S-elements odd" directly contradicts the orbit
  structure, using D_parity, the deficit walk, and modular constraints (Steps 1-2 above are useful helpers
   regardless).
  2. Weaker density statement: Instead of full periodicity, prove that the density OddCount(n)/n has
  subsequential limits, and use the "all odd" assumption to constrain those limits.
  3. Computational verification for bounded N: For the specific orbit starting at 7, verify the needed
  properties for small N by decide/native_decide, sidestepping the general statement.


/-- If S = {m | 3 ∣ m ∧ OddCount m = m/3} is infinite but all sufficiently large
    S-elements have Diter odd, we derive a contradiction.

    This is unprovable at the moment.
-/
lemma density_one_third_all_odd_contradiction
    (hS_inf : Set.Infinite {m : ℕ | 3 ∣ m ∧ OddCount m = m / 3})
    (M : ℕ) (hM : ∀ m ≥ M, 3 ∣ m → OddCount m = m / 3 → Odd (Diter m 7)) :
    False := by sorry

/-- **Critical Lemma 1 / Key Lemma (Variant C).**
Among all m ≡ 0 (mod 3) with O(m) = m/3, infinitely many have Diter m 7 even.
(Equivalently, the set {m | 3 ∣ m ∧ O(m) = m/3 ∧ Even (Diter m 7)} is infinite.) -/
lemma infinitely_many_even_at_density_one_third
    (h : Set.Infinite {m : ℕ | 3 ∣ m ∧ OddCount m = m / 3}) :
    Set.Infinite {m : ℕ | 3 ∣ m ∧ OddCount m = m / 3 ∧ Even (Diter m 7)} := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  -- S_even is finite → bounded above in ℕ
  obtain ⟨M, hM⟩ := hfin.bddAbove
  -- Beyond M, all S-elements must have Diter odd → contradiction via mixing
  exact density_one_third_all_odd_contradiction h (M + 1) fun m hm h3 hoc => by
    rcases Nat.even_or_odd (Diter m 7) with heven | hodd
    · exact absurd (hM ⟨h3, hoc, heven⟩) (by omega)
    · exact hodd


---

## Conclusion on the Direct Approach (Without Periodicity)

As investigated in `gemini-argument.md`, the direct approach to proving `infinitely_many_even_at_density_one_third` (or deriving a contradiction from "all S-elements odd") is mathematically impossible using only local modular constraints and the deficit walk $h(n) = 3 \cdot OddCount(n) - n$.

### 1. The 2-Adic Traps
The goal of the contradiction is to show that $h(n)$ cannot stay non-negative forever if it starts at 0 with an odd step. However, it is a mathematical fact that within the space of 2-adic integers ($\mathbb{Z}_2$), there exist uncountably many sequences of parities that satisfy $h(n) \ge 0$ forever and "bounce" off the zero line strictly using odd values. 

For instance, the repeating sequence of operations `odd, even, even` corresponds to the parity map generating $h(m)=0 \to 2 \to 1 \to 0$. By carefully choosing a 2-adic integer (e.g. one ending in $x \equiv 35 \pmod{64}$), the map $x \mapsto \lceil \frac{3x}{2} \rceil$ will generate this exact sequence.

### 2. The Global vs Local Obstruction
Because these "density 1/3 traps" genuinely exist as valid sequences under the 2-adic extension of the $D(n)$ map, no finite amount of modular arithmetic or local parity tracing can rule them out. 

To prove that the specific sequence starting at $D(0) = 7$ avoids all of these 2-adic traps, one must invoke the global growth constraint: $D(n) = \lfloor K(3) (3/2)^n \rfloor$. This requires proving bounds on the fractional parts $\{ K(3) (3/2)^n \}$ to show they do not align with the 2-adic traps.

This reduction directly links the statement back to Mahler's $3/2$ problem and transcendence theory. There is no elementary path forward via pure combinatorics or modular properties of the sequence.

---

## Conclusion on the Weaker Density Statement (Subsequential Limits)

The second proposed idea—proving that the density `OddCount(n)/n` has subsequential limits and using the "all odd" assumption to constrain those limits to derive a contradiction—fails for the exact same foundational reason.

### 1. Limits are Perfectly Consistent with the Traps
If we assume that all S-elements are odd (meaning $h(n) \ge 0$ forever), this local constraint only guarantees that the odd density $\rho(n) \ge 1/3$ asymptotically. Does this constraint force a contradiction in the limit? 

No. For the 2-adic sequences mentioned above (such as the repeating sequence of operations `odd, even, even`), the sequence of running densities $\rho(n)$ converges precisely and stably to $1/3$. This is a perfectly valid mathematical limit that satisfies all local modular arithmetic rules of the $D(n)$ map without forcing any contradictions.

### 2. The Unbridgeable Gap
Because a mathematically valid 2-adic sequence exists that satisfies the "all odd" condition *and* has a subsequential limit of $1/3$, there is no possible combinatorial or real-analysis argument on the limits themselves that could yield a contradiction. The contradiction does not lie in the limits of the local rules.

To prove that the specific sequence starting at $D(0)=7$ does not have a subsequential limit of $1/3$, you must again differentiate the integer sequence from the 2-adic traps. This strictly requires invoking the global real-number growth constraint $D(n) = \lfloor K(3) (3/2)^n \rfloor$ and proving that it is incompatible with the 2-adic trap, which immediately returns us to Mahler's $3/2$ problem.

