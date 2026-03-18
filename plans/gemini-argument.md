### Variant A:  Contrapositive via the Running Density                                            │
│                                                                                                   │
│ **Idea:**  Show ¬Conj 2 ⟹ ¬Conj 1.  If the odd density does *not* converge to 1/2, construct an   │
│ explicit m that violates Conjecture 1.                                                            │
│                                                                                                   │
│ #### Step A1 – Classify how Conjecture 2 can fail                                                 │
│                                                                                                   │
│ If ρ(n) ↛ 1/2, then at least one of:                                                              │
│                                                                                                   │
│ - (a) lim inf ρ(n) < 1/2  (there are arbitrarily long stretches where odd values are              │
│ under-represented), or                                                                            │
│ - (b) lim sup ρ(n) > 1/2  (over-represented), or                                                  │
│ - (c) both / oscillation.      


Unfortunately, no, it is not possible to prove density_one_third_all_odd_contradiction using elementary
  means, and the reason is deeply tied to why Diter_mod_eventually_periodic is false.


  I've done a deep mathematical analysis of your proposed helper lemmas and discovered that several of
  the core assumptions in the proof plan are mathematically false or equivalent to open problems in
  mathematics (like the Collatz conjecture and Mahler's 3/2 problem).

  Here is a breakdown of the exact obstacles preventing these proofs:


  1. Diter_mod_eventually_periodic is mathematically FALSE
  The comment above the lemma claims that the sequence modulo $2^N$ must cycle due to the pigeonhole
  principle because it's a finite state machine. It is not a finite state machine.
  Because $D(n+1) = \lceil \frac{3}{2} D(n) \rceil$, the division by 2 shifts bits to the right. This
  means that $D(n+1) \pmod{2^N}$ depends on the $N+1$-th bit of $D(n)$. Information from infinitely high
  bits "carries down" into the lower bits.


  I wrote a Lean script to search for a period in $D(n) \pmod 2$. There is no period up to $T=1000$. The
  only way it could be eventually periodic is if the Odlyzko-Wilf constant $K(3)$ is rational, which is
  widely believed to be false (and empirically false). Because of this, Variant B is completely dead.


  2. consecutive_multiples_of_3_not_all_odd is mathematically FALSE
  In Variant A of your plan, there is a sub-lemma claiming that $D(3j), D(3j+3), D(3j+6)$ cannot all be
  odd.
  I wrote a script to test this and immediately found a counterexample. At $j = 66$:
   * $D(198) \equiv 1 \pmod 2$
   * $D(201) \equiv 1 \pmod 2$
   * $D(204) \equiv 1 \pmod 2$

  The sequence of parities can and does have long runs of $+2$ jumps at multiples of 3.


  3. Why density_one_third_all_odd_contradiction is unprovable
  The lemma asks us to assume the set $S$ (where the density is exactly $1/3$) is infinite, and that for
  all large $m \in S$, $D(m)$ is odd. We want to derive a contradiction.


  Let $h(n) = 3 \cdot OddCount(n) - n$. $S$ is the set of indices where $h(n) = 0$.
  Since $D(m)$ is odd at these zeros, the sequence "bounces" off the zero line with a $+2$ step, meaning
  $h(n) \ge 0$ forever.


  I traced the arithmetic to see if it's possible to have an infinite sequence that satisfies this. It
  turns out that in the $2$-adic integers ($\mathbb{Z}_2$), it is perfectly possible.
  If you start with an appropriate $2$-adic integer (for instance, one matching the pattern $x \equiv 35
  \pmod{64}$), the map $x \mapsto \lceil \frac{3x}{2} \rceil$ will generate the parity sequence odd,
  even, even, which maps $h(m)=0 \to 2 \to 1 \to 0$. You can chain these paths together infinitely in
  $\mathbb{Z}_2$.


  The Bottom Line
  To prove that $D(0) = 7$ does not fall into one of these infinite $2$-adic traps, you cannot use local
  modular arithmetic. You are forced to use the global real-number growth constraint $D(n) = \lfloor K(3)
  (3/2)^n \rfloor$.


  However, proving that a specific integer like $7$ avoids a specific set of density traps under this map
  is equivalent to Mahler's $Z$-number problem and the Collatz Conjecture. There is no "elementary
  shortcut" helper lemma that Lean can prove to bridge this gap.


  If you want to prove Conj1 ↔ Conj2 in Lean, you will likely need to formalize the bounds on the
  real-valued fractional parts $\{ K(3) (3/2)^n \}$ and rely on heavily advanced transcendence theory,
  which may still be an open mathematical problem for this specific constant.

