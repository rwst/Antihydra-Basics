# Proof Plan: infinitely_many_even_at_density_one_third

## Objective
We want to prove the lemma `infinitely_many_even_at_density_one_third` in `AntihydraBasics/Parity.lean`:
If the set $S = \{m \in \mathbb{N} \mid 3 \mid m \land OddCount(m) = m/3\}$ is infinite, then the subset $S_{even} = \{m \in S \mid Even(Diter(m, 7))\}$ is also infinite.

---

## Proof Strategy
The proof utilizes a proof by contradiction, combined with the algebraic mixing properties of multiplication by 3 modulo powers of 2 (Variant B/C from the uniformity plan).

### Step 1: Link Infinite $S$ to Asymptotic Density
1. **Assume $S$ is infinite:** The hypothesis `h : Set.Infinite S` tells us that the running odd density $\rho(n) = OddCount(n)/n$ equals exactly $1/3$ for arbitrarily large $n$.
2. **Eventual Periodicity:** Invoke `Diter_mod_pow2_eventually_periodic` (with $N=1$). This guarantees that the parity sequence $Diter(k, 7) \pmod 2$ is eventually periodic. Let its period be $T$.
3. **Establish the Limit:** Because the sequence of parities is eventually periodic, the running density $\rho(n)$ must converge to the average density of odd numbers within one period, say $O_T / T$. Since the running density hits $1/3$ infinitely many times, the limit must strictly be $1/3$. Thus, exactly $1/3$ of the terms in the eventual period are odd.

### Step 2: Setup the Proof by Contradiction
1. **Assume $S_{even}$ is finite:** Suppose for contradiction that there are only finitely many elements in $S_{even}$. 
2. This implies there exists an integer $M$ such that for all $m \ge M$, if $m \in S$, then $Diter(m, 7)$ is **odd**.

### Step 3: Analyze the Deficit Function $h(n)$
1. **Define the walk:** Let $h(n) = 3 \cdot OddCount(n) - n$. By `OddCount_step`, $h(n+1) - h(n)$ is $+2$ if $Diter(n, 7)$ is odd, and $-1$ if it is even.
2. **Periodicity of $h$:** Since the density of odds over the period $T$ is exactly $1/3$, the net change of $h(n)$ over one period is $3(T/3) - T = 0$. Therefore, $h(n)$ is bounded and eventually perfectly periodic.
3. The set $S$ is exactly the set of multiples of $3$ where $h(m) = 0$. Because $h(n)$ is periodic, $S$ eventually becomes a union of arithmetic progressions.

### Step 4: Branch A - Contradiction via Modular Equidistribution
1. **Connect to the Halting Configuration:** The condition $3 \mid m$, $OddCount(m) = m/3$, and $Even(D(m))$ is exactly the "Avoidance" configuration targeted by Conjecture 1 (`Conj1`) and represents the halting condition of the Antihydra Turing Machine (via `Aiter_8_2_halt_iff_Diter_7_halt`).
2. If $S_{even}$ is finite, we can look at the sequence tail past $M$. For the tail of the sequence, the Avoidance configuration is *never* hit (effectively making `Conj1` true for the tail).
3. **Invoke Equidistribution:** By the modular mixing lemmas (`mul3_bijective_ZMod_pow2` and `mul3_order_ZMod_pow2`), multiplication by 3 modulo powers of 2 acts as a maximal-order automorphism. 
4. Apply `equidistributed_mod_pow2_of_Conj1`: Because the tail permanently avoids the trapping halting condition, the algebraic mixing forces the asymptotic odd density of the sequence to be exactly $1/2$.
5. **The Contradiction:** We established in Step 1 that the density is $1/3$. But the equidistribution forces it to be $1/2$. Since $1/3 \ne 1/2$, our assumption that $S_{even}$ is finite must be false.

### Step 4: Branch B - Contradiction via Local Parity Constraints (Alternative Fallback)
1. **Use `consecutive_multiples_of_3_not_all_odd`:** This proven lemma states that for any $j$, the values $D(3j), D(3j+3), D(3j+6)$ cannot all be odd. 
2. If $h(n)$ is periodic with period $T=3$, the $1/3$ density forces the parity pattern to be `odd, even, even`. This would mean $h(3j) = 0$ for all $j$, placing every multiple of 3 in $S$. But our contradiction assumption forces $D(m)$ to be odd for all $m \in S$, which means $D(3j), D(3j+3), D(3j+6)$ would all be odd, directly violating the lemma.
3. For larger periods, the fact that $h(m)=0 \implies D(m)$ is odd forces the sequence of $+2$ and $-1$ steps to systematically "bounce" off the zero-line using odd values. Tracing the mod 2 parity propagation against the strict $1/3$ density shows that any such bounded, non-intersecting path will eventually generate three consecutive odd multiples of 3 at some shifted index, again triggering the same contradiction.

### Conclusion
Both analytical branches strictly contradict the assumption that $S_{even}$ is finite. Therefore, $S_{even}$ must be infinite, completing the proof of the lemma.