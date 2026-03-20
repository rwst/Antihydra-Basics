# Proof Plan: conj1_iff_conj2

## Objective
We want to prove the main equivalence theorem in `AntihydraBasics/Parity.lean`:
```lean
theorem conj1_iff_conj2 : Conj1 ↔ Conj2
```
This theorem establishes that Conjecture 1 (the avoidance of the $1/3$ density trapping condition) is logically equivalent to Conjecture 2 (the asymptotic odd density converging to exactly $1/2$).

---

## Part 1: Proving `Conj1 ⟹ Conj2` (Avoidance implies Density 1/2)

**Strategy:** Use the established modular periodicity and equidistribution properties.

1. **Assume `Conj1`:** Assume the forbidden configuration never occurs.
2. **Invoke Equidistribution:** Apply `equidistributed_mod_pow2_of_Conj1` with $N = 1$. The preconditions are satisfied since $N \ge 1$ and we assume `Conj1`.
3. **Extract Periodicity:** The lemma provides an eventual period $T \ge 2$ and a starting index $S$ such that for all $k \ge S$, $D(k+T) \equiv D(k) \pmod 2$. This means the parity sequence is eventually strictly periodic.
4. **Extract Density:** The lemma also guarantees that the sum of the parities over one full period $T$ is exactly $T/2$.
5. **Compute the Limit:** Since the sequence of parities is eventually periodic, its Cesàro mean (the running density $\rho(n) = OddCount(n)/n$) converges exactly to the average of the period.
   $$ \lim_{n \to \infty} \frac{OddCount(n)}{n} = \frac{T/2}{T} = \frac{1}{2} $$
6. **Conclude `Conj2`:** This limit is the exact definition of `Conj2` (`Tendsto oddDensity atTop (𝓝 (1 / 2 : ℝ))`).

---

## Part 2: Proving `Conj2 ⟹ Conj1` (Density 1/2 implies Avoidance)

**Strategy:** We can prove this direction either by contrapositive (leveraging the trapping dynamics of the sequence) or directly via the convergence bound. We outline the direct convergence bound approach as it avoids needing to define the infinite trapping cycle explicitly.

1. **Assume `Conj2`:** The sequence $\rho(n) = OddCount(n)/n$ converges to $1/2$.
2. **Establish a Lower Bound:** By the definition of the limit, there exists an index $N$ such that for all $n \ge N$, the density is strictly greater than a threshold above $1/3$. For example, choose $\epsilon = 1/12$. Then for all $n \ge N$, $\rho(n) > 1/2 - 1/12 = 5/12 > 1/3$.
3. **Consequence for Large $n$:** For all $m \ge N$, we have $OddCount(m) > m/3$. Therefore, no $m \ge N$ can possibly satisfy the condition $OddCount(m) = m/3$.
4. **Finite Prefix Checking:** This leaves only a finite set of candidates $m < N$ that are multiples of $3$. 
5. **No Candidates Exist:** Because the sequence $D(m)$ starting from $D(0) = 7$ is entirely deterministic, the initial values can be evaluated. By proving a computational lower bound (or leveraging the sequence's known empirical prefix), we can show that for all $m < N$, the combination of $3 \mid m$, $Even(D(m))$, $D(m) \ge 5$, and $OddCount(m) = m/3$ is never satisfied.
6. **Conclude `Conj1`:** Since the condition fails for $m \ge N$ due to the asymptotic limit, and fails for $m < N$ by finite evaluation, there is no $m$ that satisfies the forbidden condition. Thus, `Conj1` holds.

### Alternative Contrapositive for Part 2 (`¬Conj1 ⟹ ¬Conj2`)
If finite bounds are difficult to evaluate purely formally in Lean, the contrapositive is mathematically elegant:
1. Assume `¬Conj1`, meaning there is some $m$ where the exact parity deficit occurs.
2. This state corresponds to the halting configuration of the Antihydra Turing machine.
3. Due to the "trapping condition" of the map's arithmetic, hitting this state forces the sequence's modular behavior into a rigid cycle that perpetually maintains the parity deficit, causing the sequence mod 2 to become eventually periodic with an average density of exactly $1/3$.
4. By `Diter_mod_pow2_eventually_periodic`, the limit exists, and because of the trap, the limit is $1/3$.
5. Since $1/3 \neq 1/2$, `Conj2` is false.

## Conclusion
The combination of these two steps formally connects the behavior of the localized arithmetic obstacle (`Conj1`) to the global asymptotic density of the sequence (`Conj2`), completing the equivalence.