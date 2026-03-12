
Here is a detailed, optimized plan to prove `Diter'_asymptotic` in Lean 4. 

**Shortcut 1:** We can keep the step-by-step arithmetic entirely in `ℕ` by defining a specific integer remainder function. This avoids `Real.ceil` entirely.
**Shortcut 2:** The paper states "the right side cannot be an integer for all $n$" to get strict inequality. Formalizing this over $\mathbb{R}$ is tedious. We can translate this into a pure number-theoretic divisibility contradiction in `ℕ`, utilizing `Coprime` and powers, which is extremely elegant in Mathlib.

---

### Phase 1: Purely Natural Arithmetic (The Elegant Shortcut)
Instead of dealing with reals early on, encapsulate the floor division's remainder.
1. **Define the Error Term:** Let $E(q, n) = q - 2 - ((n - 1) \bmod (q - 1))$. 
   - Prove that for $q \ge 2$ and $n \ge 1$, we have $0 \le E(q, n) \le q - 2$. (Note: Because $n \ge 1$, $n - 1 \ge 0$, so natural number subtraction behaves perfectly).
2. **Exact Division Lemma:** Prove the foundational algebraic identity:
   `Dstep q n * (q - 1) = q * n + E(q, n)`
   *Proof Sketch:* Let $n - 1 = c(q-1) + r$. Expand $qn + q - 2$ in terms of $c$ and $r$ to show that it equals $(n + c + 1)(q-1) + r$. Division by $q-1$ yields $n + c + 1$, and subtracting $r$ yields the exact multiple.
3. **Positivity:** Prove by induction that $D_k = \text{Diter}' \ k \ q \ 1 \ge 1$ for all $k$, ensuring the modulo arithmetic never underflows.

### Phase 2: Transition to Real Sequences
Now, safely cast the exact relationship to $\mathbb{R}$.
1. **Real Definitions:** Define $\alpha = \frac{q}{q-1} \in \mathbb{R}$.
2. **Sequence of Errors:** Define $e_k = \frac{E(q, D_{k-1})}{q-1} \in \mathbb{R}$ for $k \ge 1$.
3. **The Recurrence:** From Phase 1, cast to $\mathbb{R}$ and divide by $q-1$ to prove:
   $D_k = \alpha D_{k-1} + e_k$
4. **Error Bounds:** Prove $0 \le e_k \le \frac{q-2}{q-1}$ using the bounds of $E(q, n)$.

### Phase 3: Defining the Asymptotic Constant $K$
1. **Normalized Sequence:** Define $u_k = \frac{D_k}{\alpha^k}$.
2. **Telescoping Sum:** Unfold the recurrence to prove $u_k = 1 + \sum_{j=1}^k e_j \alpha^{-j}$.
3. **Summability:** Prove that the infinite series $\sum_{j=1}^\infty e_j \alpha^{-j}$ is summable.
   *Strategy:* Bound it above by $\frac{q-2}{q-1} \alpha^{-j}$. Since $\alpha > 1$ (for $q \ge 2$), the geometric series converges.
4. **Define $K$:** Define $K = 1 + \sum_{j=1}^\infty e_j \alpha^{-j}$ (using `tsum` in Lean).

### Phase 4: Deriving the Non-Strict Error Term Limits
1. **Exact Error Formula:** Let $\epsilon_k = D_k - K \alpha^k$. 
   Multiply $K = u_k + \sum_{j=k+1}^\infty e_j \alpha^{-j}$ by $\alpha^k$ to prove:
   $\epsilon_k = - \sum_{m=1}^\infty e_{k+m} \alpha^{-m}$
2. **Upper Bound:** Because $e_m \ge 0$ and $\alpha > 0$, the sum is non-negative, proving $\epsilon_k \le 0$.
3. **The $q = 2$ Case:** If $q = 2$, then $E(2, n) = 0$, meaning $e_j = 0$ for all $j$. The infinite sum is exactly $0$, directly yielding $\epsilon_k = 0$.
4. **Non-Strict Lower Bound for $q \ge 3$:** Since $e_{k+m} \le \frac{q-2}{q-1}$, the sum is bounded by $\frac{q-2}{q-1} \sum_{m=1}^\infty \alpha^{-m}$. 
   Prove the geometric series exact value: $\sum_{m=1}^\infty \alpha^{-m} = \frac{1}{\alpha - 1} = q - 1$.
   Multiplying gives $\epsilon_k \ge -(q-2)$.

### Phase 5: The Strict Bound via Divisibility (Number Theory Shortcut)
To prove $\epsilon_k > -(q-2)$ for $q \ge 3$, proceed by contradiction.
1. **Equality Implies Constant Error:** Assume $\epsilon_k = -(q-2)$. Because the terms $e_{k+m}$ are bounded by $\frac{q-2}{q-1}$, achieving the maximum possible sum requires $e_{k+m} = \frac{q-2}{q-1}$ for all $m \ge 1$.
   *(In Lean, frame this as $\sum (\frac{q-2}{q-1} - e_{k+m}) \alpha^{-m} = 0$, which implies each non-negative term is $0$).*
2. **The Constant Recurrence:** If $e_{k+m} = \frac{q-2}{q-1}$, then $E(q, D_{k+m-1}) = q-2$.
   Plugging this back into Phase 1's exact division gives $D_{k+m} = \frac{q D_{k+m-1} + q - 2}{q-1}$.
3. **The Auxiliary Sequence:** Define a shifted sequence $y_n = D_n + q - 2$.
   Prove that the recurrence simplifies beautifully to $y_{n+1} = \frac{q}{q-1} y_n$.
   By induction, $y_{k+m} (q-1)^m = y_k q^m$.
4. **The Divisibility Contradiction:** 
   Since $y_n \in \mathbb{N}$, this implies $(q-1)^m \mid y_k q^m$.
   Because $\gcd(q-1, q) = 1$, `Coprime.pow` allows you to deduce $(q-1)^m \mid y_k$.
   Because $y_k \ge 1$, we must have $(q-1)^m \le y_k$ for all $m$.
   However, for $q \ge 3$, we have $q - 1 \ge 2$, meaning $2^m \le y_k$ for all $m \in \mathbb{N}$. 
   This is an immediate contradiction for large $m$.
5. **Conclusion:** Thus, $\epsilon_k \neq -(q-2)$, strictly placing $\epsilon_k > -(q-2)$.

The above was created for the Diter' k q 1 case. The theorem however is about
Diter' k q n. In this case you just have to manage the $n = 0$ case separately in Phase 1.

* **The $n \ge 1$ case:** The identity $E(q, x) = q - 2 - ((x - 1) \bmod (q - 1))$ relies on $x \ge 1$. In Lean, natural number subtraction saturates at zero (i.e., `0 - 1 = 0`). If $x = 0$, the exact division lemma from Phase 1 breaks down. 
* **The $n = 0$ case is trivial:** If $D_0 = 0$, then `Dstep q 0 = (q * 0 + q - 2) / (q - 1)`. Since $q-2 < q-1$, integer division yields `0`. The sequence is just $0, 0, 0, \dots$. 
  * Therefore, $K = 0$.
  * The error $\epsilon_k = 0 - 0 \cdot \alpha^k = 0$.
  * For $q \ge 3$, the bounds are $-(q-2) < \epsilon_k \le 0$, which simplifies to $-(q-2) < 0 \le 0$. This is trivially true!

### Summary
To formalize it for an arbitrary $n$, you would start your Lean proof with:
```lean
rcases n with _ | n'
· -- Case n = 0: Trivial. Sequence is all 0s, K = 0, ε = 0.
· -- Case n = n' + 1 (i.e., n ≥ 1): Use the exact proof plan provided previously.
```
