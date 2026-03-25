
Here is a detailed, step-by-step mathematical plan to prove your conditional theorem `conditional_irrationality_of_K3`. 

This plan leverages the equidistribution hypothesis to bypass the "chaos" of the sequence, transforming an intractable Collatz-like problem into a rigorous proof by contradiction involving bounded dynamical systems.

### Phase 1: Setup and the Rationality Assumption
1. **Assume the Contradiction:** Assume $K(3)$ is rational. Let $K(3) = \frac{a}{b}$ for positive integers $a, b$.
2. **Define the Error Term:** Let $E_n = \frac{a}{b} \left(\frac{3}{2}\right)^n - x_n$, where $x_n$ is the sequence `odlyzkoWilfSeq n`. 
3. **Bound the Error:** By the definition of the Odlyzko-Wilf constant, $x_n$ strictly tracks the exponential growth, and it is a known property of this sequence that $E_n$ is bounded: $E_n \in[0, 1)$. 
4. **Establish the Exact Recurrence:** From the definition $x_{n+1} = \lceil \frac{3}{2} x_n \rceil$, we know $x_{n+1} = \frac{3}{2}x_n + \frac{\delta_n}{2}$, where $\delta_n \in \{0, 1\}$ is the parity of $x_n$. Substituting $x_n = \frac{a}{b}(3/2)^n - E_n$ into this relation simplifies beautifully to the exact algebraic constraint:
   $$3 E_n = \delta_n + 2 E_{n+1}$$

### Phase 2: Connecting the Error to Fractional Parts
1. **Scale by the Denominator:** Multiply the error term equation by $b$ to get $b E_n = a \left(\frac{3}{2}\right)^n - b x_n$.
2. **Isolate the Fractional Part:** Because $b x_n$ is strictly an integer, taking the fractional part of both sides yields:
   $$\{ b E_n \} = \left\{ a \left(\frac{3}{2}\right)^n \right\}$$
3. **Define the Bounded State Sequence:** Since $E_n \in[0, 1)$, we know $b E_n \in[0, b)$. We can split $b E_n$ into its integer and fractional parts:
   $$b E_n = k_n + y_n$$
   Where $k_n = \lfloor b E_n \rfloor \in \{0, 1, \dots, b-1\}$ is a strictly bounded integer sequence, and $y_n = \{ a (3/2)^n \}$ is the fractional part.

### Phase 3: Applying the Equidistribution Hypothesis
1. **Invoke the Lean 4 Premise:** Your theorem provides the hypothesis `heq : IsEquidistributedModuloOne (fun n => (3 / 2)^n)`. 
2. **Apply Weyl’s Criterion:** A standard theorem in uniform distribution states that if a sequence $u_n$ is equidistributed modulo 1, then for any non-zero integer $a$, the scaled sequence $a \cdot u_n$ is also equidistributed modulo 1. 
3. **Conclude Equidistribution of $y_n$:** Therefore, the sequence $y_n = \left\{ a \left(\frac{3}{2}\right)^n \right\}$ must be equidistributed (and thus uniformly dense) in the interval $[0, 1)$.

### Phase 4: Constructing the Automaton Contradiction
1. **Substitute into the Recurrence:** Plug $b E_n = k_n + y_n$ back into our Phase 1 recurrence ($3 b E_n = b \delta_n + 2 b E_{n+1}$):
   $$3(k_n + y_n) = b \delta_n + 2(k_{n+1} + y_{n+1})$$
2. **Rearrange to Isolate Integers:**
   $$2 k_{n+1} - 3 k_n = 3 y_n - 2 y_{n+1} - b \delta_n$$
3. **Define the "Carry" Term:** Let $c_n = 3 y_n - 2 y_{n+1}$. Because the left side of the equation is an integer, and $b \delta_n$ is an integer, $c_n$ **must** be an integer. Since $y_n, y_{n+1} \in
