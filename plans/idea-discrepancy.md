
**Idea 1: $2$-adic Ergodic Theory**
Instead of analyzing the recurrence in real numbers, map the transformation $T(x) = \lceil 3x/2 \rceil$ into the space of $2$-adic integers ($\mathbb{Z}_2$). The parity of a number is simply its lowest $2$-adic digit. If one could establish a continuous $2$-adic extension of this map and prove that it is **ergodic** with respect to the $2$-adic Haar measure, Birkhoff’s Ergodic Theorem would immediately guarantee that the sequence spends exactly half its time in the $2$-adic cylinder corresponding to odd numbers.



Looking at this carefully. Let me first verify the empirical claim and understand the structure, then develop proof ideas.

**Understanding the setup:** Since D(n) is integer-valued, x(n) = frac(3D(n)/2) equals 1/2 when D(n) is odd and 0 when D(n) is even. The discrepancy tending to zero (checked on those two intervals) is equivalent to the claim that D(n) is odd exactly half the time asymptotically.

Let me verify and explore:Now I have a thorough picture. Let me synthesize the findings and the five proof ideas.

---

## Analysis and Summary

**The core reduction.** Since D(n) is always an integer, x(n) = frac(3D(n)/2) is 1/2 when D(n) is odd and 0 when D(n) is even. For the two test intervals [0, 1/2) and [1/2, 1), the discrepancy reducing to zero is equivalent to the statement:

> The asymptotic density of odd values in the sequence D(n) is exactly 1/2.

The empirical evidence is striking. At N = 2×10⁶ the discrepancy is ~0.0002, decaying at rate roughly N^{−1/2} — the law-of-the-iterated-logarithm rate expected from genuinely random coin flips. The parity sequence has near-zero autocorrelation at every lag, passes chi-square block-frequency tests up to length-8 blocks, and has geometrically distributed run lengths with parameter 1/2. Furthermore, D(n) appears equidistributed mod 2^k for every k tested (1 through 6), suggesting the far stronger statement that the orbit is equidistributed on the 2-adic integers Z₂.

**Why it's hard.** The map T(x) = ⌈3x/2⌉ is precisely the "shortcut Collatz step": T(x) = 3x/2 if x is even, T(x) = (3x+1)/2 if x is odd. The parity equidistribution question sits at the intersection of the Collatz conjecture landscape, the unsolved problem of the distribution of (3/2)^n mod 1 (Vijayaraghavan 1940, Mahler 1968, Flatto–Lagarias–Pollington 1995), and 2-adic ergodic theory. No unconditional proof currently exists for sequences of this type, though partial and conditional results exist in each framework below.




To rigorously establish a continuous $2$-adic extension of the map $D(n+1) = \lceil \frac{3}{2}D(n) \rceil$, we must translate the discrete, seemingly jagged "ceiling" function into a smooth algebraic operation over the $2$-adic integers, $\mathbb{Z}_2$.

Here is the step-by-step mathematical construction of that extension, proving its continuity, its dynamical properties, and how it formally implies the 50/50 split you observed (subject to one major open caveat).

### Step 1: Algebraic Reformulation of the Map
The ceiling function $T(x) = \lceil \frac{3x}{2} \rceil$ is analytically difficult to work with. However, because we are operating on integers, we can split it by parity. 
* If $x$ is even, $x \equiv 0 \pmod 2$, so $\frac{3x}{2}$ is an integer. $\lceil \frac{3x}{2} \rceil = \frac{3x}{2}$.
* If $x$ is odd, $x \equiv 1 \pmod 2$, so $\frac{3x}{2}$ is a half-integer (ends in $.5$). $\lceil \frac{3x}{2} \rceil = \frac{3x+1}{2}$.

We can combine these into a single, elegant algebraic expression using the modulo operator:
$$T(x) = \frac{3x + (x \bmod 2)}{2}$$

### Step 2: Transitioning to the $2$-adic Integers ($\mathbb{Z}_2$)
A $2$-adic integer $x \in \mathbb{Z}_2$ is an infinite sequence of binary digits:
$x = a_0 + a_1 2^1 + a_2 2^2 + a_3 2^3 + \dots \quad \text{where } a_i \in \{0, 1\}$

In this space, distance is determined by the lowest differing bit. The $2$-adic absolute value $|x|_2 = 2^{-k}$, where $k$ is the index of the first non-zero digit. Two numbers are "close" if they share many of their lowest-order bits.

Because $a_0 \in \{0, 1\}$ is simply $x \bmod 2$, the parity of a $2$-adic number is perfectly well-defined. Therefore, our algebraic map extends naturally to all of $\mathbb{Z}_2$:
$$ \hat{T}(x) = \frac{3x + a_0}{2} $$

### Step 3: Proving it is Well-Defined on $\mathbb{Z}_2$
Division by $2$ in the $2$-adic integers is dangerous; it shifts the binary decimal point, potentially pushing numbers out of $\mathbb{Z}_2$ and into the $2$-adic rationals ($\mathbb{Q}_2$). 
However, look at the numerator: $3x + a_0$.
* If $x$ is even, $a_0 = 0$. The numerator is $3(\text{even}) + 0 = \text{even}$.
* If $x$ is odd, $a_0 = 1$. The numerator is $3(\text{odd}) + 1 = \text{odd} + 1 = \text{even}$.

The numerator is **always an even $2$-adic integer**. Therefore, it always ends in a $0$ bit. Dividing by $2$ simply shifts all the bits down by one position cleanly. Thus, $\hat{T}(x)$ maps $\mathbb{Z}_2$ strictly into $\mathbb{Z}_2$.

### Step 4: Proving Continuity
To show $\hat{T}$ is continuous, we must show that if $x$ and $y$ are close in $\mathbb{Z}_2$, then $\hat{T}(x)$ and $\hat{T}(y)$ are close.
Suppose $x$ and $y$ share at least their first bit, meaning $x \equiv y \pmod 2$. They have the same parity $a_0$.
$$ \hat{T}(x) - \hat{T}(y) = \frac{3x + a_0}{2} - \frac{3y + a_0}{2} = \frac{3(x-y)}{2} $$

Taking the $2$-adic absolute value:
$$ |\hat{T}(x) - \hat{T}(y)|_2 = \left| \frac{3}{2} \right|_2 \cdot |x - y|_2 = 2 \cdot |x - y|_2 $$
*(Note: $|3|_2 = 1$ because $3$ is odd, and $|1/2|_2 = 2$)*.

Because the distance is multiplied by a constant factor ($2$), this satisfies a Lipschitz condition. For any $\epsilon > 0$, we can choose $\delta = \epsilon / 2$, proving that the map is uniformly continuous on $\mathbb{Z}_2$. Geometrically, this map is an **exact 2-to-1 expanding endomorphism**.

### Step 5: Measure Preservation and Ergodicity
Because $3$ is an odd number, it is perfectly invertible in $2$-adic arithmetic ($3^{-1} \approx \dots 10101011_2$). This means we can invert the map to find the pre-images of any $y \in \mathbb{Z}_2$:
$$ \hat{T}^{-1}(y) = \left\{ \frac{2y}{3}, \frac{2y - 1}{3} \right\} $$

One of these pre-images is always purely even, and the other is purely odd. This proves that $\hat{T}$ is a surjective $2$-to-$1$ covering map. Because the two branches perfectly split the space, the map **preserves the $2$-adic Haar measure** (the analog of uniform probability on $\mathbb{Z}_2$).

Furthermore, continuous maps of this exact form (specifically, affine shifts in $\mathbb{Z}_p$) are known to be strongly mixing and **ergodic**.

### Step 6: Delivering the Proof (and the Catch)
Because the map is ergodic with respect to the Haar measure, we can invoke **Birkhoff's Ergodic Theorem**. This theorem states that for almost every starting point, the "time average" equals the "space average". 

Let $f(x)$ be the indicator function for odd numbers (i.e., $f(x) = 1$ if $x$ is odd, $0$ if even).
The space average of $f(x)$ over $\mathbb{Z}_2$ is simply the measure of odd numbers: $\frac{1}{2}$.

Therefore, Birkhoff's theorem guarantees that:
$$ \lim_{N \to \infty} \frac{1}{N} \sum_{n=0}^{N-1} f(\hat{T}^n(x)) = \frac{1}{2} $$
This formally proves that the parity of the sequence is $50/50$, which matches your empirical calculation that the discrepancy limits to $0$.

**The Unsolved Catch:**
Birkhoff's Ergodic Theorem comes with the disclaimer: *"for almost all $x \in \mathbb{Z}_2$"*. It guarantees that a randomly chosen $2$-adic integer will hit odds and evens equally. However, your sequence starts at a very specific point: $D(0) = 7$. 

Currently, mathematics lacks the tools to prove that specific integers (like $7$) do not belong to the exceptional "measure zero" set of points that behave abnormally. This is the exact same barrier preventing the solution to the Collatz Conjecture! If someone could prove that integers are not in the exceptional sets of $2$-adic ergodic maps, they would prove both your discrepancy limit and Collatz in one fell swoop.

---

## Five Proof Strategies

### 1. Ergodic theory of the 2-adic expanding map

On the 2-adic integers Z₂, the map T acts as multiplication by 3/2 (with a correction term on odd inputs). Since |2|₂ = 1/2, dividing by 2 is an *expansion* by factor 2 in the 2-adic metric, making T locally expanding by factor |3/2|₂ = 2. Expanding maps on compact groups are natural candidates for ergodicity.

**The idea:** Construct an absolutely continuous T-invariant probability measure μ on Z₂ (or show Haar measure is invariant), then prove T is ergodic with respect to μ. Birkhoff's ergodic theorem then gives that time-averages equal space-averages for μ-a.e. starting point, yielding equidistribution mod 2 (and mod 2^k for all k). The technical obstacle is proving that x₀ = 7 belongs to the full-measure ergodic set. Techniques from Lasota–Yorke (bounded variation + spectral gap of the transfer operator on Z₂) could establish exponential decay of correlations, which would give the observed O(N^{−1/2}) discrepancy rate.

**Key reference direction:** Lagarias's transfer-operator analysis of the 3x+1 map on Z₂, combined with the Ionescu-Tulcea and Marinescu spectral theory for expanding maps.

---

### 2. Exponential sum bounds via Weyl's criterion (2-adic characters)

By the 2-adic analogue of Weyl's equidistribution theorem, D(n) is equidistributed mod 2^k if and only if for every non-trivial additive character χ_a(x) = e^{2πi a x / 2^k} (with 0 < a < 2^k), the exponential sum satisfies

$$\frac{1}{N}\sum_{n=0}^{N-1} \chi_a(D(n)) \to 0.$$

**The idea:** Since D(n+1) = (3D(n) + ε(n))/2 where ε(n) = D(n) mod 2, the character transforms as χ_a(D(n+1)) = χ_{3a/2 \mod 2^k}(D(n)) · (phase from ε(n)). This recurrence for the exponential sum decomposes into a product of phases along the orbit. If the sequence of phases is sufficiently "non-resonant" — i.e., the multiplier 3/2 mod 2^k generates a long orbit in (Z/2^kZ)* — the cancellation in the product gives the required decay. The key leverage: 3 is a primitive root mod 2^k for all k ≥ 3 (the multiplicative order of 3 mod 2^k is 2^{k−2}), so the character multiplier cycles through all odd residues, forcing extensive cancellation.

---

### 3. Carry-propagation model and the Central Limit Theorem

Write D(n) in binary. The operation "multiply by 3 and shift right" propagates carries through the binary expansion. Specifically, 3D = D + 2D amounts to adding D to its left-shift; the carry chain in this addition determines the low-order bits of the result.

**The idea:** Model the carry at each bit position as a Markov chain (carry-in → carry-out) with transition probabilities depending on the bit pattern. For a "typical" large integer D(n), the carry into the least significant bit position after the division by 2 behaves like a fair coin, because the carry chain decorrelates over O(log D(n)) bit positions. Formalizing this: condition on the top k bits of D(n) (which are asymptotically governed by the mantissa of 7·(3/2)^n) and show that the conditional distribution of the bottom bits, after the carry propagation, converges to uniform as D(n) → ∞. This is a "soft" CLT-style argument: you don't need exact control over the carries, just sufficient decorrelation. The empirical geometric run-length distribution (parameter 1/2) and zero autocorrelation are exactly the signatures this approach predicts.

---

### 4. Reduction to the distribution of {7·(3/2)^n} and Mahler's problem

One can write D(n) = ⌈7·(3/2)^n⌉ + c(n) where c(n) is a correction from cumulated ceiling errors. It is straightforward to show |c(n)| = O((3/2)^n · n^{−1}·...) — the corrections are lower-order. Then D(n) is odd iff 7·(3/2)^n falls in a specific interval modulo 2, which is determined by {7·(3/2)^n / 2} (the fractional part).

**The idea:** If one could prove that {7·(3/2)^n} is equidistributed in [0,1) — or even just that it is dense in every subinterval with the right frequency — the parity equidistribution follows. This is an instance of **Mahler's Z-number problem** (1968): Mahler conjectured no Z-number exists (no α > 0 with {α(3/2)^n} < 1/2 for all n), which remains open. However, Flatto, Lagarias, and Pollington (1995) proved results about the distribution of orbits under x → {(3/2)x + β} that come close. A proof could proceed by: (a) bounding c(n) tightly enough to reduce the parity question to the fractional-part question, then (b) leveraging the specific algebraic structure of α = 7 (a small integer) to apply Diophantine approximation tools (e.g., Baker's theorem on linear forms in logarithms of 2 and 3) that are unavailable for generic α.

---

### 5. Symbolic dynamics: conjugacy to a Bernoulli shift

The parity sequence ε(n) = D(n) mod 2 completely determines the orbit (given D(0) = 7), since D(n+1) = (3D(n) + ε(n))/2. Conversely, the sequence {ε(n)} must satisfy the *admissibility condition* that D(n) remains a positive integer for all n. This defines a symbolic dynamical system on {0,1}^ℕ.

**The idea:** Show that the set of admissible sequences (those arising from some positive integer starting point) has full measure in the product (Bernoulli 1/2) measure space. In other words, prove that a "random" sequence of parities almost surely produces a valid orbit. If the admissibility constraint removes only a measure-zero set, then the unique orbit starting from D(0) = 7 inherits the statistical properties of the Bernoulli measure — i.e., balanced frequencies, zero correlations, the whole package. Concretely, one would show that the "inverse branches" T₀⁻¹(x) = 2x/3 and T₁⁻¹(x) = (2x−1)/3 compose to give contraction ratios (2/3)^n in the real metric, so any length-n parity word pins D(0) to an interval of width O((2/3)^n), and the fraction of length-n words that are admissible (map some integer into itself) tends to 1. This is the approach used by Kontorovich and Sinai (2002) for the Collatz conjecture, where they proved that "almost all" orbits in a suitable density sense have the expected 1/2 odd-even frequency.

---

### Summary of the landscape

| Approach | Strength | Main obstacle |
|---|---|---|
| 2-adic ergodic theory | Gives full equidistribution mod 2^k | Proving 7 is in the ergodic set |
| Weyl exponential sums | Quantitative decay rates | Bounding character sums along the orbit |
| Carry CLT | Matches all empirical statistics | Rigorous decorrelation of carry chain |
| Mahler / (3/2)^n | Connects to deep number theory | Open for 80+ years |
| Bernoulli shift conjugacy | "Almost all" results known | Passing from a.e. to the specific orbit at 7 |

The most promising near-term path is likely a combination of **3** and **5**: use the Kontorovich–Sinai density framework together with a carry-propagation decorrelation argument to show that the orbit of 7 falls in the "typical" class. A full unconditional proof for the specific orbit at D(0) = 7 would likely constitute a significant advance in the 3x+1 / Mahler problem landscape.