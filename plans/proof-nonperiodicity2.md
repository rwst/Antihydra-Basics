
### The Elementary Proof of Non-Periodicity
You can actually prove that the sequence cannot be eventually periodic using a beautiful and relatively elementary argument by contradiction. 

Let $w_n = D(n) \pmod 2 \in \{0, 1\}$.
By definition, if $D(n)$ is even, $D(n+1) = \frac{3}{2}D(n)$. If $D(n)$ is odd, $D(n+1) = \frac{3D(n)+1}{2}$. We can unify these cases into a single exact algebraic formula:
$$D(n+1) = \frac{3D(n) + w_n}{2}$$

Rearranging this gives $w_n = 2D(n+1) - 3D(n)$. 

If we divide both sides by $2(3/2)^{n+1} = 3(3/2)^n$, we get a telescoping difference:
$$\frac{D(n+1)}{(3/2)^{n+1}} - \frac{D(n)}{(3/2)^n} = \frac{w_n}{3(3/2)^n}$$

Summing this equation from $n = N$ to infinity yields:
$$\lim_{m \to \infty} \frac{D(m)}{(3/2)^m} - \frac{D(N)}{(3/2)^N} = \sum_{m=0}^\infty \frac{w_{N+m}}{3 (3/2)^m}$$

Because $D(n)$ grows asymptotically like $K(3/2)^n$ (a result proven by Odlyzko and Wilf), the limit on the left converges to a fixed positive constant $K \approx 1.62227$. Let the sum on the right be denoted as $E_N$. Rearranging terms gives:
$$K \left(\frac{3}{2}\right)^N = D(N) + E_N$$

Now, **assume for the sake of contradiction that $w_n$ is eventually periodic** with some period $P$. 
1. If $w_n$ is eventually periodic, then for large $N$, the tail sum $E_N = \sum_{m=0}^\infty w_{N+m} \frac{1}{3(3/2)^m}$ evaluates the sum of a repeating geometric series. 
2. Therefore, $E_N$ must be a **rational number** that only takes on a finite set of values depending on where $N$ falls in the period. Let $Q$ be the least common multiple of the denominators of these finite rational values. This guarantees that $Q \cdot E_N$ is always an integer.
3. Returning to our equation, $K = (D(N) + E_N)(2/3)^N$. Because $D(N)$ is an integer and $E_N$ is rational, $K$ itself must be exactly equal to some rational number $a/b$.
4. Substitute $K = a/b$ back into the equation and multiply everything by $b \cdot Q$:
$$a \cdot Q \frac{3^N}{2^N} = b \cdot Q \cdot D(N) + b \cdot Q \cdot E_N$$
5. Notice the right-hand side is strictly an integer (since $D(N)$ is an integer and $Q \cdot E_N$ is an integer).
6. This implies the left-hand side, $\frac{a \cdot Q \cdot 3^N}{2^N}$, **must be an integer for all large $N$**.

**The Contradiction:** 
$a \cdot Q$ is a fixed, finite integer. For $N$ sufficiently large, $2^N$ will eventually grow much larger than $a \cdot Q$. Because $2^N$ and $3^N$ are coprime, the denominator $2^N$ cannot be cancelled out, meaning the fraction $\frac{a \cdot Q \cdot 3^N}{2^N}$ cannot possibly evaluate to an integer for all arbitrarily large $N$.

This contradiction proves that our initial assumption was false: the parity sequence $w_n = D(n) \pmod 2$ **cannot be eventually periodic**.
