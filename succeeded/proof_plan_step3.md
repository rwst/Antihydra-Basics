# Formal Proof Plan for the Antihydra Program Equivalence

This document outlines the detailed plan to prove the connection methodology (`Step 3` lemmas: `tm_simulates_math` and `tm_halt_iff_math_condition`). 

We use the bbchallenge proof description for $A(a,b)$ (which corresponds to $E(b,a)$ in our definition) to map out exactly how we can formally prove these lemmas in Lean 4 without getting stuck in arithmetic tarpits.

## The Shortcut: Structural Induction over $k$

The reference proof relies heavily on reasoning about $\lfloor a/2 \rfloor - 1$ steps and modulo arithmetic. Native division and modulo operations in Lean can require tedious bounding proofs.

Instead, we use **Structural Induction** by recognizing that since $a / 2 \ge 1$ (from our mathematical halting condition), $a \ge 2$. Any such $a$ can be uniquely written as:
- $a = 2k + 2$ (if $a$ is even)
- $a = 2k + 3$ (if $a$ is odd)

This means we can isolate the reduction step $A \to A$ (or $E \to E$) into a macro sequence $P(m,n)$ and prove its effect by induction on $k$, perfectly avoiding all fractional arithmetic.

---

## 1. Define Helper Constructors and Tape Segments

First, we need robust ways to talk about repeating blocks of 1s without counting manually.
- Define `repeatOne (k : Nat) : List TapeSymbol := replicate k true`
- Prove simple properties about `repeatOne` interacting with `tailD'`, `headD'`, and `++`.

## 2. Define the Parametrized Configuration $P(m, n)$

From the paper, we define $P(m, n) := 0^\infty 1^b 0 1^m E> 0 1^n 0^\infty$. 
In our `Config` zipper tape, this corresponds to:
```lean
def P_Config (b : Nat) (m : Nat) (n : Nat) : Config :=
  { state := some ⟨4, ...⟩, -- State E
    head := false,
    left := repeatOne m ++ [false] ++ repeatOne b ++ ... -- left tape is reversed!
    right := repeatOne n ++ [false] ++ ...
  }
```
**Key observation from the trace**: The transition $P(m, n) \to P(m-2, n+3)$ completely preserves the tape to the left of the `0` between $1^m$ and $1^b$. The head never crosses that `0` during the main reduction loop!

## 3. Prove Micro-Shift Lemmas

Turing machines spend most of their time moving across blocks of identical symbols. We need lemmas that fast-forward these phases.
- **A-Shift**: Prove `A> 1^k \to 1^k A>`. (In Lean: running state A to the right over `repeatOne k` takes $k$ steps and leaves the tape unchanged).
- **C-Shift**: Prove `<C 1^k \to 1^k <C`. (State C moving left over `repeatOne k`).

These lemmas will drastically reduce the proof length by turning $O(N)$ TM steps into $O(1)$ Lean rewrites.

## 4. Prove the Reduction Step Lemma

Prove the core transition shown in the BBchallenge analysis:
`theorem tm_P_step (b m n : Nat) : run (P_Config b (m+2) n) (2*n + 12) = P_Config b m (n+3)`

*Proof strategy:* This is proven by manually unfolding `run` for the edge cases (A on 0, B on 0, etc.) and rewriting with the `A-Shift` and `C-Shift` lemmas for the $1^x$ blocks.

## 5. Prove the Multi-Step Lemma (The Loop)

This is where the shortcut shines. We define the multi-step reduction by induction on $k$ (the number of loops).
`theorem tm_P_multistep (b m n k : Nat) : ∃ steps, run (P_Config b (m + 2*k) n) steps = P_Config b m (n + 3*k)`

*Proof strategy:* Standard `Nat` induction on $k$. The zero case is `rfl`. The successor case applies `tm_P_step` and uses the induction hypothesis. This completely bypasses $\lfloor a/2 \rfloor$!

## 6. Prove the Endgames

The loop finishes when $m$ is reduced to either $2$ or $3$. The head finally crosses the `0` into the $1^b$ block and resets to State E. We prove these final phases as isolated lemmas:

- **Even Endgame (`m = 2`):**
  `theorem tm_even_endgame (b N : Nat) : ∃ steps, run (P_Config b 2 N) steps = P_Config (b + 2) (N + 2) 0`
  *(Note that $N$ will be $3k$, so the next $a$ is $3k+2$, which exactly matches the math model $E(2k+2, b) \to E(3k+2, b+2)$)*

- **Odd Endgame (`m = 3`):**
  `theorem tm_odd_endgame (b N : Nat) :`
  `- if b = 0, machine halts (reaches F0)`
  `- if b > 0, ∃ steps, run (P_Config b 3 N) steps = P_Config (b - 1) (N + 6) 0`
  *(Note that $N$ will be $3k$, so the next $a$ is $3k+6$, which exactly matches the math model $E(2k+3, b) \to E(3k+6, b-1)$)*

## 7. Tie it all together in `tm_simulates_math`

With the loop and endgames solved, the core `tm_simulates_math` theorem becomes a clean case analysis:

1. Assume `isValidLoopStart c`. This implies `c = P_Config b a 0` for some $a, b$.
2. The math halting condition dictates $a/2 \ge 1$. Thus $a \ge 2$.
3. We branch on whether $a$ is even or odd:
   - **If even**: write $a = 2k + 2$. 
     Apply `tm_P_multistep` to jump to `P_Config b 2 (3k)`.
     Apply `tm_even_endgame` to arrive at `P_Config (b+2) (3k+2) 0`.
     Show this matches `nextMathState (a, b) = some (3k+2, b+2)`.
   - **If odd**: write $a = 2k + 3$.
     Apply `tm_P_multistep` to jump to `P_Config b 3 (3k)`.
     Apply `tm_odd_endgame` and branch on $b$.
     If $b > 0$, show the state becomes `P_Config (b-1) (3k+6) 0`, which matches `some (3k+6, b-1)`.
     If $b = 0$, show the TM hits the `none` (HALT) state.

This completes the proof of `tm_simulates_math` entirely algebraically without ever calculating divisions by 2 inside the TM proofs.

## 8. Prove Halting Equivalence

With `tm_simulates_math` established as a perfect one-step bisimulation of `nextMathState`, the `tm_halt_iff_math_condition` theorem is proved by a standard structural induction over the `mathHalts` relation.
