# Proof Plan: Equivalence of `Aiter` halting and `Citer` parity sum

## Objective
Plan the proof for the equivalence between the halting condition of the `Aiter` sequence starting at `(8, 2)` and the parity sum condition on the `Citer` sequence starting at `8`. 

## Background & Motivation
The user wants to establish a link between the 2D sequence `Aiter i (8, 2)` and the 1D sequence `Citer i 8`. The original lemma statement proposed by the user was:
```lean
lemma Aiter_8_2_halt_iff_Citer_8_halt :
  (∃ i, (Aiter i (8, 2)).1 % 2 = 1 ∧ (Aiter i (8, 2)).1 / 2 ≥ 1 ∧ (Aiter i (8, 2)).2 = 0) ↔
  (∃ i, (Citer i 8) % 2 = 1 ∧ (Citer i 8) / 2 ≥ 1 ∧ i % 3 = 2 ∧
    (∑ j in Finset.range (i + 1), (Citer j 8) % 2) = 2 * (i + 1) / 3)
```
However, because the sequence starts at `b = 2` instead of `0`, and because the first component of `Aiter` evaluates to $c_{i+1} - 4$ rather than $c_i$, we need to adjust the indices and conditions on the right-hand side. 

## Key Observations
Let $a_i = (Aiter~i~(8,2))_1$, $b_i = (Aiter~i~(8,2))_2$, and $c_i = Citer~i~8$.
1.  **First Component Offset:** By tracing the maps, we find $a_i = c_{i+1} - 4$ for all $i \ge 0$.
Make a helper lemma for this.
    *   This implies $a_i \bmod 2 = c_{i+1} \bmod 2$.
    *   It also means $a_i / 2 \ge 1 \iff a_i \ge 2 \iff c_{i+1} \ge 6$.
2.  **Second Component (The Tape `b`):** 
    *   The transition for $b$ is $+2$ if $a$ is even, and $-1$ if $a$ is odd.
    *   Since $b_0 = 2$, we can model $b_i$ before it reaches 0 as:
        $b_i = 2 + 2i - 3 \sum_{j=0}^{i-1} (a_j \bmod 2)$.
    *   Substituting $a_j \equiv c_{j+1} \pmod 2$, and noting $c_0 = 8 \equiv 0 \pmod 2$, the sum of odd terms is exactly $Psum(i) = \sum_{j=0}^i (c_j \bmod 2)$.
    *   Thus, the idealized integer value of $b_i$ is $b\_int(i) = 2 + 2i - 3 \cdot Psum(i)$.
    *   The halting condition $b_i = 0$ implies $3 \cdot Psum(i) = 2(i+1)$, meaning $Psum(i) = 2(i+1)/3$ and necessarily $i \equiv 2 \pmod 3$.
3.  **Truncation:** Since $b$ is a natural number, $0 - 1 = 0$. However, because $b_i$ starts at $2$ and takes steps of $+2$ or $-1$, it cannot drop below $0$ without hitting $0$ first. Therefore, at the *first* index $i$ where $b_i = 0$, no truncation has occurred, and $b_i = b\_int(i)$ exactly.

## Proposed Modified Lemma
We will update the lemma in `AntihydraBasics/Basics.lean` to reflect the exact $c_{i+1}$ shift:

```lean
lemma Aiter_8_2_halt_iff_Citer_8_halt :
  (∃ i, (Aiter i (8, 2)).1 % 2 = 1 ∧ (Aiter i (8, 2)).1 / 2 ≥ 1 ∧ (Aiter i (8, 2)).2 = 0) ↔
  (∃ i, (Citer (i + 1) 8) % 2 = 1 ∧ (Citer (i + 1) 8) ≥ 6 ∧ i % 3 = 2 ∧
    (∑ j in Finset.range (i + 1), (Citer j 8) % 2) = 2 * (i + 1) / 3)
```

## Implementation Plan

### Step 1: Prove Properties of the First Component
*   **`lemma Citer_ge_8 (i : ℕ)`:** Prove `Citer i 8 ≥ 8` by induction.
*   **`lemma A_fst_eq_C_sub_four {c : ℕ} (h : c ≥ 4)`:** Prove `(A (c - 4, b)).1 = C c - 4`.
*   **`lemma Aiter_fst_eq_Citer_succ_sub_four (i : ℕ)`:** Prove `(Aiter i (8, 2)).1 = Citer (i + 1) 8 - 4` by induction using the above lemmas.
*   Establish equivalence lemmas for parity and size:
    *   `a_i % 2 = 1 ↔ c_{i+1} % 2 = 1`
    *   `a_i / 2 ≥ 1 ↔ c_{i+1} ≥ 6`

### Step 2: Model the Second Component in `ℤ`
*   Define `b_int (i : ℕ) : ℤ := 2 + 2 * (i : ℤ) - 3 * (∑ j in Finset.range (i + 1), ((Citer j 8) % 2 : ℤ))`
*   **`lemma b_int_step (i : ℕ)`:** Show `b_int (i + 1) = b_int i + if Citer (i + 1) 8 % 2 = 0 then 2 else -1`.
*   **`lemma Aiter_snd_eq_b_int (i : ℕ)`:** Prove that if $\forall j < i, (Aiter~j~(8,2))_2 > 0$, then $((Aiter~i~(8,2))_2 : \mathbb{Z}) = b\_int(i)$. This confirms the formula holds until the first time it reaches 0.

### Step 3: Prove the Forward Implication ($\rightarrow$)
*   Assume the LHS. Let $i$ be the smallest natural number where it halts (using `Nat.find`).
*   Because $i$ is minimal, $b_j > 0$ for all $j < i$.
*   Apply `Aiter_snd_eq_b_int` to show $b\_int(i) = 0$.
*   Rearrange $b\_int(i) = 0$ to deduce the parity sum formula and $i \equiv 2 \pmod 3$.
*   Use the first component lemmas to map the $a_i$ conditions to $c_{i+1}$.

### Step 4: Prove the Backward Implication ($\leftarrow$)
*   Assume the RHS. Let $i$ be the smallest natural number satisfying the RHS sum condition.
*   For all $j < i$, the sum condition is not met, which structurally forces $b\_int(j) > 0$.
*   Thus no truncation occurs up to step $i$.
*   Therefore $b_i = b\_int(i) = 0$, satisfying the halting requirement.
*   Again use the first component lemmas to map $c_{i+1}$ conditions back to $a_i$.

## Verification
*   The updated lemma correctly reflects the sequence behavior.
*   The proof will be verified via Lean 4 compilation ensuring no `sorry` remains.
