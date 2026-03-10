import Mathlib

-- 1. Finitary Types for optimal pattern matching
abbrev TapeSymbol := Bool -- false = 0 (blank), true = 1
abbrev State  := Fin 6 -- The 6 non-halt states of your BB(6)

inductive Dir where | L | R
deriving DecidableEq, Repr

-- 2. The Transition Table (deterministic function)
-- Returns: (Next State (none = HALT), Write Symbol, Move Direction)
def transition (q : State) (s : TapeSymbol) : Option State × TapeSymbol × Dir :=
  match q.val, s with
  -- A
  | 0, false => (some ⟨1, by decide⟩, true, Dir.R)
  | 0, true  => (some ⟨0, by decide⟩, true, Dir.R)
  -- B
  | 1, false => (some ⟨2, by decide⟩, false, Dir.L)
  | 1, true  => (some ⟨4, by decide⟩, true, Dir.L)
  -- C
  | 2, false => (some ⟨3, by decide⟩, true, Dir.L)
  | 2, true  => (some ⟨2, by decide⟩, true, Dir.L)
  -- D
  | 3, false => (some ⟨0, by decide⟩, true, Dir.L)
  | 3, true  => (some ⟨1, by decide⟩, false, Dir.L)
  -- E
  | 4, false => (some ⟨5, by decide⟩, true, Dir.L)
  | 4, true  => (some ⟨4, by decide⟩, true, Dir.R)
  -- F
  | 5, false => (none, false, Dir.R)
  | 5, true  => (some ⟨0, by decide⟩, false, Dir.R)
  | _, _     => (none, false, Dir.R)

-- 3. The Configuration using a Zipper Tape
structure Config where
  state : Option State      -- none represents the HALT state
  left  : List TapeSymbol       -- Reversed: first element is immediately left of head
  head  : TapeSymbol
  right : List TapeSymbol       -- First element is immediately right of head
deriving Repr, Inhabited

def tailD' {α : Type} (l : List α) : List α :=
  match l with
  | [] => []
  | _ :: as => as

def headD' {α : Type} (l : List α) (default : α) : α :=
  match l with
  | [] => default
  | a :: _ => a

-- 4. The Deterministic Step Function
-- A zipper makes moving O(1) and trivially easy to prove by `simp`.
def step (c : Config) : Config :=
  match c.state with
  | none => c -- HALT state is a fixed point
  | some q =>
    let (q', w, d) := transition q c.head
    match d with
    | Dir.R => 
      let newRight := tailD' c.right
      let newHead := headD' c.right false
      { state := q', left := w :: c.left, head := newHead, right := newRight }
    | Dir.L => 
      let newLeft := tailD' c.left
      let newHead := headD' c.left false
      { state := q', left := newLeft, head := newHead, right := w :: c.right }

-- Run the machine for `n` steps
def run (c : Config) (n : Nat) : Config :=
  match n with
  | 0 => c
  | n' + 1 => run (step c) n'

-- 5. The Mathematical "High-Level" Model
structure MathState where
  a : Nat
  b : Nat
deriving Repr, Inhabited, DecidableEq

def nextMathState (m : MathState) : Option MathState :=
  let n := m.a / 2
  if n ≥ 1 then
    if m.a % 2 == 0 then
      some { a := 3 * n + 2, b := m.b + 2 }
    else
      if m.b == 0 then
        none
      else
        some { a := 3 * n + 3, b := m.b - 1 }
  else
    none

def mathHaltingCondition (m : MathState) : Prop :=
  m.a % 2 == 1 ∧ m.a / 2 ≥ 1 ∧ m.b == 0

-- 6. The "p-Proof" (Connection Methodology)

def countOnes : List TapeSymbol → Nat
  | [] => 0
  | true :: xs => countOnes xs + 1
  | false :: _ => 0

def repeatOne (k : Nat) : List TapeSymbol :=
  List.replicate k true

def repeatFalse (k : Nat) : List TapeSymbol :=
  List.replicate k false

@[simp] lemma repeatOne_succ (k : Nat) : repeatOne (k + 1) = true :: repeatOne k := rfl
@[simp] lemma repeatFalse_succ (k : Nat) : repeatFalse (k + 1) = false :: repeatFalse k := rfl


lemma run_add (c : Config) (n m : Nat) : run c (n + m) = run (run c n) m := by
  induction n generalizing c with
  | zero => rw [Nat.zero_add]; rfl
  | succ n ih =>
    calc
      run c (n + 1 + m) = run c (n + m + 1) := by congr 1; omega
      _ = run (step c) (n + m) := rfl
      _ = run (run (step c) n) m := ih (step c)
      _ = run (run c (n + 1)) m := rfl

def P_Config_Pad (b : Nat) (m : Nat) (n : Nat) (p : Nat) : Config :=
  { state := some ⟨4, by decide⟩,
    head := false,
    left := repeatOne m ++ [false] ++ repeatOne b,
    right := repeatOne n ++ repeatFalse p
  }

@[simp] lemma repeatOne_append_true (k : Nat) (L : List TapeSymbol) :
  repeatOne k ++ true :: L = repeatOne (k + 1) ++ L := by
  induction k with | zero => rfl | succ k ih => simp [repeatOne_succ, ih]

@[simp] lemma headD'_replicate_true (k : Nat) (R : List TapeSymbol) :
  headD' (repeatOne (k + 1) ++ R) false = true := rfl

@[simp] lemma tailD'_replicate_true (k : Nat) (R : List TapeSymbol) :
  tailD' (repeatOne (k + 1) ++ R) = repeatOne k ++ R := rfl

@[simp] lemma run_step_succ (c : Config) (n : Nat) :
  run c (n + 1) = run (step c) n := rfl

lemma A_shift (k : Nat) (L R : List TapeSymbol) :
  run { state := some ⟨0, by decide⟩, head := true, left := L, right := repeatOne k ++ R } (k + 1) =
  { state := some ⟨0, by decide⟩, head := headD' R false, left := repeatOne (k + 1) ++ L, right := tailD' R } := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    calc
      run { state := some ⟨0, by decide⟩, head := true, left := L, right := repeatOne (k + 1) ++ R } (k + 2)
      _ = run { state := some ⟨0, by decide⟩, head := true, left := true :: L, right := repeatOne k ++ R } (k + 1) := rfl
      _ = _ := by rw [ih (true :: L)]; simp

lemma C_shift (k : Nat) (L R : List TapeSymbol) :
  run { state := some ⟨2, by decide⟩, head := true, left := repeatOne k ++ L, right := R } (k + 1) =
  { state := some ⟨2, by decide⟩, head := headD' L false, left := tailD' L, right := repeatOne (k + 1) ++ R } := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    calc
      run { state := some ⟨2, by decide⟩, head := true, left := repeatOne (k + 1) ++ L, right := R } (k + 2)
      _ = run { state := some ⟨2, by decide⟩, head := true, left := repeatOne k ++ L, right := true :: R } (k + 1) := rfl
      _ = _ := by rw [ih (true :: R)]; simp

lemma E_shift (k : Nat) (L R : List TapeSymbol) :
  run { state := some ⟨4, by decide⟩, head := true, left := L, right := repeatOne k ++ R } (k + 1) =
  { state := some ⟨4, by decide⟩, head := headD' R false, left := repeatOne (k + 1) ++ L, right := tailD' R } := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    calc
      run { state := some ⟨4, by decide⟩, head := true, left := L, right := repeatOne (k + 1) ++ R } (k + 2)
      _ = run { state := some ⟨4, by decide⟩, head := true, left := true :: L, right := repeatOne k ++ R } (k + 1) := rfl
      _ = _ := by rw [ih (true :: L)]; simp

@[simp] lemma headD'_cons {α} (x : α) (xs : List α) (d : α) : headD' (x :: xs) d = x := rfl
@[simp] lemma tailD'_cons {α} (x : α) (xs : List α) : tailD' (x :: xs) = xs := rfl

@[simp] lemma headD'_repeatOne_false (m : Nat) (L : List TapeSymbol) : headD' (repeatOne m ++ false :: L) false = if m = 0 then false else true := by
  cases m with
  | zero => rfl
  | succ m => rfl

@[simp] lemma tailD'_repeatOne_false (m : Nat) (L : List TapeSymbol) : tailD' (repeatOne m ++ false :: L) = if m = 0 then L else repeatOne (m-1) ++ false :: L := by
  cases m with
  | zero => rfl
  | succ m => rfl

@[simp] lemma headD'_false_cons (R : List TapeSymbol) : headD' (false :: R) false = false := rfl
@[simp] lemma tailD'_false_cons (R : List TapeSymbol) : tailD' (false :: R) = R := rfl
@[simp] lemma headD'_nil (b : TapeSymbol) : headD' [] b = b := rfl
@[simp] lemma tailD'_nil : @tailD' TapeSymbol [] = [] := rfl

-- Macro Loop Steps

theorem tm_P_step (b m n p : Nat) : run (P_Config_Pad b (m+2+2) n (p+2)) (2*n + 12) = P_Config_Pad b (m+2) (n+3) (p+1) := by
  -- Step 1: E(m+2+2, n) -> state 5
  rw [show 2*n + 12 = 1 + (2*n + 11) by omega, run_add]
  have step1 : run (P_Config_Pad b (m+2+2) n (p+2)) 1 = 
    { state := some ⟨5, by decide⟩, head := true, left := repeatOne (m+2+1) ++ false :: repeatOne b, right := repeatOne (n+1) ++ repeatFalse (p+2) } := by
    simp [run, step, transition, P_Config_Pad]
  rw [step1]
  
  -- Step 2: state 5 -> A(m+2+1, n)
  rw [show 2*n + 11 = 1 + (2*n + 10) by omega, run_add]
  have step2 : run { state := some ⟨5, by decide⟩, head := true, left := repeatOne (m+2+1) ++ false :: repeatOne b, right := repeatOne (n+1) ++ repeatFalse (p+2) } 1 =
    { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne (m+2+1) ++ false :: repeatOne b, right := repeatOne n ++ repeatFalse (p+2) } := by
    simp [run, step, transition]
  rw [step2]

  -- Step 3: A_shift (n+1 steps)
  rw [show 2*n + 10 = (n+1) + (n+9) by omega, run_add]
  have step3 : run { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne (m+2+1) ++ false :: repeatOne b, right := repeatOne n ++ repeatFalse (p+2) } (n+1) =
    { state := some ⟨0, by decide⟩, head := false, left := repeatOne (n+1) ++ (false :: repeatOne (m+2+1) ++ false :: repeatOne b), right := repeatFalse (p+1) } := by
    have hA := A_shift n (false :: repeatOne (m+2+1) ++ false :: repeatOne b) (repeatFalse (p+2))
    have hp_head : headD' (repeatFalse (p+2)) false = false := rfl
    have hp_tail : tailD' (repeatFalse (p+2)) = repeatFalse (p+1) := rfl
    rw [hp_head, hp_tail] at hA
    exact hA
  rw [step3]

  -- Step 4: A0 -> B1
  rw [show n + 9 = 1 + (n + 8) by omega, run_add]
  have step4 : run { state := some ⟨0, by decide⟩, head := false, left := repeatOne (n+1) ++ (false :: repeatOne (m+2+1) ++ false :: repeatOne b), right := repeatFalse (p+1) } 1 =
    { state := some ⟨1, by decide⟩, head := false, left := true :: repeatOne (n+1) ++ (false :: repeatOne (m+2+1) ++ false :: repeatOne b), right := repeatFalse p } := by
    simp [run, step, transition]
  rw [step4]

  -- Step 5: B0 -> C1
  rw [show n + 8 = 1 + (n + 7) by omega, run_add]
  have step5 : run { state := some ⟨1, by decide⟩, head := false, left := true :: repeatOne (n+1) ++ (false :: repeatOne (m+2+1) ++ false :: repeatOne b), right := repeatFalse p } 1 =
    { state := some ⟨2, by decide⟩, head := true, left := repeatOne (n+1) ++ (false :: repeatOne (m+2+1) ++ false :: repeatOne b), right := false :: repeatFalse p } := by
    simp [run, step, transition]
  rw [step5]

  -- Step 6: C1 shift (n+2 steps)
  rw [show n + 7 = (n+2) + 5 by omega, run_add]
  have step6 : run { state := some ⟨2, by decide⟩, head := true, left := repeatOne (n+1) ++ (false :: repeatOne (m+2+1) ++ false :: repeatOne b), right := false :: repeatFalse p } (n+2) =
    { state := some ⟨2, by decide⟩, head := false, left := repeatOne (m+2+1) ++ false :: repeatOne b, right := repeatOne (n+2) ++ false :: repeatFalse p } := by
    have hC := C_shift (n+1) (false :: repeatOne (m+2+1) ++ false :: repeatOne b) (false :: repeatFalse p)
    have hC_head : headD' (false :: repeatOne (m+2+1) ++ false :: repeatOne b) false = false := rfl
    have hC_tail : tailD' (false :: repeatOne (m+2+1) ++ false :: repeatOne b) = repeatOne (m+2+1) ++ false :: repeatOne b := rfl
    rw [hC_head, hC_tail] at hC
    exact hC
  rw [step6]

  -- Step 7: C0 -> D1
  rw [show 5 = 1 + 4 by omega, run_add]
  have step7 : run { state := some ⟨2, by decide⟩, head := false, left := repeatOne (m+2+1) ++ false :: repeatOne b, right := repeatOne (n+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨3, by decide⟩, head := true, left := repeatOne (m+2) ++ false :: repeatOne b, right := true :: repeatOne (n+2) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  rw [step7]
  
  -- Step 8: D1 -> 1
  rw [show 4 = 1 + 3 by omega, run_add]
  have step8 : run { state := some ⟨3, by decide⟩, head := true, left := repeatOne (m+2) ++ false :: repeatOne b, right := true :: repeatOne (n+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨1, by decide⟩, head := headD' (repeatOne (m+2) ++ false :: repeatOne b) false, left := tailD' (repeatOne (m+2) ++ false :: repeatOne b), right := false :: true :: repeatOne (n+2) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  rw [step8]

  -- Step 9: 1 -> 4
  rw [show 3 = 1 + 2 by omega, run_add]
  have step9 : run { state := some ⟨1, by decide⟩, head := headD' (repeatOne (m+2) ++ false :: repeatOne b) false, left := tailD' (repeatOne (m+2) ++ false :: repeatOne b), right := false :: true :: repeatOne (n+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨4, by decide⟩, head := true, left := tailD' (tailD' (repeatOne (m+2) ++ false :: repeatOne b)), right := true :: false :: true :: repeatOne (n+2) ++ false :: repeatFalse p } := by
    -- m+2 >= 1, so head is true
    have h_head : headD' (repeatOne (m+2) ++ false :: repeatOne b) false = true := rfl
    rw [h_head]
    simp [run, step, transition]
  rw [step9]

  -- Step 10: 4 -> 4 (Right)
  rw [show 2 = 1 + 1 by omega, run_add]
  have step10 : run { state := some ⟨4, by decide⟩, head := true, left := tailD' (tailD' (repeatOne (m+2) ++ false :: repeatOne b)), right := true :: false :: true :: repeatOne (n+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨4, by decide⟩, head := true, left := true :: tailD' (tailD' (repeatOne (m+2) ++ false :: repeatOne b)), right := false :: true :: repeatOne (n+2) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  rw [step10]

  -- Step 11: 4 -> 4 (Right)
  rw [show 1 = 1 + 0 by omega, run_add]
  have step11 : run { state := some ⟨4, by decide⟩, head := true, left := true :: tailD' (tailD' (repeatOne (m+2) ++ false :: repeatOne b)), right := false :: true :: repeatOne (n+2) ++ false :: repeatFalse p } 1 =
    { state := some ⟨4, by decide⟩, head := false, left := true :: true :: tailD' (tailD' (repeatOne (m+2) ++ false :: repeatOne b)), right := true :: repeatOne (n+2) ++ false :: repeatFalse p } := by
    simp [run, step, transition]
  rw [step11]

  -- Final matching: P_Config_Pad b (m+2) (n+3) (p+1)
  change run _ 0 = _
  rw [run]
  simp [P_Config_Pad]





theorem tm_P_multistep (b m n p k : Nat) :
  run (P_Config_Pad b (m+2 + 2*k) n (p+1 + k)) (k*(2*n + 3*k + 9)) = P_Config_Pad b (m+2) (n+3*k) (p+1) := by
  induction k generalizing n with
  | zero =>
    have h0 : 0 * (2 * n + 3 * 0 + 9) = 0 := by ring
    rw [h0]
    have hm : m + 2 + 2 * 0 = m + 2 := by ring
    have hp : p + 1 + 0 = p + 1 := by ring
    have hn : n + 3 * 0 = n := by ring
    rw [hm, hp, hn]
    rfl
  | succ k' ih =>
    -- We want to do 1 step, then k' steps.
    -- Total steps = (2n + 12) + k' * (2(n+3) + 3k' + 9)
    have h_steps : (k' + 1) * (2 * n + 3 * (k' + 1) + 9) = (2 * n + 12) + k' * (2 * (n + 3) + 3 * k' + 9) := by ring
    rw [h_steps]
    rw [run_add]
    
    -- The first chunk of steps is tm_P_step for M = m + 2*k' and P = p + k'
    -- Note that m + 2 + 2(k'+1) = (m + 2*k') + 2 + 2
    -- and p + 1 + (k'+1) = (p + k') + 2
    have h_m : m + 2 + 2 * (k' + 1) = (m + 2 * k') + 2 + 2 := by omega
    have h_p : p + 1 + (k' + 1) = (p + k') + 2 := by omega
    
    -- We can rewrite the inner run with tm_P_step
    have step1 : run (P_Config_Pad b (m + 2 + 2 * (k' + 1)) n (p + 1 + (k' + 1))) (2 * n + 12) = P_Config_Pad b ((m + 2 * k') + 2) (n + 3) ((p + k') + 1) := by
      rw [h_m, h_p]
      exact tm_P_step b (m + 2 * k') n (p + k')
    
    rw [step1]
    
    -- Now we need to apply the IH for n+3
    -- The IH state is P_Config_Pad b (m + 2 + 2*k') (n+3) (p + 1 + k')
    -- Let's check that 
    have h_m2 : (m + 2 * k') + 2 = m + 2 + 2 * k' := by omega
    have h_p2 : (p + k') + 1 = p + 1 + k' := by omega
    have h_n2 : n + 3 * (k' + 1) = (n + 3) + 3 * k' := by omega
    
    rw [h_m2, h_p2]
    rw [ih (n + 3)]
    rw [h_n2]

-- Even Endgame (m=0)
theorem tm_even_endgame (b N p : Nat) :
  (run (P_Config_Pad b 0 N (p+2)) 2).state = none := by
  have step1 : run (P_Config_Pad b 0 N (p+2)) 1 = 
    { state := some ⟨5, by decide⟩, head := false, left := repeatOne b, right := true :: repeatOne N ++ repeatFalse (p+2) } := by
    simp [run, step, transition, P_Config_Pad]
  rw [show 2 = 1 + 1 by rfl, run_add, step1]
  have step2 : run { state := some ⟨5, by decide⟩, head := false, left := repeatOne b, right := true :: repeatOne N ++ repeatFalse (p+2) } 1 =
    { state := none, head := true, left := false :: repeatOne b, right := repeatOne N ++ repeatFalse (p+2) } := by
    cases b with
    | zero => simp [run, step, transition]
    | succ b' => simp [run, step, transition]
  rw [step2]

-- Odd Endgame (m=3, b>0)
theorem tm_odd_endgame (b' N p : Nat) :
  run (P_Config_Pad (b' + 1) 3 N (p+2)) (N + 30) = P_Config_Pad b' (N+6) 0 p := by
  have step1 : run (P_Config_Pad (b' + 1) 3 N (p+2)) 1 =
    { state := some ⟨5, by decide⟩, head := true, left := repeatOne 2 ++ false :: repeatOne (b'+1), right := repeatOne (N+1) ++ repeatFalse (p+2) } := by
    simp [run, step, transition, P_Config_Pad]

  have step2 : run { state := some ⟨5, by decide⟩, head := true, left := repeatOne 2 ++ false :: repeatOne (b'+1), right := repeatOne (N+1) ++ repeatFalse (p+2) } 1 =
    { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne 2 ++ false :: repeatOne (b'+1), right := repeatOne N ++ repeatFalse (p+2) } := by
    cases N with
    | zero => simp [run, step, transition]
    | succ N' => simp [run, step, transition]

  -- Step 3: A_shift N
  have step3 : run { state := some ⟨0, by decide⟩, head := true, left := false :: repeatOne 2 ++ false :: repeatOne (b'+1), right := repeatOne N ++ repeatFalse (p+2) } (N+1) =
    { state := some ⟨0, by decide⟩, head := false, left := repeatOne (N+1) ++ (false :: repeatOne 2 ++ false :: repeatOne (b'+1)), right := repeatFalse (p+1) } := by
    have hA := A_shift N (false :: repeatOne 2 ++ false :: repeatOne (b'+1)) (repeatFalse (p+2))
    have hp_head : headD' (repeatFalse (p+2)) false = false := rfl
    have hp_tail : tailD' (repeatFalse (p+2)) = repeatFalse (p+1) := rfl
    rw [hp_head, hp_tail] at hA
    exact hA

  sorry

-- A. The Abstraction Function (Decoding the Tape)
def decodeTape (c : Config) : MathState :=
  let a := countOnes c.left
  let after_a := c.left.drop a
  let b := match after_a with
           | false :: xs => countOnes xs
           | _ => 0
  { a := a, b := b }

-- B. Defining the "Clean" Invariant
-- Based on the BBchallenge definition, E(a,b) is TM in state E
def isValidLoopStart (c : Config) : Prop :=
  c.state = some ⟨4, by decide⟩ ∧
  c.head = false ∧
  (c.right.all (!·) = true) ∧
  let a := countOnes c.left
  let after_a := c.left.drop a
  match after_a with
  | false :: xs =>
    let b := countOnes xs
    let after_b := xs.drop b
    after_b.all (!·) = true
  | _ => False

-- C. The Block-Step Lemma (The Core Theorem)
theorem tm_simulates_math (c : Config) (hm : isValidLoopStart c) :
  ∃ (k : Nat), 
    let c' := run c k
    match nextMathState (decodeTape c) with
    | some m' => isValidLoopStart c' ∧ decodeTape c' = m'
    | none    => c'.state = none := by
  sorry

-- D. The Halting Equivalence Theorem
-- We define a simple inductive predicate for reaching none
inductive mathHalts : MathState → Prop where
| haltStep (m : MathState) (h : nextMathState m = none) : mathHalts m
| nextStep (m m' : MathState) (h : nextMathState m = some m') (h' : mathHalts m') : mathHalts m

theorem tm_halt_iff_math_condition (c : Config) (hm : isValidLoopStart c) :
  (∃ k, (run c k).state = none) ↔ mathHalts (decodeTape c) := by
  sorry

-- TEMP EVALS
deriving instance BEq for Config

-- Trace from ALL-ZEROS initial config to find the loop structure
-- Initial: state A, all zeros
def initConfig : Config := { state := some ⟨0, by decide⟩, head := false, left := [], right := [] }
-- Find first 5 visits to state E, head=false, right all zeros
#eval (List.range 200).filterMap (fun k =>
  let c := run initConfig k
  if c.state == some ⟨4, by decide⟩ && c.head == false && c.right.all (!·)
  then some (k, c) else none)
  |>.take 5
