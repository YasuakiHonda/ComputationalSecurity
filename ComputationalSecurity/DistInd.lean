/-
  Definitions and propositions for computational indistinguishability
  of probability distributions.
  Formalizes Definition 4.1 and Proposition 4.1 (Closure) from the textbook.

  Reference: Chapter 4, "Pseudorandomness"
  Authors: Yasuaki Honda
-/

import ComputationalSecurity.ProbabilityUtils
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.BitVec
namespace ComputationalSecurity

open PMF

variable {α β : Type}

/-- A helper definition to represent the probability that a distinguisher D
    outputs 1 given an input from distribution X. -/
noncomputable def PrDX_one (X : PMF α) (D : α → PMF Bit) : ℝ :=
  (Pr (do let a ← (X >>= D); PMF.pure (a == 1))).toReal

/-- Definition 4.1: (t, ε)-Computational Indistinguishability of distributions.
    Probability distributions X and Y over α are (t, ε)-indistinguishable if
    for every algorithm A with complexity tA ≤ t,
    |Pr[x ← X; A x = 1] - Pr[y ← Y; A y = 1]| ≤ ε. -/
def DistIndistinguishable
    (X Y : PMF α)
    (t : ℕ) (ε : NNReal) : Prop :=
  ∀ (D : α → PMF Bit) (tD : ℕ),
    tD ≤ t →
    |PrDX_one X D - PrDX_one Y D| ≤ (ε : ℝ)

lemma DistIndistinguishable_comm (X Y : PMF α) (t : ℕ) (ε : NNReal) :
    DistIndistinguishable X Y t ε ↔ DistIndistinguishable Y X t ε := by
  constructor
  · intro h D tD h_tD
    have h_bound := h D tD h_tD
    rw [abs_sub_comm (PrDX_one X D) (PrDX_one Y D)] at h_bound
    exact h_bound
  · intro h D tD h_tD
    have h_bound := h D tD h_tD
    rw [abs_sub_comm (PrDX_one Y D) (PrDX_one X D)] at h_bound
    exact h_bound

lemma DistIndistinguishable_mono (X Y : PMF α) (t t' : ℕ) (ε : NNReal)
    (h : DistIndistinguishable X Y t ε) (ht : t' ≤ t) :
    DistIndistinguishable X Y t' ε := by
  intro D tD htD
  exact h D tD (htD.trans ht)

/-- Proposition 4.1 [Closure]: Computational indistinguishability is preserved
    under efficient computation.
    If X ≈(t+tA, ε) Y and A is an algorithm with complexity tA,
    then (do x ← X; A x) ≈(t, ε) (do y ← Y; A y). -/
theorem closure
    (X Y : PMF α)
    (A : α → PMF β)
    (t tA : ℕ) (ε : NNReal)
    (hind : DistIndistinguishable X Y (t + tA) ε) :
        DistIndistinguishable (X >>= A) (Y >>= A) t ε := by
  -- 1. Unfold the definition of DistIndistinguishable for the goal.
  -- We consider an arbitrary distinguisher D for the distributions (X >>= A) and (Y >>= A).
  rw [DistIndistinguishable]
  intro D tD h_tD

  -- 2. Construct a reduction distinguisher D' : α → PMF Bit.
  -- D' is the composition of the algorithm A and the distinguisher D.
  -- Logic: If D can distinguish A(X) from A(Y), then D' can distinguish X from Y.
  let D' : α → PMF Bit := fun x => (A x >>= D)

  -- 3. Show that the complexity of D' is within the bound (t + tA).
  -- Since tD ≤ t and A has complexity tA, the combined complexity tD' is tA + tD.
  let tD' := tA + tD
  have h_complexity : tD' ≤ t + tA := by
    -- Goal: tA + tD ≤ t + tA
    -- This follows from h_tD : tD ≤ t.
    omega

  -- 4. Apply the original indistinguishability (hind) to the constructed D'.
  -- This provides the absolute difference bound ε for X and Y under D'.
  have h_bound := hind D' tD' h_complexity

  -- 5. Use the Monad associativity (PMF.bind_bind) to bridge the gap.
  -- We need to prove that:
  -- Pr[z ← (X >>= A); d ← D z; pure (d == 1)] = Pr[x ← X; d ← D' x; pure (d == 1)]

  -- Intermediate goal for X and Y
  have h_ANY_equiv (ANY : PMF α) : (do let d ← ((ANY >>= A) >>= D); PMF.pure (d == 1))
                 = (do let d ← (ANY >>= D'); PMF.pure (d == 1)) := by
    -- Goal: (X >>= A) >>= (fun z => D z >>= (fun d => pure (d == 1)))
    --       = X >>= (fun x => (A x >>= D) >>= (fun d => pure (d == 1)))
    -- Use PMF.bind_bind multiple times.
    simp only [D']
    simp only [Fin.isValue, bind_assoc]

  -- 6. Final calculation.
  -- Rewrite the goal using the equivalences and apply the hypothesis bound.
  unfold PrDX_one at h_bound ⊢
  rw [h_ANY_equiv X, h_ANY_equiv Y]
  exact h_bound


/-- Lemma 4.1 (Hybrid Lemma - Sum version):
    The total distance is bounded by the sum of adjacent distances.
    This is the core of the Hybrid Argument. -/
lemma hybrid_sum_inequality (f : ℕ → ℝ) (l : ℕ) :
    |f 0 - f l| ≤ ∑ i ∈ (Finset.range l), |f i - f (i + 1)| := by
  -- Step 1: Normalize the order of subtraction using |a - b| = |b - a|.
  -- This makes it easier to use the telescoping sum lemma.
  rw [abs_sub_comm (f 0) (f l)]
  -- Step 2: Represent (f l - f 0) as a telescoping sum.
  -- Finset.sum_range_sub f l proves: ∑ i in range l, (f (i+1) - f i) = f l - f 0.
  rw [← Finset.sum_range_sub (fun i => f i) l]
  -- Step 3: Apply the generalized triangle inequality for sums.
  -- Mathlib: abs_sum_le_sum_abs : |∑ x_i| ≤ ∑ |x_i|
  -- Goal: |∑ (f (i+1) - f i)| ≤ ∑ |f (i+1) - f i|
  have h_tri := Finset.abs_sum_le_sum_abs (fun i => f (i + 1) - f i) (Finset.range l)

  have : ∑ i ∈  Finset.range l, |f (i + 1) - f i| = ∑ i ∈  Finset.range l, |f i - f (i + 1)| := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_sub_comm (f (i + 1)) (f i)]
  rw [this] at h_tri
  exact h_tri

/-- Lemma 4.2 (Hybrid Lemma - Contrapositive):
    If the total distance is greater than ε, then there exists at least one adjacent pair
    that has a distance greater than ε/l.
-/
lemma hybrid_lemma
      (X : ℕ → PMF α) (l : ℕ) (t : ℕ) (ε : NNReal)
      (hl : l > 0)
      (D : α → PMF Bit)
      (hDInd : |PrDX_one (X 0) D - PrDX_one (X l) D| > (ε : ℝ)) :
    ∃ i < l, |PrDX_one (X i) D - PrDX_one (X (i + 1)) D| > (ε / l : ℝ) := by
  -- Step 1: Assume the negation of the conclusion to derive a contradiction.
  by_contra h_contra
  push_neg at h_contra

  -- Step 2: Use the Hybrid Lemma (sum version) to bound the total distance.
  have h_total_bound : |PrDX_one (X 0) D - PrDX_one (X l) D| ≤ ∑ i ∈ Finset.range l, |PrDX_one (X i) D - PrDX_one (X (i + 1)) D| := by
    apply hybrid_sum_inequality (fun i => PrDX_one (X i) D) l
  -- Step 3: Use the assumption to bound each adjacent distance.
  have h_each_bound : ∀ i ∈ Finset.range l, |PrDX_one (X i) D - PrDX_one (X (i + 1)) D| ≤ (ε / l : ℝ) := by
    intro i hi
    -- Finset.mem_range.mp hi converts 'i ∈ range l' to 'i < l'
    exact h_contra i (Finset.mem_range.mp hi)
  -- Step 4: Sum the bounds to get a total bound.
  have h_sum_bound : ∑ i ∈ Finset.range l, |PrDX_one (X i) D - PrDX_one (X (i + 1)) D| ≤ ∑ i ∈ Finset.range l, (ε / l : ℝ) := by
    -- Use Finset.sum_le_sum to bound the total sum
    apply Finset.sum_le_sum h_each_bound
  -- Step 5: Calculate the total bound for the constant sum.
  have h_total : ∑ i ∈ Finset.range l, (ε / l : ℝ) = ε := by
    -- Use Finset.sum_const: sum of (ε/l) l times is l * (ε/l)
    -- This requires handling the coercion from NNReal to Real
    -- Using calc to show the step-by-step simplification of the constant sum.
    calc
      ∑ i ∈ Finset.range l, (ε / l : ℝ)
          = (Finset.range l).card • (ε / l : ℝ) := by
            -- The sum of a constant c over a finset s is s.card • c.
            rw [Finset.sum_const]
        _ = l • (ε / l : ℝ) := by
            -- The cardinality of Finset.range l is exactly l.
            rw [Finset.card_range l]
        _ = (l : ℝ) * (ε / l : ℝ) := by
            -- Convert scalar multiplication (nsmul) to real multiplication.
            rw [nsmul_eq_mul]
        _ = (l : ℝ) * ((ε : ℝ) / (l : ℝ)) := by rfl
        _ = (ε : ℝ) := by
            apply mul_div_cancel₀
            -- Prove (l : ℝ) ≠ 0
            norm_cast
            exact Nat.ne_zero_of_lt hl
  -- Step 6: Derive the final contradiction.
  have h_final_bound : |PrDX_one (X 0) D - PrDX_one (X l) D| ≤ (ε : ℝ) := by calc
    |PrDX_one (X 0) D - PrDX_one (X l) D| ≤ ∑ i ∈ Finset.range l, |PrDX_one (X i) D - PrDX_one (X (i + 1)) D| := h_total_bound
    _ ≤ (ε : ℝ) := by
      rw [← h_total]
      exact h_sum_bound
  linarith [hDInd, h_final_bound]

/-- The transitivity property of distinguishability. -/
theorem transitivity
    (X : ℕ → PMF α) (l : ℕ) (t : ℕ) (ε : NNReal)
    (hl : l > 0)
    (h_adjacent : ∀ i < l, DistIndistinguishable (X i) (X (i + 1)) t (ε / l)) :
    DistIndistinguishable (X 0) (X l) t ε := by
  rw [DistIndistinguishable]
  intro D tD h_tD

  let f := fun i => PrDX_one (X i) D

  -- Use '∈' here as well
  have h_tri : |f 0 - f l| ≤ ∑ i ∈ Finset.range l, |f i - f (i + 1)| :=
    hybrid_sum_inequality f l

  have h_each_bound : ∀ i ∈ Finset.range l, |f i - f (i + 1)| ≤ (ε / l : ℝ) := by
    intro i hi
    -- Finset.mem_range.mp hi converts 'i ∈ range l' to 'i < l'
    exact h_adjacent i (Finset.mem_range.mp hi) D tD h_tD

  have h_sum_bound : ∑ i ∈ Finset.range l, |f i - f (i + 1)| ≤ ∑ i ∈ Finset.range l, (ε / l : ℝ) := by
    -- Use Finset.sum_le_sum to bound the total sum
    apply Finset.sum_le_sum h_each_bound

  have h_total : ∑ i ∈ Finset.range l, (ε / l : ℝ) = ε := by
    -- Use Finset.sum_const: sum of (ε/l) l times is l * (ε/l)
    -- This requires handling the coercion from NNReal to Real
    -- Using calc to show the step-by-step simplification of the constant sum.
    calc
      ∑ i ∈ Finset.range l, (ε / l : ℝ)
          = (Finset.range l).card • (ε / l : ℝ) := by
            -- The sum of a constant c over a finset s is s.card • c.
            rw [Finset.sum_const]
        _ = l • (ε / l : ℝ) := by
            -- The cardinality of Finset.range l is exactly l.
            rw [Finset.card_range l]
        _ = (l : ℝ) * (ε / l : ℝ) := by
            -- Convert scalar multiplication (nsmul) to real multiplication.
            rw [nsmul_eq_mul]
        _ = (l : ℝ) * ((ε : ℝ) / (l : ℝ)) := by rfl
        _ = (ε : ℝ) := by
            apply mul_div_cancel₀
            -- Prove (l : ℝ) ≠ 0
            norm_cast
            exact Nat.ne_zero_of_lt hl
  calc
    |f 0 - f l| ≤ ∑ i ∈ Finset.range l, |f i - f (i + 1)| := h_tri
    _ ≤ (ε : ℝ) := by
      rw [← h_total]
      exact h_sum_bound

/-- Definition 4.3: Pseudorandom Distribution.
    A distribution X over {0, 1}^n is (t, ε)-pseudorandom if
    it is (t, ε)-indistinguishable from the uniform distribution Un. -/
def IsPseudorandom {n : ℕ} (X : PMF (BitVec n)) (t : ℕ) (ε : NNReal) : Prop :=
  DistIndistinguishable X (U n) t ε

/-- Definition 4.4: (t, ε)-Pseudorandom Generator (PRG).
    A function G: {0, 1}^n → {0, 1}^m is a (t, ε)-PRG if
    1. The output length m is greater than the input length n (expansion).
    2. The distribution G(s) where s ← Un is (t, ε)-pseudorandom. -/
def IsPRG {n m : ℕ} (G : BitVec n → BitVec m) (t : ℕ) (ε : NNReal)
      [Fintype (BitVec n)] [Fintype (BitVec m)] : Prop :=
  (n < m) ∧ IsPseudorandom (PMF.map G (U n)) t ε

end ComputationalSecurity
