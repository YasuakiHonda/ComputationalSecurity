import ComputationalSecurity.BVCryptGameLib
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.BitVec
/-!
  Definitions and propositions for computational indistinguishability
  of probability distributions.
  Formalizes Definition 4.1 and Proposition 4.1 (Closure) from the textbook,
  along with supporting lemmas for the hybrid argument and bind preservation.

  Reference: Chapter 4, "Pseudorandomness"
  Authors: Yasuaki Honda
-/


namespace ComputationalSecurity

open PMF
open BVCryptGame

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

/-- `DistIndistinguishable` is symmetric. -/
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

/-- `DistIndistinguishable` is monotone in t: a bound for larger t implies one for smaller t. -/
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
  rw [DistIndistinguishable]
  intro D tD h_tD
  -- Reduce to indistinguishability of X and Y under the composed distinguisher D'.
  let D' : α → PMF Bit := fun x => (A x >>= D)
  let tD' := tA + tD
  have h_complexity : tD' ≤ t + tA := by omega
  have h_bound := hind D' tD' h_complexity
  have h_ANY_equiv (ANY : PMF α) : (do let d ← ((ANY >>= A) >>= D); PMF.pure (d == 1))
                 = (do let d ← (ANY >>= D'); PMF.pure (d == 1)) := by
    simp only [D', Fin.isValue, bind_assoc]
  unfold PrDX_one at h_bound ⊢
  rw [h_ANY_equiv X, h_ANY_equiv Y]
  exact h_bound

/-- Lemma 4.1 (Hybrid Lemma - Sum version):
    The total distance is bounded by the sum of adjacent distances.
    This is the core of the Hybrid Argument. -/
lemma hybrid_sum_inequality (f : ℕ → ℝ) (l : ℕ) :
    |f 0 - f l| ≤ ∑ i ∈ (Finset.range l), |f i - f (i + 1)| := by
  rw [abs_sub_comm (f 0) (f l)]
  rw [← Finset.sum_range_sub (fun i => f i) l]
  have h_tri := Finset.abs_sum_le_sum_abs (fun i => f (i + 1) - f i) (Finset.range l)
  have : ∑ i ∈ Finset.range l, |f (i + 1) - f i| = ∑ i ∈ Finset.range l, |f i - f (i + 1)| := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_sub_comm (f (i + 1)) (f i)]
  rw [this] at h_tri
  exact h_tri

/-- Lemma 4.2 (Hybrid Lemma - Contrapositive):
    If the total distance is greater than ε, then there exists at least one adjacent pair
    that has a distance greater than ε/l. -/
lemma hybrid_lemma
      (X : ℕ → PMF α) (l : ℕ) (t : ℕ) (ε : NNReal)
      (hl : l > 0)
      (D : α → PMF Bit)
      (hDInd : |PrDX_one (X 0) D - PrDX_one (X l) D| > (ε : ℝ)) :
    ∃ i < l, |PrDX_one (X i) D - PrDX_one (X (i + 1)) D| > (ε / l : ℝ) := by
  by_contra h_contra
  push_neg at h_contra
  have h_total_bound : |PrDX_one (X 0) D - PrDX_one (X l) D| ≤
      ∑ i ∈ Finset.range l, |PrDX_one (X i) D - PrDX_one (X (i + 1)) D| :=
    hybrid_sum_inequality (fun i => PrDX_one (X i) D) l
  have h_each_bound : ∀ i ∈ Finset.range l,
      |PrDX_one (X i) D - PrDX_one (X (i + 1)) D| ≤ (ε / l : ℝ) := by
    intro i hi
    exact h_contra i (Finset.mem_range.mp hi)
  have h_sum_bound : ∑ i ∈ Finset.range l, |PrDX_one (X i) D - PrDX_one (X (i + 1)) D| ≤
      ∑ i ∈ Finset.range l, (ε / l : ℝ) :=
    Finset.sum_le_sum h_each_bound
  have h_total : ∑ i ∈ Finset.range l, (ε / l : ℝ) = ε := by
    calc
      ∑ i ∈ Finset.range l, (ε / l : ℝ)
          = (Finset.range l).card • (ε / l : ℝ) := by rw [Finset.sum_const]
        _ = l • (ε / l : ℝ)               := by rw [Finset.card_range l]
        _ = (l : ℝ) * (ε / l : ℝ)         := by rw [nsmul_eq_mul]
        _ = (l : ℝ) * ((ε : ℝ) / (l : ℝ)) := by rfl
        _ = (ε : ℝ)                        := by
              apply mul_div_cancel₀; norm_cast; exact Nat.ne_zero_of_lt hl
  have h_final_bound : |PrDX_one (X 0) D - PrDX_one (X l) D| ≤ (ε : ℝ) := by
    calc |PrDX_one (X 0) D - PrDX_one (X l) D|
        ≤ ∑ i ∈ Finset.range l, |PrDX_one (X i) D - PrDX_one (X (i + 1)) D| := h_total_bound
      _ ≤ (ε : ℝ) := by rw [← h_total]; exact h_sum_bound
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
  have h_tri : |f 0 - f l| ≤ ∑ i ∈ Finset.range l, |f i - f (i + 1)| :=
    hybrid_sum_inequality f l
  have h_each_bound : ∀ i ∈ Finset.range l, |f i - f (i + 1)| ≤ (ε / l : ℝ) := by
    intro i hi
    exact h_adjacent i (Finset.mem_range.mp hi) D tD h_tD
  have h_sum_bound : ∑ i ∈ Finset.range l, |f i - f (i + 1)| ≤
      ∑ i ∈ Finset.range l, (ε / l : ℝ) :=
    Finset.sum_le_sum h_each_bound
  have h_total : ∑ i ∈ Finset.range l, (ε / l : ℝ) = ε := by
    calc
      ∑ i ∈ Finset.range l, (ε / l : ℝ)
          = (Finset.range l).card • (ε / l : ℝ) := by rw [Finset.sum_const]
        _ = l • (ε / l : ℝ)               := by rw [Finset.card_range l]
        _ = (l : ℝ) * (ε / l : ℝ)         := by rw [nsmul_eq_mul]
        _ = (l : ℝ) * ((ε : ℝ) / (l : ℝ)) := by rfl
        _ = (ε : ℝ)                        := by
              apply mul_div_cancel₀; norm_cast; exact Nat.ne_zero_of_lt hl
  calc
    |f 0 - f l| ≤ ∑ i ∈ Finset.range l, |f i - f (i + 1)| := h_tri
    _ ≤ (ε : ℝ) := by rw [← h_total]; exact h_sum_bound

/-- `DistIndistinguishable` is preserved under monadic bind
    when indistinguishability holds pointwise. -/
lemma DistIndistinguishable_bind {α β : Type} [Fintype α] [Fintype β]
    (X : PMF α) (Y1 Y2 : α → PMF β) (t : ℕ) (ε : NNReal) :
    (∀ a, DistIndistinguishable (Y1 a) (Y2 a) t ε) →
    DistIndistinguishable (X >>= Y1) (X >>= Y2) t ε := by
  intro h_indist D tD h_tD
  unfold DistIndistinguishable at h_indist
  -- Rewrite Pr[D(X >>= Y)] as a weighted sum over X.
  have h_linear (Y : α → PMF β) :
      PrDX_one (X >>= Y) D = ∑ a, (X a).toReal * (PrDX_one (Y a) D) := by
    unfold PrDX_one Pr
    simp only [bind_assoc]
    erw [PMF.bind_apply]
    simp only [tsum_fintype]
    rw [ENNReal.toReal_sum]
    · simp_rw [ENNReal.toReal_mul]
    · intro a _
      apply ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  rw [h_linear Y1, h_linear Y2, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    |∑ a, (X a).toReal * (PrDX_one (Y1 a) D - PrDX_one (Y2 a) D)|
      ≤ ∑ a, |(X a).toReal * (PrDX_one (Y1 a) D - PrDX_one (Y2 a) D)| := by
        apply Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a, (X a).toReal * |PrDX_one (Y1 a) D - PrDX_one (Y2 a) D| := by
          congr; funext a
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ ∑ a, (X a).toReal * (ε : ℝ) := by
          apply Finset.sum_le_sum; intro a _
          apply mul_le_mul_of_nonneg_left (h_indist a D tD h_tD) ENNReal.toReal_nonneg
      _ = (ε : ℝ) := by
          rw [← Finset.sum_mul]
          have h_tsum : ∑ a, X a = ∑' a, X a := (tsum_fintype _).symm
          rw [← ENNReal.toReal_sum]
          · rw [h_tsum, PMF.tsum_coe]; simp
          · intro a _; apply PMF.apply_ne_top

end ComputationalSecurity



/-! ### Hybrid Argument Support -/

open BigOperators
/-
/-- Finite version of hybrid_sum_inequality using Fin l.
    Allows summation over a fixed index range without Nat-based off-by-one errors. -/
lemma hybrid_sum_inequality_fin {l : ℕ} (f : Fin (l + 1) → ℝ) :
    |f 0 - f (Fin.last l)| ≤ ∑ i : Fin l, |f i.castSucc - f i.succ| := by
  let f_nat := fun (i : ℕ) => f (if h : i < l + 1 then ⟨i, h⟩ else Fin.last l)
  have h_sum : ∑ i : Fin l, |f i.castSucc - f i.succ| = ∑ i ∈ Finset.range l, |f_nat i - f_nat (i + 1)| := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hi_l : i < l := Finset.mem_range.mp hi
    have h_curr : i < l + 1 := by omega
    have h_next : i + 1 < l + 1 := by omega
    dsimp [f_nat]
    rw [dif_pos h_curr, dif_pos h_next]
    rfl
  rw [h_sum]
  have h_nat_0 : f_nat 0 = f 0 := by dsimp [f_nat]
  have h_nat_l : f_nat l = f (Fin.last l) := by dsimp [f_nat]; rw [dif_pos (by omega)]; rfl
  rw [← h_nat_0, ← h_nat_l]
  exact hybrid_sum_inequality f_nat l

/-- Finite version of hybrid_lemma. Returns an index i : Fin l.
    This is the most ergonomic way to apply the hybrid argument in BV proofs. -/
lemma hybrid_lemma_fin {α : Type} (X : Fin (l + 1) → PMF α) (l : ℕ) (ε : ℝ)
      (hl : l > 0) (D : α → PMF Bit)
      (hDInd : |PrDX_one (X 0) D - PrDX_one (X (Fin.last l)) D| > ε) :
    ∃ i : Fin l, |PrDX_one (X i.castSucc) D - PrDX_one (X i.succ) D| > ε / l := by
  let X_nat := fun (i : ℕ) => X (if h : i < l + 1 then ⟨i, h⟩ else Fin.last l)
  have h_nat_0 : X_nat 0 = X 0 := by dsimp [X_nat]; rw [dif_pos (by omega)]
  have h_nat_l : X_nat l = X (Fin.last l) := by dsimp [X_nat]; rw [dif_pos (by omega)]; rfl
  have h_total_nat : |PrDX_one (X_nat 0) D - PrDX_one (X_nat l) D| > ε := by
    rwa [h_nat_0, h_nat_l]
  obtain ⟨i, hi_l, h_step⟩ := hybrid_lemma X_nat l (t := 0) (ε := ⟨ε.toNNReal, sorry⟩) hl D h_total_nat
  · use ⟨i, hi_l⟩
    have h_curr : i < l + 1 := by omega
    have h_next : i + 1 < l + 1 := by omega
    dsimp [X_nat] at h_step
    rwa [dif_pos h_curr, dif_pos h_next] at h_step
  -- Note: The t and ε in hybrid_lemma are placeholders here;
  -- the core inequality only depends on the PrDX_one values.

/-- Finite version of transitivity for indistinguishability. -/
theorem transitivity_fin {α : Type} (X : Fin (l + 1) → PMF α) (l : ℕ) (t : ℕ) (ε : NNReal)
    (hl : l > 0)
    (h_adjacent : ∀ i : Fin l, DistIndistinguishable (X i.castSucc) (X i.succ) t (ε / l)) :
    DistIndistinguishable (X 0) (X (Fin.last l)) t ε := by
  let X_nat := fun (i : ℕ) => X (if h : i < l + 1 then ⟨i, h⟩ else Fin.last l)
  have h_nat_adj : ∀ i < l, DistIndistinguishable (X_nat i) (X_nat (i + 1)) t (ε / l) := by
    intro i hi
    have h_curr : i < l + 1 := by omega
    have h_next : i + 1 < l + 1 := by omega
    dsimp [X_nat]
    rw [dif_pos h_curr, dif_pos h_next]
    exact h_adjacent ⟨i, hi⟩
  have h_total := transitivity X_nat l t ε hl h_nat_adj
  have h_nat_0 : X_nat 0 = X 0 := by dsimp [X_nat]; rw [dif_pos (by omega)]
  have h_nat_l : X_nat l = X (Fin.last l) := by dsimp [X_nat]; rw [dif_pos (by omega)]; rfl
  rwa [h_nat_0, h_nat_l] at h_total
-/
