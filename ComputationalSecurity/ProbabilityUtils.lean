/-
  Probability utilities for computational security proofs.
  Defines Bit, randomBit, Pr, and related lemmas.
-/

import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-- Bit is defined as Fin 2 -/
abbrev Bit := Fin 2

open BigOperators

/-- The sum of a function over all bits (0 and 1) can be expressed
as the sum of its values at 0 and 1. -/
theorem tsum_bit {f : Bit → ENNReal} : (∑' (b : Bit), f b) = f 0 + f 1 := by
  rw [tsum_fintype]
  rw [Fin.sum_univ_two]

/-- `randomBit` is a PMF that outputs 0 or 1 with equal probability. -/
noncomputable
abbrev randomBit : PMF Bit :=
  PMF.uniformOfFintype Bit

/-- The probability that `randomBit` outputs either 0 or 1 is 1/2. -/
theorem randomBit_apply (b : Bit) : randomBit b = 1/2 := by
  rw [randomBit, PMF.uniformOfFintype_apply]
  simp only [one_div, Fintype.card_fin, Nat.cast_two]

-- ============================================================
-- Additions to Defs_bit.lean
-- ============================================================

/-- Pr: the probability that a PMF Bool outputs true -/
noncomputable def Pr (p : PMF Bool) : ENNReal := p true

lemma Pr_bind (p : PMF α) (f : α → PMF Bool) :
    Pr (p.bind f) = ∑' a, p a * Pr (f a) := by
  simp [Pr, PMF.bind_apply]


lemma Pr_compl (p : PMF Bool) :
    Pr p = 1 - (p.bind (fun b => PMF.pure (!b))) true := by
  have h := p.tsum_coe
  rw [tsum_bool, add_comm] at h
  simp only [Pr, PMF.bind_apply, PMF.pure_apply,
             tsum_bool, Bool.not_true, Bool.not_false, ↓reduceIte]
  apply ENNReal.eq_sub_of_add_eq' (by norm_num)
  simp only [mul_one, Bool.true_eq_false, ↓reduceIte, mul_zero, add_zero, h]

/--
Algebraic identity used in the Guessing Lemma proof.
Rewrites the expression `1/2 * (1 - A) + 1/2 * B`
as `1/2 + 1/2 * (B - A)`, reflecting the step
  Pr[correct guess] = 1/2 + 1/2 * (Pr[A outputs 1 | X 1] - Pr[A outputs 1 | X 0]).
Requires `A ≤ 1`, `A ≤ B`, and `B ≠ ⊤` to handle `ENNReal` subtraction correctly.
-/
lemma formula1 (A B : ENNReal)
    (hA : A ≤ 1) (hAB : A ≤ B) (hBnotT : B ≠ ⊤) :
    1/2 * (1 - A) + 1/2 * B = 1/2 + 1/2 * (B - A) := by
  have hAnotT : A ≠ ⊤ := ne_top_of_le_ne_top hBnotT hAB
  rw [← ENNReal.toReal_eq_toReal_iff'
    (ENNReal.Finiteness.add_ne_top
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.sub_ne_top (by norm_num)))
      (ENNReal.mul_ne_top (by norm_num) hBnotT))
    (ENNReal.Finiteness.add_ne_top (by norm_num)
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.sub_ne_top hBnotT)))]
  rw [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hA,
      ENNReal.toReal_mul, ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le hAB, ENNReal.toReal_div, ENNReal.toReal_one]
  · simp only [ENNReal.toReal_ofNat, one_div]; ring
  · exact hBnotT
  · norm_num
  · exact ENNReal.mul_ne_top (by norm_num) (ENNReal.sub_ne_top hBnotT)
  · norm_num
  · exact ENNReal.mul_ne_top (by norm_num) (ENNReal.sub_ne_top (by norm_num))
  · exact ENNReal.mul_ne_top (by norm_num) hBnotT
