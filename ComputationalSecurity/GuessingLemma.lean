/-
  Formalization of Lemma 3.1 (Guessing Lemma).
  Reference: Textbook Chapter 3, p. 33.

  Given a distinguisher A that tells apart two distributions X 0 and X 1,
  the Guessing Lemma constructs an algorithm B that correctly identifies which
  distribution a sample came from with probability strictly greater than 1/2.

  More precisely, if
    |Pr[a ← A(X 1); a = 1] - Pr[a ← A(X 0); a = 1]| > ε
  then there exists B such that
    Pr[b ← randomBit; x ← X b; a ← B x; a = b] > 1/2 * (1 + ε).

  The proof splits into two cases based on the sign of the difference:
    - Case 1: Pr[A on X 1] - Pr[A on X 0] > ε  →  use A directly as B.
    - Case 2: Pr[A on X 0] - Pr[A on X 1] > ε  →  use flipA A (the bit-flipped A) as B.

  File organization:
    - guessing_lemma_case1: Case 1 (A used directly).
    - flipA, Pr_flip: definition of the flipped adversary and its probability identity.
    - guessing_lemma_case2: Case 2 (flipA A used).
    - guessing_lemma_abs: Combined absolute-value version used in practice.

  Authors: Yasuaki Honda
-/

import ComputationalSecurity.ProbabilityUtils
set_option linter.style.emptyLine false

namespace ComputationalSecurity

/--
Lemma 3.1 [Guessing Lemma case 1]
For a family of distributions X : Bit → PMF α and an algorithm A : α → PMF Bit
outputting 0 or 1, if
  Pr[x ← X 1; a ← A x; a == 1] - Pr[x ← X 0; a ← A x; a == 1] > ε
then
  Pr[b ← randomBit; x ← X b; a ← A x; a == b] > 1/2 * (1 + ε).
-/
lemma guessing_lemma_case1 {α : Type}
    (A : α → PMF Bit)
    (X : Bit → PMF α)
    (ε : ENNReal)
    (h : Pr (do let x ← X 1; let a ← A x; pure (a == 1))
       - Pr (do let x ← X 0; let a ← A x; pure (a == 1)) > ε) :
    Pr (do let b ← randomBit; let x ← X b; let a ← A x; pure (a == b)) > 1/2 * (1 + ε) := by

  calc Pr (do let b ← randomBit; let x ← X b; let a ← A x; pure (a == b))
      = randomBit 0 * Pr (do let x ← X 0; let a ← A x; pure (a == 0))
      + randomBit 1 * Pr (do let x ← X 1; let a ← A x; pure (a == 1)) := by
        change Pr (randomBit.bind (fun b => do let x ← X b; let a ← A x; pure (a == b))) = _
        rw [Pr_bind]
        rw [tsum_bit]

      _= 1/2 * (1 - Pr (do let x ← X 0; let a ← A x; pure (a == 1)))
        + 1/2 * Pr (do let x ← X 1; let a ← A x; pure (a == 1)) := by
        rw [randomBit_apply 0, randomBit_apply 1]
        congr
        conv_lhs => rw [Pr_compl]
        rw [Pr]
        congr 2
        apply PMF.ext; intro b
        simp only [Bind.bind, PMF.bind_apply, PMF.pure_apply]
        fin_cases b <;> simp
        all_goals
          simp only [show (pure true : PMF Bool) = PMF.pure true from rfl,
                     show (pure false : PMF Bool) = PMF.pure false from rfl,
                     PMF.pure_apply]
          simp only [Fin.isValue, Bool.false_eq_true, ↓reduceIte, mul_zero, mul_one, zero_add,
            Bool.true_eq_false]
      -- = 1/2 + 1/2 * (Pr[x ← X 1; a ← A x; a == 1]
      --               - Pr[x ← X 0; a ← A x; a == 1])
      _= 1/2 + 1/2 * (Pr (do let x ← X 1; let a ← A x; pure (a == 1))
                      - Pr (do let x ← X 0; let a ← A x; pure (a == 1))) := by
          rw [formula1]
          · exact PMF.coe_le_one _ _
          · by_contra hc
            push_neg at hc
            have hzero : Pr (do let x ← X 1; let a ← A x; pure (a == 1))
                      - Pr (do let x ← X 0; let a ← A x; pure (a == 1)) = 0 := by
                rw [tsub_eq_zero_iff_le]
                exact le_of_lt hc
            rw [hzero] at h
            apply ENNReal.not_lt_zero h
          · exact PMF.apply_ne_top _ _
      -- > 1/2 * (1 + ε)
      _> 1/2 * (1 + ε) := by
        rw [mul_add, mul_one]
        apply ENNReal.add_lt_add_left
        · norm_num
        · apply ENNReal.mul_lt_mul_right
          · norm_num
          · norm_num
          · exact h

-- ============================================================
-- Guessing Lemma with absolute value (for use in pa_gt_half)
-- ============================================================

/-- Flip algorithm: reverses the output of A (0 ↔ 1). -/
noncomputable def flipA {α : Type} (A : α → PMF Bit) : α → PMF Bit :=
  fun x => do
    let b ← A x
    pure (if b = 0 then 1 else 0)

/-- Flipping the algorithm complements the success probability.
    Pr[x ← X; a ← flipA A x; a == 1] = 1 - Pr[x ← X; a ← A x; a == 1] -/
lemma Pr_flip {α : Type} (A : α → PMF Bit) (X : PMF α) :
    Pr (do let x ← X; let a ← flipA A x; pure (a == 1)) =
    1 - Pr (do let x ← X; let a ← A x; pure (a == 1)) := by
  simp only [Pr, flipA, Bind.bind, PMF.bind_apply, tsum_fintype, Fin.sum_univ_two,
             show (pure true : PMF Bool) = PMF.pure true from rfl,
             PMF.pure_apply,
             show ((0 : Bit) == (1 : Bit)) = false from by decide,
             show ((1 : Bit) == (1 : Bit)) = true from by decide,
             show ((1 : Bit) : Bit) = (0 : Bit) ↔ False from by decide]
  simp only [↓reduceIte, mul_one]
  have hpf : (PMF.pure false) true = 0 := by simp [PMF.pure_apply]
  have h10 : (PMF.pure (1 : Bit)) (0 : Bit) = 0 := by simp [PMF.pure_apply]
  have h00 : (PMF.pure (0 : Bit)) (0 : Bit) = 1 := by simp [PMF.pure_apply]
  have h11 : (PMF.pure (1 : Bit)) (1 : Bit) = 1 := by simp [PMF.pure_apply]
  have h01 : (PMF.pure (0 : Bit)) (1 : Bit) = 0 := by simp [PMF.pure_apply]
  simp only [show (pure (1 : Bit) : PMF Bit) = PMF.pure 1 from rfl,
             show (pure (0 : Bit) : PMF Bit) = PMF.pure 0 from rfl,
             show (pure false : PMF Bool) = PMF.pure false from rfl,
             h10, h00, h11, h01, hpf]
  simp only [mul_zero, zero_add, mul_one, add_zero]
  have hsum : ∀ x, (A x) 0 + (A x) 1 = 1 := fun x => by
    have := (A x).tsum_coe
    rw [tsum_fintype, Fin.sum_univ_two] at this
    exact this
  apply ENNReal.eq_sub_of_add_eq'
  · apply ne_top_of_le_ne_top (by norm_num : (1 : ENNReal) ≠ ⊤)
    norm_num
  · rw [← ENNReal.tsum_add]
    conv_lhs => arg 1; ext a; rw [← mul_add]; rw [hsum a]
    simp only [mul_one, PMF.tsum_coe]

/--
Lemma 3.1 [Guessing Lemma case 2]
For a family of distributions X : Bit → PMF α and an algorithm A : α → PMF Bit
outputting 0 or 1, if
  Pr[x ← X 0; a ← A x; a == 1] - Pr[x ← X 1; a ← A x; a == 1] > ε
then there exists B such that
  Pr[b ← randomBit; x ← X b; a ← B x; a == b] > 1/2 * (1 + ε).
Note: B = flipA A, not A itself (correcting the textbook).
-/
lemma guessing_lemma_case2 {α : Type}
    (A : α → PMF Bit)
    (X : Bit → PMF α)
    (ε : ENNReal)
    (h : Pr (do let x ← X 0; let a ← A x; pure (a == 1))
       - Pr (do let x ← X 1; let a ← A x; pure (a == 1)) > ε) :
    ∃ B : α → PMF Bit,
      Pr (do let b ← randomBit; let x ← X b; let a ← B x; pure (a == b)) > 1/2 * (1 + ε) := by
  use flipA A
  apply guessing_lemma_case1 (flipA A) X ε
  rw [Pr_flip A (X 1), Pr_flip A (X 0)]
  have hp0 : Pr (do let x ← X 0; let a ← A x; pure (a == 1)) ≤ 1 := PMF.coe_le_one _ _
  rw [ENNReal.sub_sub_sub_cancel_left (by norm_num) hp0]
  exact h

/--
Lemma 3.1 [Guessing Lemma with absolute value] (ENNReal tsub version).
If  Pr[x ← X 1; a ← A x; a == 1] - Pr[x ← X 0; a ← A x; a == 1] > ε
 or Pr[x ← X 0; a ← A x; a == 1] - Pr[x ← X 1; a ← A x; a == 1] > ε
then there exists B such that
  Pr[b ← randomBit; x ← X b; a ← B x; a == b] > 1/2 * (1 + ε).
-/
lemma guessing_lemma_abs {α : Type}
    (A : α → PMF Bit)
    (X : Bit → PMF α)
    (ε : ENNReal)
    (h : Pr (do let x ← X 1; let a ← A x; pure (a == 1))
       - Pr (do let x ← X 0; let a ← A x; pure (a == 1)) > ε
      ∨ Pr (do let x ← X 0; let a ← A x; pure (a == 1))
       - Pr (do let x ← X 1; let a ← A x; pure (a == 1)) > ε) :
    ∃ B : α → PMF Bit,
      Pr (do let b ← randomBit; let x ← X b; let a ← B x; pure (a == b)) > 1/2 * (1 + ε) := by
  rcases h with h1 | h0
  · exact ⟨A, guessing_lemma_case1 A X ε h1⟩
  · exact guessing_lemma_case2 A X ε h0

end ComputationalSecurity
