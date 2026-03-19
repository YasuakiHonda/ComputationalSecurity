/-
  Formalization of Theorem 3.1 (textbook Chapter 3, pp.34-35):
  (t, α, ε/2)-Semantic Security implies (t, ε)-Indistinguishability.

  ----------------------------------------------------------------
  Proof structure (following textbook pp.34-35):
  ----------------------------------------------------------------
  Proof by contradiction. Assume Indistinguishable fails.

  Step 1: Obtain adversary (A1, A2) with |p0 - p1| > ε.
  Step 2: Apply Guessing Lemma (Lemma 3.1):
            Pr[b ← randomBit; m ← mDist b; a ← A2(Enc(k,m), st); a == b]
              > 1/2 * (1 + ε)
  Step 3: Construct semantic security adversary (B1, B2 = A2):
            B1 samples (m0, m1, st) from A1, sets
              mDist = randomBit.map ![m0, m1]  (uniform over {m0, m1}),
              h     = const 0,
              R m a = if (m,a) = (m0,0) ∨ (m,a) = (m1,1) then 1 else 0
              st'   = st  (pass original state through to B2)
            B2 = A2  (receives c and st, ignores h-value)
  Step 4: Show:
            pa(B1, B2) > 1/2 * (1 + ε/2)    (from Step 2)
            ps(B1, S)  ≤ 1/2                 (S has no info about b)
  Step 5: |pa - ps| > ε/2, contradicting SemanticallySecure.

  ----------------------------------------------------------------
  File organization:
  ----------------------------------------------------------------
    Section 1 (def B1, B2):      Tool for Step 3
    Section 2 (lemma pa_gt):     Tool for Step 4a — pa lower bound
    Section 3 (lemmas):          Tools for Step 4b — ps upper bound
    Section 4 (theorem):         Steps 1–5 assembled

  Authors: Yasuaki Honda
-/

import ComputationalSecurity.Defs

namespace ComputationalSecurity

open PMF

variable {M C K St : Type} [DecidableEq M]

-- ============================================================
-- Section 1: Construction of (B1, B2) (tool for Step 3)
-- ============================================================

/-- Semantic security adversary B1 constructed from
    indistinguishability adversary A1 : PMF (M × M × St).
    B1 outputs (mDist, h, R, st) where:
      mDist = randomBit.map ![m0, m1]  (uniform over {m0, m1})
      h     = const 0 (no partial information)
      R m a = 1 iff (m, a) = (m0, 0) ∨ (m, a) = (m1, 1)
      st    = original state from A1, passed through to B2 -/
noncomputable def B1
    (A1 : PMF (M × M × St)) :
    PMF (PMF M × (M → Bit) × (M → Bit → Bit) × St) :=
  do
    let (m0, m1, st) ← A1
    let mDist : PMF M := randomBit.map ![m0, m1]
    let h : M → Bit := fun _ => 0
    let R : M → Bit → Bit := fun m a =>
      if (m, a) = (m0, 0) ∨ (m, a) = (m1, 1) then 1 else 0
    PMF.pure (mDist, h, R, st)

/-- Semantic security adversary B2 = A2.
    B2 receives ciphertext c, h-value (ignored), and original state st,
    then calls A2 with c and st directly. -/
noncomputable def B2 (A2 : C → St → PMF Bit) : C → Bit → St → PMF Bit :=
  fun c _ st => A2 c st

-- ============================================================
-- Section 2: pa lower bound (tool for Step 4a)
-- ============================================================

/-- If |p0 - p1| > ε then pa(B1(A1), B2(A2)) > 1/2 * (1 + ε/2). -/
lemma pa_gt_half
    (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit)
    (ε : ENNReal)
    (h : |(p0 Enc Gen A1 A2).toReal - (p1 Enc Gen A1 A2).toReal| > ε.toReal) :
    pa Enc Gen (B1 A1) (B2 A2) > 1 / 2 * (1 + ε / 2) := by
  sorry

-- ============================================================
-- Section 3: ps upper bound (tools for Step 4b)
-- ============================================================

/-- For fixed (m0, m1) with m0 ≠ m1, the inner probability equals 1/2.
    This lemma is preserved for reference, though ps_le_half does not use it directly.
    S receives only h(m) = 0 and st, so s is independent of b.
    R(m, s) = 1 iff s = b (R(m0,s)=1 ↔ s=0 and R(m1,s)=1 ↔ s=1). -/
lemma inner_eq_half (m0 m1 : M) (st : St) (S : Bit → St → PMF Bit)
    (hne : m0 ≠ m1) :
    ((randomBit.map ![m0, m1]).bind (fun m =>
      (S 0 st).bind (fun s =>
        PMF.pure (if (m, s) = (m0, 0) ∨ (m, s) = (m1, 1) then (1:Bit) else 0)))) 1
    = 1 / 2 := by
  have hne' : m1 ≠ m0 := hne.symm
  have hS : (S 0 st) 0 + (S 0 st) 1 = 1 := by
    have := (S 0 st).tsum_coe
    rw [tsum_fintype, Fin.sum_univ_two] at this; exact this
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Prod.mk.injEq, PMF.bind_map,
    bind_apply, uniformOfFintype_apply, Fintype.card_fin, Nat.cast_ofNat, Function.comp_apply,
    pure_apply, left_eq_ite_iff, not_or, not_and, one_ne_zero, imp_false, Classical.not_imp,
    Decidable.not_not, mul_ite, mul_one, mul_zero, tsum_fintype, Fin.sum_univ_two,
    not_true_eq_false, zero_ne_one, and_false, not_false_eq_true, implies_true, and_true,
    forall_const, Matrix.cons_val_zero, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_div, hne, hne', add_zero, zero_add]
  rw [← mul_add, hS, mul_one]

/-- For any simulator S, ps(B1(A1), S) ≤ 1/2,
    provided A1 only outputs pairs with m0 ≠ m1.
    Proof: ps = 1/2 exactly, shown by rewriting each term via tsum_congr. -/
lemma ps_le_half
    (A1 : PMF (M × M × St))
    (S : Bit → St → PMF Bit)
    (hne : ∀ m0 m1 st, A1 (m0, m1, st) ≠ 0 → m0 ≠ m1) :
    ps (B1 A1) S ≤ 1 / 2 := by
  have heq : ps (B1 A1) S = 1 / 2 := by
    rw [show ps (B1 A1) S = ∑' a : M × M × St, A1 a * (1/2) from ?_]
    · -- ∑' a, A1 a * (1/2) = 1/2
      rw [ENNReal.tsum_mul_right]
      simp [A1.tsum_coe]
    · -- each term equals A1 a * (1/2) by tsum_congr
      unfold ps B1
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Prod.mk.injEq, bind_assoc, one_div]
      simp only [Bind.bind]
      simp only [Fin.isValue, PMF.pure_bind, PMF.bind_map, bind_apply, uniformOfFintype_apply,
        Fintype.card_fin, Nat.cast_ofNat, Function.comp_apply, pure_apply, left_eq_ite_iff, not_or,
        not_and, one_ne_zero, imp_false, Classical.not_imp, Decidable.not_not, mul_ite, mul_one,
        mul_zero, tsum_fintype, Fin.sum_univ_two, not_true_eq_false, zero_ne_one, and_false,
        not_false_eq_true, implies_true, and_true, forall_const, Matrix.cons_val_zero, ↓reduceIte,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      apply tsum_congr
      intro ⟨m0, m1, st⟩
      by_cases hA1 : A1 (m0, m1, st) = 0
      · simp [hA1]
      · have hne' : m0 ≠ m1 := hne m0 m1 st hA1
        simp [hne', hne'.symm]
        congr
        rw [← mul_add]
        have : (2:ENNReal)⁻¹ * 1 = 2⁻¹ := by rw [mul_one]
        nth_rw 2 [← this]
        congr
        have hS : (S 0 st) 0 + (S 0 st) 1 = 1 := by
          have := (S 0 st).tsum_coe
          rw [tsum_fintype, Fin.sum_univ_two] at this; exact this
        exact hS
  rw [heq]

-- ============================================================
-- Section 4: Main theorem (Steps 1–5)
--
-- Step 1: by_contra + push_neg to obtain |p0 - p1| > ε
-- Step 2: apply guessing_lemma
-- Step 3: instantiate B1, B2 from Section 1
-- Step 4: apply pa_gt_half and ps_le_half from Sections 2–3
-- Step 5: derive |pa - ps| > ε/2, contradicting hss
-- ============================================================

/-- Theorem 3.1: (t, α, ε/2)-Semantic Security implies (t, ε)-Indistinguishability.
    If (Enc, Gen) is (t, α, ε/2)-semantically secure,
    then it is (t, ε)-indistinguishable. -/
theorem semantic_security_implies_indistinguishable
    (Enc : K → M → C) (Gen : PMF K)
    (t α : ℕ) (ε : ENNReal)
    (hss : SemanticallySecure (St := St) Enc Gen t α (ε / 2)) :
    Indistinguishable (St := St) Enc Gen t ε := by
  -- Step 1: Take any adversary (A1, A2) with combined complexity ≤ t
  --         and assume for contradiction that |p0 - p1| > ε
  intro A1 A2 tA1 tA2 htA
  by_contra h
  push_neg at h
  -- h : |(p0 ...).toReal - (p1 ...).toReal| > ε.toReal
  -- Steps 2–5: to be filled in
  sorry

end ComputationalSecurity
