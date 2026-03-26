/-
  Formalization of the Equivalence between Semantic Security and Indistinguishability.
  Reference: Textbook Chapter 3, pp. 34-37.

  This file proves Theorem 3.1: (t, α, ε/2)-Semantic Security implies (t, ε)-Indistinguishability.

  Logic:
  The proof follows a direct "Advantage Equality" approach rather than the traditional
  reduction through a guessing lemma. It establishes the signed identity:
    pa - ps = 1/2 * (p1 - p0)
  and hence the absolute-value version:
    |pa - ps| = 1/2 * |p1 - p0|
  This equality is proved by decomposing the global probabilities into local success
  probabilities for each message pair (m0, m1) in the support of the message distribution.
  Crucially, this approach handles the case where m0 = m1 naturally (both sides become zero),
  eliminating the need for the distinctness constraint (hne) on the adversary's output.

  This file is organized into five sections:
    Section 1: Construction of adversaries B1 and B2 for the semantic security game.
    Section 2: Local probability definitions (local_pa, local_ps, p_local).
    Section 3: Evaluation lemmas (local_pa_eval, local_ps_eval).
    Section 4: Global bridging lemmas relating pa, ps, p0, p1 to their local summations.
    Section 5: Advantage equality (signed and absolute) and the final theorem.

  Authors: Yasuaki Honda, assisted by AI
-/

import ComputationalSecurity.Defs
import ComputationalSecurity.GuessingLemma

namespace ComputationalSecurity

open PMF

-- Base variable declaration: used throughout Sections 1-4.
-- [Fintype M], [Fintype C], [Fintype St] are added before Section 5,
-- where tsum_fintype is needed for the global advantage equality.
variable {M C K St : Type} [DecidableEq M]

-- ============================================================
-- Section 1: Construction of (B1, B2)
-- ============================================================

/-- Semantic security adversary B1 constructed from an indistinguishability adversary A1.
    It picks m0 or m1 with probability 1/2 and defines a relation R that is satisfied
    only if the adversary correctly identifies which message was chosen.
    The partial information function h is set to the constant zero function,
    providing no side information to A2 beyond what the ciphertext reveals. -/
noncomputable def B1 (A1 : PMF (M × M × St)) :
    PMF (PMF M × (M → Bit) × (M → Bit → Bit) × St) := do
  let (m0, m1, st) ← A1
  let mDist : PMF M := randomBit.map ![m0, m1]
  let h : M → Bit := fun _ => 0
  let R : M → Bit → Bit := fun m a => if (m, a) = (m0, 0) ∨ (m, a) = (m1, 1) then 1 else 0
  PMF.pure (mDist, h, R, st)

/-- Semantic security adversary B2 wrapping an indistinguishability adversary A2.
    It simply passes the ciphertext and state to A2, ignoring the side information h. -/
noncomputable def B2 (A2 : C → St → PMF Bit) : C → Bit → St → PMF Bit :=
  fun c _ st => A2 c st

-- ============================================================
-- Section 2: Local Probabilities
-- ============================================================

/-- Local probability that A2 outputs 1 given message m is encrypted under a random key. -/
noncomputable def p_local (Enc : K → M → C) (Gen : PMF K)
                          (A2 : C → St → PMF Bit) (m : M) (st : St) : ENNReal :=
  (Gen.bind fun k ↦ A2 (Enc k m) st) 1

/-- Success probability of the Semantic Security REAL experiment for a fixed point (m0, m1, st).
    Corresponds to the probability that R(m, a) = 1 in the real experiment. -/
noncomputable def local_pa (Enc : K → M → C) (Gen : PMF K)
    (A2 : C → St → PMF Bit) (m0 m1 : M) (st : St) : ENNReal :=
  ((randomBit.map ![m0, m1]).bind (fun m =>
      Gen.bind (fun k =>
        (A2 (Enc k m) st).bind (fun a =>
          PMF.pure (if (m, a) = (m0, 0) ∨ (m, a) = (m1, 1) then (1 : Bit) else 0))))) 1

/-- Success probability of the Semantic Security IDEAL experiment for a fixed point (m0, m1, st).
    Corresponds to the probability that R(m, s) = 1 in the ideal experiment with a simulator. -/
noncomputable def local_ps (S : Bit → St → PMF Bit) (m0 m1 : M) (st : St) : ENNReal :=
  ((randomBit.map ![m0, m1]).bind (fun m ↦
      (S 0 st).bind (fun s ↦
        PMF.pure (if (m, s) = (m0, 0) ∨ (m, s) = (m1, 1) then (1 : Bit) else 0)))) 1

-- ============================================================
-- Section 3: Evaluation Lemmas
-- ============================================================

/-- Evaluation of local_ps. If m0 = m1, success is certain (1).
    Otherwise, success probability is exactly 1/2: S only observes h(m) = 0 and st,
    and has no information about which message was actually chosen. -/
lemma local_ps_eval (m0 m1 : M) (st : St) (S : Bit → St → PMF Bit) :
    local_ps S m0 m1 st = if m0 = m1 then 1 else 1 / 2 := by
  unfold local_ps
  split_ifs with hm01
  · -- Case m0 = m1: The relation R is always satisfied
    simp only [hm01]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Prod.mk.injEq, PMF.bind_map,
      bind_apply, uniformOfFintype_apply, Fintype.card_fin, Nat.cast_ofNat, Function.comp_apply,
      pure_apply, left_eq_ite_iff, not_or, not_and, one_ne_zero, imp_false, Classical.not_imp,
      Decidable.not_not, mul_ite, mul_one, mul_zero, tsum_fintype, Fin.sum_univ_two,
      not_true_eq_false, zero_ne_one, and_false, not_false_eq_true, implies_true, and_true,
      forall_const, Matrix.cons_val_zero, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hS : (S 0 st) 0 + (S 0 st) 1 = 1 := by
      have := (S 0 st).tsum_coe
      rw [tsum_fintype, Fin.sum_univ_two] at this; exact this
    rw [hS, mul_one]
    exact ENNReal.inv_two_add_inv_two
  · -- Case m0 ≠ m1: Standard semantic security argument
    have inner_eq_half :
        ((randomBit.map ![m0, m1]).bind (fun m =>
          (S 0 st).bind (fun s =>
            PMF.pure (if (m, s) = (m0, 0) ∨ (m, s) = (m1, 1) then (1:Bit) else 0)))) 1
        = 1 / 2 := by
      push_neg at hm01
      have hne' : m1 ≠ m0 := hm01.symm
      have hS : (S 0 st) 0 + (S 0 st) 1 = 1 := by
        have := (S 0 st).tsum_coe
        rw [tsum_fintype, Fin.sum_univ_two] at this; exact this
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Prod.mk.injEq, PMF.bind_map,
        bind_apply, uniformOfFintype_apply, Fintype.card_fin, Nat.cast_ofNat, Function.comp_apply,
        pure_apply, left_eq_ite_iff, not_or, not_and, one_ne_zero, imp_false, Classical.not_imp,
        Decidable.not_not, mul_ite, mul_one, mul_zero, tsum_fintype, Fin.sum_univ_two,
        not_true_eq_false, zero_ne_one, and_false, not_false_eq_true, implies_true, and_true,
        forall_const, Matrix.cons_val_zero, ↓reduceIte, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, one_div, hm01, hne', add_zero, zero_add]
      rw [← mul_add, hS, mul_one]
    exact inner_eq_half

/-- Evaluation of local_pa. If m0 = m1, success is certain (1).
    Otherwise, it is 1/2 * (Pr[A2=0|m0] + Pr[A2=1|m1]). -/
lemma local_pa_eval (Enc : K → M → C) (Gen : PMF K) (A2 : C → St → PMF Bit)
    (m0 m1 : M) (st : St) :
    local_pa Enc Gen A2 m0 m1 st = if m0 = m1 then 1
      else 1 / 2 * (1 - (Gen.bind (fun k => A2 (Enc k m0) st)) 1)
         + 1 / 2 * (Gen.bind (fun k => A2 (Enc k m1) st)) 1 := by
  -- Auxiliary lemma: probabilities of bit outputs sum to 1
  have hS (k : K) (m : M): (A2 (Enc k m) st) 0 + (A2 (Enc k m) st) 1 = 1 := by
    have := (A2 (Enc k m) st).tsum_coe
    rw [tsum_fintype, Fin.sum_univ_two] at this; exact this
  unfold local_pa
  split_ifs with hm01
  · -- Case m0 = m1
    simp only [hm01]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Prod.mk.injEq, PMF.bind_map,
      bind_apply, uniformOfFintype_apply, Fintype.card_fin, Nat.cast_ofNat, Function.comp_apply,
      pure_apply, left_eq_ite_iff, not_or, not_and, one_ne_zero, imp_false, Classical.not_imp,
      Decidable.not_not, mul_ite, mul_one, mul_zero, tsum_bit]
    simp only [Fin.isValue, Matrix.cons_val_zero, not_true_eq_false, imp_false, zero_ne_one,
      and_false, imp_self, ↓reduceIte, not_false_eq_true, and_self,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [← two_mul, ENNReal.mul_inv_cancel_left (by norm_num : (2:ENNReal) ≠ 0) (by norm_num)]
    conv_lhs =>
      arg 1; ext k; arg 2
      apply hS
    simp only [mul_one]
    exact tsum_coe Gen
  · -- Case m0 ≠ m1
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Prod.mk.injEq, PMF.bind_map,
      bind_apply, uniformOfFintype_apply, Fintype.card_fin, Nat.cast_ofNat, Function.comp_apply,
      pure_apply, left_eq_ite_iff, not_or, not_and, one_ne_zero, imp_false, Classical.not_imp,
      Decidable.not_not, mul_ite, mul_one, mul_zero, tsum_bit]
    simp only [Fin.isValue, Matrix.cons_val_zero, not_true_eq_false, imp_false, zero_ne_one,
      and_false, imp_self, ↓reduceIte, not_false_eq_true, and_true, forall_const,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Decidable.not_not, implies_true, and_self,
      one_div]
    push_neg at hm01
    simp only [hm01, hm01.symm, if_false, add_zero, zero_add]
    congr
    apply ENNReal.eq_sub_of_add_eq
    · apply PMF.tsum_mul_ne_top
      exact fun x ↦ coe_le_one (A2 (Enc x m0) st) 1
    · rw [← ENNReal.tsum_add]
      conv_lhs => arg 1; ext k; rw [← mul_add]; arg 2; rw [hS]
      conv_lhs => arg 1; ext k; rw [mul_one]
      rw [tsum_coe]

-- ============================================================
-- Section 4: Global Bridging Lemmas
-- ============================================================

/-- Bridge between the global pa definition and the local success probability summation. -/
lemma pa_eq_tsum (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit) :
    pa Enc Gen (B1 A1) (B2 A2) = ∑' x, A1 x * local_pa Enc Gen A2 x.1 x.2.1 x.2.2 := by
  unfold pa B1 B2
  -- Outer bind on A1 is converted to tsum via bind_apply
  simp only [bind_assoc]
  apply tsum_congr
  intro ⟨m0, m1, st⟩
  unfold local_pa
  congr 1
  congr 1
  simp (config := { zeta := true }) only []
  apply PMF.ext; intro a'
  simp only [bind_apply, pure_apply]
  simp only [Bind.bind]
  rw [bind_apply]
  simp only [pure_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Prod.mk.injEq, bind_apply, pure_apply,
    mul_ite, mul_one, mul_zero, tsum_fintype, Fin.sum_univ_two, ite_mul, one_mul, zero_mul,
    tsum_ite_eq, map_apply, uniformOfFintype_apply, Fintype.card_fin, Nat.cast_ofNat,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, and_true, zero_ne_one,
    and_false, or_false, one_ne_zero, false_or]

/-- Bridge between the global ps definition and the local simulator success summation. -/
lemma ps_eq_tsum (A1 : PMF (M × M × St)) (S : Bit → St → PMF Bit) :
    ps (B1 A1) S = ∑' x, A1 x * local_ps S x.1 x.2.1 x.2.2 := by
  unfold ps B1
  simp only [bind_assoc]
  apply tsum_congr; intro ⟨m0, m1, st⟩
  congr 2
  apply PMF.ext; intro a'
  rw [bind_apply]
  simp only [bind_apply, pure_apply, Bind.bind, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    Prod.mk.injEq, mul_ite, mul_one, mul_zero, tsum_fintype, Fin.sum_univ_two, ite_mul, one_mul,
    zero_mul, tsum_ite_eq, map_apply, uniformOfFintype_apply, Fintype.card_fin, Nat.cast_ofNat,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, and_true, zero_ne_one,
    and_false, or_false, one_ne_zero, false_or]

/-- Bridge between global p0 and local p_local at m0. -/
lemma p0_eq_tsum (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit) :
    p0 Enc Gen A1 A2 = ∑' x, A1 x * p_local Enc Gen A2 x.1 x.2.2 := by
  unfold p0 p_local; apply tsum_congr; intro ⟨m0, m1, st⟩; rw [bind_apply]; congr

/-- Bridge between global p1 and local p_local at m1. -/
lemma p1_eq_tsum (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit) :
    p1 Enc Gen A1 A2 = ∑' x, A1 x * p_local Enc Gen A2 x.2.1 x.2.2 := by
  unfold p1 p_local; apply tsum_congr; intro ⟨m0, m1, st⟩; rw [bind_apply]; congr

-- ============================================================
-- Section 5: Advantage Equality and Final Theorem
-- [Fintype M], [Fintype C], [Fintype St] are introduced here,
-- as they are first needed by pa_sub_ps_eq_half_dist (via tsum_fintype).
-- ============================================================

variable [Fintype M] [Fintype C] [Fintype St]

/-- Identity relating Semantic Security advantage and Indistinguishability advantage at each point.
    Here p_local Enc Gen A2 m st denotes Pr[A2 outputs 1 | m is encrypted].
    If m0 = m1, both local_pa and local_ps equal 1, so the difference is 0.
    If m0 ≠ m1, local_pa = 1/2*(1 - p_local m0) + 1/2*p_local m1 and local_ps = 1/2,
    giving local_pa - local_ps = 1/2*(p_local m1 - p_local m0). -/
lemma local_diff_eq (Enc : K → M → C) (Gen : PMF K)
    (A2 : C → St → PMF Bit) (S : Bit → St → PMF Bit) (m0 m1 : M) (st : St) :
    (local_pa Enc Gen A2 m0 m1 st).toReal - (local_ps S m0 m1 st).toReal =
    1 / 2 * (p_local Enc Gen A2 m1 st).toReal - 1 / 2 * (p_local Enc Gen A2 m0 st).toReal := by
  by_cases hm01 : m1 = m0
  · -- Case: m0 = m1. Advantage is zero on both sides.
    subst hm01
    have pa_1 : local_pa Enc Gen A2 m1 m1 st = 1 := by rw [local_pa_eval]; simp
    have ps_1 : local_ps S m1 m1 st = 1 := by rw [local_ps_eval]; simp
    simp [pa_1, ps_1]
  · -- Case: m0 ≠ m1.
    have h_pa := local_pa_eval Enc Gen A2 m0 m1 st
    have h_ps := local_ps_eval m0 m1 st S
    push_neg at hm01
    simp [hm01.symm] at h_pa h_ps
    rw [h_pa, h_ps]
    unfold p_local
    rw [ENNReal.toReal_add]
    · simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat, Fin.isValue,
        one_div, bind_apply]
      rw [ENNReal.toReal_sub_of_le]
      · rw [ENNReal.toReal_one]; ring
      · apply PMF.tsum_mul_le_one; exact fun x ↦ coe_le_one (A2 (Enc x m0) st) 1
      · norm_num
    · apply ENNReal.mul_ne_top (by norm_num); apply ENNReal.sub_ne_top (by norm_num)
    · apply ENNReal.mul_ne_top (by norm_num); apply PMF.tsum_mul_ne_top
      exact fun x ↦ coe_le_one (A2 (Enc x m1) st) 1

/-- The Global Advantage Equality: (pa - ps) = 1/2 * (p1 - p0).
    Proved by summing local_diff_eq over the support of A1. -/
lemma pa_sub_ps_eq_half_dist (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit) (S : Bit → St → PMF Bit) :
    (pa Enc Gen (B1 A1) (B2 A2)).toReal - (ps (B1 A1) S).toReal =
    1 / 2 * ((p1 Enc Gen A1 A2).toReal - (p0 Enc Gen A1 A2).toReal) := by
  -- 1. Decompose global definitions into summations
  rw [pa_eq_tsum, ps_eq_tsum, p0_eq_tsum, p1_eq_tsum]
  -- 2. Convert ENNReal summations to finite Real summations
  rw [tsum_fintype,tsum_fintype,tsum_fintype,tsum_fintype]
  rw [ENNReal.toReal_sum,ENNReal.toReal_sum,ENNReal.toReal_sum,ENNReal.toReal_sum]
  · -- 3. Consolidate sums and apply the local difference identity
    simp only [ENNReal.toReal_mul]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    conv_lhs => arg 2; ext a; arg 2; rw [local_diff_eq]
    conv_lhs => arg 2; ext a; arg 2; rw [one_div, ← mul_sub]
    conv_lhs => arg 2; ext a; rw [mul_comm, mul_assoc]
    rw [← Finset.mul_sum, one_div, ← Finset.sum_sub_distrib]
    congr 2; ext i; rw [mul_comm, mul_sub]
  -- Handle all ne_top side goals for the sum conversion
  any_goals intro _ _; apply ENNReal.mul_ne_top <;> apply PMF.apply_ne_top

/-- Absolute value version of the advantage equality. -/
lemma abs_pa_sub_ps_eq_half_dist (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit) (S : Bit → St → PMF Bit) :
    |(pa Enc Gen (B1 A1) (B2 A2)).toReal - (ps (B1 A1) S).toReal| =
    1 / 2 * |(p1 Enc Gen A1 A2).toReal - (p0 Enc Gen A1 A2).toReal| := by
  rw [pa_sub_ps_eq_half_dist]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]

/-- Theorem 3.1: (t, α, ε/2)-Semantic Security implies (t, ε)-Indistinguishability.
    Final proof assembling the Advantage Equality with the definition of Semantic Security.

    Parameters:
    - t  : complexity budget for the indistinguishability adversary (A1, A2)
    - α  : complexity budget for key generation and encryption (tGen + tEnc)
    - ε  : distinguishing advantage bound (the hypothesis gives ε/2 for semantic security)

    The adversaries B1, B2 constructed in Section 1 serve as the semantic security
    adversary. The Advantage Equality (abs_pa_sub_ps_eq_half_dist) converts the
    semantic security bound ε/2 into the indistinguishability bound ε. -/
theorem semantic_security_implies_indistinguishable
    (Enc : K → M → C) (Gen : PMF K) (t α : ℕ) (ε : NNReal)
    (hss : SemanticallySecure (St := St) Enc Gen t α (ε / 2)) :
    Indistinguishable (St := St) Enc Gen t ε := by
  -- Obtain adversary A1, A2
  intro A1 A2 tA1 tA2 htA
  -- Apply Semantic Security to obtain simulator S
  obtain ⟨S, _, _, h_sem⟩ := hss (B1 A1) (B2 A2) tA1 tA2 htA
  -- Use Advantage Equality to relate the advantages
  rw [abs_pa_sub_ps_eq_half_dist, abs_sub_comm] at h_sem
  -- Simplify the inequality (1/2 * X ≤ ε/2  =>  X ≤ ε)
  simp [NNReal.coe_div] at h_sem
  linarith

end ComputationalSecurity
