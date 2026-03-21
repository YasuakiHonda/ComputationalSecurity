/-
  Formalization of Theorem 3.1 (textbook Chapter 3, pp.34-35):
  (t, α, ε/2)-Semantic Security implies (t, ε)-Indistinguishability.

  ----------------------------------------------------------------
  Proof structure (following textbook pp.34-35):
  ----------------------------------------------------------------
  Proof by contradiction. Assume Indistinguishable fails.

  Step 1: Obtain adversary (A1, A2) with |p0 - p1| > ε.
  Step 2: Apply pa_gt_half (which uses the Guessing Lemma internally):
            ∃ B2', pa(B1(A1), B2(B2')) > 1/2 * (1 + ε)
  Step 3: Apply SemanticallySecure to (B1 A1, B2 B2') to obtain simulator S.
  Step 4: Apply ps_le_half: ps(B1(A1), S) ≤ 1/2  (S has no info about b).
  Step 5: pa - ps > ε/2, contradicting SemanticallySecure.

  ----------------------------------------------------------------
  File organization:
  ----------------------------------------------------------------
    Section 1 (def B1, B2):       Construction of semantic security adversaries
    Section 2 (lemma pa_gt_half): pa lower bound via Guessing Lemma
      - X_dist, A'_wrap:          Helper definitions for guessing game bridge
      - abs_toReal_gt_iff_tsub:   |a-b|.toReal > ε → tsub disjunction (ε : NNReal)
      - pmf_bit_eval:             (p : PMF Bit) 1 = (p >>= fun a => pure (a==1)) true
      - p0_eq_Pr, p1_eq_Pr:       p0/p1 expressed via Pr and X_dist
      - pa_eq_guessing:           pa expressed as guessing probability
      - pa_gt_half:               main lemma
    Section 3 (lemmas):           ps upper bound
    Section 4 (theorem):          Main theorem assembling Steps 1–5

  Authors: Yasuaki Honda
-/

import ComputationalSecurity.Defs
import ComputationalSecurity.GuessingLemma

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

/-- Semantic security adversary B2 wrapping an indistinguishability adversary.
    B2 receives ciphertext c, h-value (ignored), and original state st,
    then calls the wrapped adversary with c and st directly. -/
noncomputable def B2 (A2 : C → St → PMF Bit) : C → Bit → St → PMF Bit :=
  fun c _ st => A2 c st

-- ============================================================
-- Section 2: pa lower bound (tool for Step 4a)
-- ============================================================

-- ------------------------------------------------------------
-- Helper definitions for bridging p0/p1 to the guessing game
-- ------------------------------------------------------------

/-- X_dist Enc Gen A1 b : PMF (C × St)
    Samples (m0, m1, st) from A1, a key k from Gen,
    and returns the ciphertext of the b-th message together with the state. -/
noncomputable def X_dist
    (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) : Bit → PMF (C × St) :=
  fun b => do
    let (m0, m1, st) ← A1
    let k ← Gen
    PMF.pure (Enc k (![m0, m1] b), st)

/-- A'_wrap A2 : (C × St) → PMF Bit
    Uncurries A2 : C → St → PMF Bit into a function on pairs,
    for use with guessing_lemma_abs whose adversary type is α → PMF Bit. -/
noncomputable def A'_wrap (A2 : C → St → PMF Bit) : (C × St) → PMF Bit :=
  fun (c, st) => A2 c st

-- ------------------------------------------------------------
-- Auxiliary lemmas for pa_gt_half
-- ------------------------------------------------------------

/-- If |a.toReal - b.toReal| > (ε : ℝ) (with a, b ≠ ⊤ and ε : NNReal),
    then b - a > (ε : ENNReal) or a - b > (ε : ENNReal) (ENNReal tsub).
    Since ε : NNReal, we have (ε : ENNReal) ≠ ⊤ automatically.
    The disjunction order matches guessing_lemma_abs:
      first (X 1 - X 0 > ε), then (X 0 - X 1 > ε). -/
lemma abs_toReal_gt_iff_tsub
    (a b : ENNReal) (ε : NNReal) (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h : |a.toReal - b.toReal| > (ε : ℝ)) :
    b - a > (ε : ENNReal) ∨ a - b > (ε : ENNReal) := by
  have hε : (ε : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  rcases le_or_gt 0 (a.toReal - b.toReal) with hab | hab
  · right  -- a ≥ b, show a - b > ε
    have hba : b ≤ a := by rw [← ENNReal.toReal_le_toReal hb ha]; linarith
    rw [show a - b > (ε : ENNReal) ↔ (ε : ENNReal) < a - b from Iff.rfl]
    rw [← ENNReal.toReal_lt_toReal hε (ENNReal.sub_ne_top ha)]
    rw [ENNReal.toReal_sub_of_le hba ha]
    rw [ENNReal.coe_toReal]
    rwa [abs_of_nonneg hab] at h
  · left   -- b > a, show b - a > ε
    have hba : a ≤ b := by rw [← ENNReal.toReal_le_toReal ha hb]; linarith
    rw [show b - a > (ε : ENNReal) ↔ (ε : ENNReal) < b - a from Iff.rfl]
    rw [← ENNReal.toReal_lt_toReal hε (ENNReal.sub_ne_top hb)]
    rw [ENNReal.toReal_sub_of_le hba hb]
    rw [ENNReal.coe_toReal]
    rw [abs_of_neg hab] at h; linarith

/-- Key bridge: evaluating a PMF Bit at 1 equals evaluating
    its image under (fun a => PMF.pure (a == 1)) at true.
    Used to relate p0/p1 (which evaluate A2's output PMF at 1)
    to Pr (which uses PMF.pure (a == 1) evaluated at true). -/
private lemma pmf_bit_eval (p : PMF Bit) :
    p 1 = (p.bind fun a => PMF.pure (a == 1)) true := by
  simp [PMF.bind_apply, PMF.pure_apply, tsum_fintype]

/-- p0 Enc Gen A1 A2 equals the probability that A2 outputs 1
    when the input is sampled from X_dist Enc Gen A1 0.
    This bridges the Indistinguishability definition to the Guessing Lemma format. -/
lemma p0_eq_Pr
    (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit) :
    p0 Enc Gen A1 A2 =
    Pr (do let x ← X_dist Enc Gen A1 0; let a ← A'_wrap A2 x; PMF.pure (a == 1)) := by
  simp only [p0, Pr, X_dist, A'_wrap,
    Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_zero, bind_assoc]
  simp only [Bind.bind, PMF.pure_bind]
  simp_rw [PMF.bind_apply, pmf_bit_eval, PMF.bind_apply]

/-- p1 Enc Gen A1 A2 equals the probability that A2 outputs 1
    when the input is sampled from X_dist Enc Gen A1 1.
    This bridges the Indistinguishability definition to the Guessing Lemma format. -/
lemma p1_eq_Pr
    (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit) :
    p1 Enc Gen A1 A2 =
    Pr (do let x ← X_dist Enc Gen A1 1; let a ← A'_wrap A2 x; PMF.pure (a == 1)) := by
  simp only [p1, Pr, X_dist, A'_wrap,
    Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, bind_assoc]
  simp only [Bind.bind, PMF.pure_bind]
  simp_rw [PMF.bind_apply, pmf_bit_eval, PMF.bind_apply]

/-- pa Enc Gen (B1 A1) (B2 A2') equals the guessing probability in Lemma 3.1.
    Key identity: the semantic security game with (B1, B2) is exactly the
    guessing game where b is chosen uniformly, mb is encrypted, and A2'
    tries to guess b from the ciphertext.
    The hypothesis hne (m0 ≠ m1 for all support points of A1) is needed to
    simplify the relation R(![m0,m1][b], a) = (a == b). -/
lemma pa_eq_guessing
    (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) (A2' : C → St → PMF Bit)
    (hne : ∀ m0 m1 st, A1 (m0, m1, st) ≠ 0 → m0 ≠ m1) :
    pa Enc Gen (B1 A1) (B2 A2') =
    Pr (do
      let b ← randomBit
      let x ← X_dist Enc Gen A1 b
      let a ← A'_wrap A2' x
      PMF.pure (a == b)) := by
  simp only [pa, B1, B2, X_dist, A'_wrap, Pr, Bind.bind]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Prod.mk.injEq, bind_bind,
    PMF.pure_bind, PMF.bind_map, bind_apply, uniformOfFintype_apply, Fintype.card_fin,
    Nat.cast_ofNat, Function.comp_apply, pure_apply, left_eq_ite_iff, not_or, not_and, one_ne_zero,
    imp_false, Classical.not_imp, Decidable.not_not, mul_ite, mul_one, mul_zero, tsum_fintype,
    Fin.sum_univ_two, not_true_eq_false, zero_ne_one, and_false, not_false_eq_true, implies_true,
    and_true, forall_const, Matrix.cons_val_zero, ↓reduceIte, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Bool.true_eq, beq_iff_eq, Finset.sum_ite_eq', Finset.mem_univ]
  -- Use hne to simplify the if-terms: since m0 ≠ m1 on the support of A1,
  -- R(![m0,m1][b], a) simplifies to (a == b).
  have key : ∀ a : M × M × St, A1 a *
      (2⁻¹ * ∑' k, Gen k * ((A2' (Enc k a.1) a.2.2) 0 +
          if a.1 = a.2.1 then (A2' (Enc k a.1) a.2.2) 1 else 0) +
       2⁻¹ * ∑' k, Gen k * ((if a.2.1 = a.1 then (A2' (Enc k a.2.1) a.2.2) 0 else 0) +
          (A2' (Enc k a.2.1) a.2.2) 1))
    = A1 a * (2⁻¹ * ∑' k, Gen k * (A2' (Enc k a.1) a.2.2) 0
            + 2⁻¹ * ∑' k, Gen k * (A2' (Enc k a.2.1) a.2.2) 1) := by
    intro ⟨m0, m1, st⟩
    by_cases hA1 : A1 (m0, m1, st) = 0
    · simp [hA1]
    · have hne' := hne m0 m1 st hA1
      simp [hne', hne'.symm]
  simp_rw [key]
  simp_rw [mul_add, mul_left_comm (A1 _) 2⁻¹, ENNReal.tsum_add,
           ENNReal.tsum_mul_left]


/-- If |p0 - p1| > ε (in real-valued sense, ε : NNReal),
    then there exists B2' such that pa(Enc, Gen, B1(A1), B2(B2')) > 1/2 * (1 + ε).
    The witness B2' is either A2 (case 1) or flipA A2 (case 2),
    as determined by the Guessing Lemma (Lemma 3.1).
    Proof:
      A. Convert |p0 - p1| > ε (real) to ENNReal tsub disjunction.
      B. Rewrite p0, p1 via p0_eq_Pr, p1_eq_Pr.
      C. Apply guessing_lemma_abs to obtain ∃ B : (C × St) → PMF Bit.
      D. Uncurry B into B2' : C → St → PMF Bit.
      E. Rewrite pa via pa_eq_guessing and conclude. -/
lemma pa_gt_half
    (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit)
    (ε : NNReal)
    (hne : ∀ m0 m1 st, A1 (m0, m1, st) ≠ 0 → m0 ≠ m1)
    (h : |(p0 Enc Gen A1 A2).toReal - (p1 Enc Gen A1 A2).toReal| > (ε : ℝ)) :
    ∃ B2' : C → St → PMF Bit,
      pa Enc Gen (B1 A1) (B2 B2') > 1 / 2 * (1 + (ε : ENNReal)) := by
  -- Step A: convert real inequality to ENNReal tsub disjunction
  have hp0_ne_top : p0 Enc Gen A1 A2 ≠ ⊤ := PMF.apply_ne_top _ _
  have hp1_ne_top : p1 Enc Gen A1 A2 ≠ ⊤ := PMF.apply_ne_top _ _
  have hOR := abs_toReal_gt_iff_tsub
    (p0 Enc Gen A1 A2) (p1 Enc Gen A1 A2) ε hp0_ne_top hp1_ne_top h
  -- Step B: rewrite p0, p1 as Pr over X_dist
  rw [p0_eq_Pr, p1_eq_Pr] at hOR
  -- Step C: apply guessing_lemma_abs to get ∃ B : (C × St) → PMF Bit
  obtain ⟨B, hB⟩ := guessing_lemma_abs (A'_wrap A2) (X_dist Enc Gen A1) (ε : ENNReal) hOR
  -- Step D: uncurry B into B2' : C → St → PMF Bit
  refine ⟨fun c st => B (c, st), ?_⟩
  -- Step E: rewrite pa via pa_eq_guessing, then match with hB
  rw [pa_eq_guessing (hne := hne)]
  simp only [A'_wrap]
  exact hB

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
    · rw [ENNReal.tsum_mul_right]; simp [A1.tsum_coe]
    · unfold ps B1
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
        nth_rw 2 [← this]; congr
        have hS : (S 0 st) 0 + (S 0 st) 1 = 1 := by
          have := (S 0 st).tsum_coe
          rw [tsum_fintype, Fin.sum_univ_two] at this; exact this
        exact hS
  rw [heq]

-- ============================================================
-- Section 4: Main theorem (Steps 1–5)
--
-- Step 1: by_contra + push_neg to obtain |p0 - p1| > ε
-- Step 2: apply pa_gt_half to obtain ∃ B2' with pa > 1/2*(1+ε)
-- Step 3: apply SemanticallySecure to (B1 A1, B2 B2') to obtain simulator S
-- Step 4: apply ps_le_half to obtain ps ≤ 1/2
-- Step 5: derive pa - ps > ε/2, contradicting hss_ineq
-- ============================================================

/-- Theorem 3.1: (t, α, ε/2)-Semantic Security implies (t, ε)-Indistinguishability.
    If (Enc, Gen) is (t, α, ε/2)-semantically secure,
    then it is (t, ε)-indistinguishable. -/
theorem semantic_security_implies_indistinguishable
    (Enc : K → M → C) (Gen : PMF K)
    (t α : ℕ) (ε : NNReal)
    (hss : SemanticallySecure (St := St) Enc Gen t α (ε / 2)) :
    Indistinguishable (St := St) Enc Gen t ε := by
  -- intro now takes hne directly from the Indistinguishable definition
  intro A1 hne A2 tA1 tA2 htA
  by_contra h
  push_neg at h
  -- h : |(p0 Enc Gen A1 A2).toReal - (p1 Enc Gen A1 A2).toReal| > (ε : ℝ)
  -- hne : ∀ m0 m1 st, A1 (m0, m1, st) > 0 → m0 ≠ m1

  -- Step 2: Apply pa_gt_half to obtain B2' with pa(B1 A1, B2 B2') > 1/2 * (1 + ε)
  have hne' : ∀ m0 m1 st, A1 (m0, m1, st) ≠ 0 → m0 ≠ m1 :=
    fun m0 m1 st h => hne m0 m1 st (pos_iff_ne_zero.mpr h)
  obtain ⟨B2', hpa⟩ := pa_gt_half Enc Gen A1 A2 ε hne' h

  -- Step 3: Apply SemanticallySecure to (B1 A1, B2 B2') to obtain simulator S
  obtain ⟨S, _tS, _htS, hss_ineq⟩ := hss (B1 A1) (B2 B2') tA1 tA2 htA
  -- hss_ineq : |(pa Enc Gen (B1 A1) (B2 B2')).toReal - (ps (B1 A1) S).toReal| ≤ (ε/2 : ℝ)

  -- Step 4: ps ≤ 1/2 for any simulator S (S receives only h(m)=0 and st, no info about b)
  -- hne gives A1 (m0,m1,st) > 0 → m0 ≠ m1; ps_le_half needs ≠ 0, equivalent via pos_iff_ne_zero
  have hps : ps (B1 A1) S ≤ 1 / 2 := ps_le_half A1 S hne'

  -- Step 5: Derive contradiction.
  -- pa > 1/2*(1+ε) and ps ≤ 1/2, so pa - ps > ε/2,
  -- but hss_ineq says |pa - ps| ≤ ε/2.
  have hgap : (pa Enc Gen (B1 A1) (B2 B2')).toReal - (ps (B1 A1) S).toReal > (ε / 2 : ℝ) := by
    -- hpa_real: hpa (ENNReal inequality) → pa.toReal > (1/2*(1+ε)).toReal
    have hpa_real : (pa Enc Gen (B1 A1) (B2 B2')).toReal >
        (1 / 2 * (1 + (ε : ENNReal))).toReal := by
      have hrhs_fin : 1 / 2 * (1 + (ε : ENNReal)) ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num)
          (ENNReal.add_ne_top.mpr ⟨by norm_num, ENNReal.coe_ne_top⟩)
      exact (ENNReal.toReal_lt_toReal hrhs_fin (PMF.apply_ne_top _ _)).mpr hpa
    -- hrhs_eq: (1/2*(1+ε)).toReal = 1/2 + ε/2, by simp + ring
    have hrhs_eq : (1 / 2 * (1 + (ε : ENNReal))).toReal = 1/2 + (ε : ℝ)/2 := by
      simp [ENNReal.toReal_mul, ENNReal.toReal_add, ENNReal.coe_toReal]; ring
    -- hps_real: ps.toReal ≤ 1/2, from hps via ENNReal.toReal_le_toReal
    have hps_real : (ps (B1 A1) S).toReal ≤ 1/2 := by
      have h1 : ps (B1 A1) S ≠ ⊤ := PMF.apply_ne_top _ _
      have h2 : (1/2 : ENNReal) ≠ ⊤ := by norm_num
      have := (ENNReal.toReal_le_toReal h1 h2).mpr hps
      simp at this; linarith
    linarith
  -- habs: pa - ps > ε/2 implies |pa - ps| > ε/2, since pa - ps > 0
  have habs : |(pa Enc Gen (B1 A1) (B2 B2')).toReal - (ps (B1 A1) S).toReal| > (ε / 2 : ℝ) := by
    have hnn : (0 : ℝ) ≤ (ε / 2 : ℝ) := by positivity
    have hpos : (pa Enc Gen (B1 A1) (B2 B2')).toReal - (ps (B1 A1) S).toReal > 0 :=
      lt_of_le_of_lt hnn hgap
    rwa [abs_of_pos hpos]
  -- Contradiction: |pa - ps| > ε/2 but hss_ineq says |pa - ps| ≤ ε/2
  have hss_ineq' : |(pa Enc Gen (B1 A1) (B2 B2')).toReal - (ps (B1 A1) S).toReal|
      ≤ (ε : ℝ) / 2 := by
    have : ((ε / 2 : NNReal) : ℝ) = (ε : ℝ) / 2 := Real.ext_cauchy rfl
    linarith [hss_ineq]
  linarith [hss_ineq']

end ComputationalSecurity
