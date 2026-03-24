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
    Section 1 (def B1, B2):         Construction of semantic security adversaries
    Section 2 (lemmas):             pa lower bound via Guessing Lemma
      - X_dist, A'_wrap:            Helper definitions for guessing game bridge
      - abs_toReal_gt_iff_tsub:     |a-b|.toReal > ε → tsub disjunction (ε : NNReal)
      - pmf_bit_eval:               (p : PMF Bit) 1 = (p >>= fun a => pure (a==1)) true
      - p0_eq_Pr, p1_eq_Pr:         p0/p1 expressed via Pr and X_dist
      - pa_eq_guessing:             pa expressed as guessing probability (requires hne)
      - pa_gt_half:                 pa lower bound main lemma
    Section 3 (lemmas):             ps upper bound
      - inner_eq_half:              per-point probability equals 1/2
      - ps_le_half:                 ps ≤ 1/2 for any simulator
    Section 4 (theorem):            Main theorem assembling Steps 1–5

  Authors: Yasuaki Honda
-/

import ComputationalSecurity.Defs
import ComputationalSecurity.GuessingLemma

namespace ComputationalSecurity

open PMF

variable {M C K St : Type} [DecidableEq M] [Fintype M] [Fintype C] [Fintype St]

-- ============================================================
-- Section 1: Construction of (B1, B2) (used in Step 3)
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
    then calls the wrapped adversary A2 with c and st directly. -/
noncomputable def B2 (A2 : C → St → PMF Bit) : C → Bit → St → PMF Bit :=
  fun c _ st => A2 c st

-- ============================================================
-- Section 2: pa lower bound (used in Step 2)
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
-- Auxiliary lemmas
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


-- ============================================================
-- Section 3: ps upper bound (used in Step 4)
-- ============================================================








/-- For fixed (m0, m1) with m0 ≠ m1, the probability that simulator S
    satisfies R(m, s) = 1 when m is drawn uniformly from {m0, m1} equals 1/2.
    This is a standalone auxiliary lemma capturing the per-point calculation
    underlying ps_le_half.
    Since S receives only h(m) = 0 and st (no ciphertext), its output s is
    independent of which of m0 or m1 was chosen. The relation R satisfies
    R(m0, s) = 1 iff s = 0, and R(m1, s) = 1 iff s = 1,
    so success probability equals (S 0 st) 0 * 1/2 + (S 0 st) 1 * 1/2 = 1/2. -/
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


-- 局所的な ps (シミュレータの成功確率)
noncomputable def local_ps (S : Bit → St → PMF Bit) (m0 m1 : M) (st : St) : ENNReal :=
  ((randomBit.map ![m0, m1]).bind (fun m ↦
      (S 0 st).bind (fun s ↦
        PMF.pure (if (m, s) = (m0, 0) ∨ (m, s) = (m1, 1) then (1 : Bit) else 0)))) 1

/-- Local success probability of the simulator S for a fixed pair (m0, m1) and state st.
This lemma removes the `m0 ≠ m1` requirement from the hypotheses.

If m0 = m1, the relation R(m, s) is satisfied for any output s ∈ {0, 1},
resulting in a success probability of 1.
If m0 ≠ m1, S has no information about which message was encrypted (since h(m)=0),
resulting in a success probability of 1/2.
-/
lemma local_ps_eval (m0 m1 : M) (st : St) (S : Bit → St → PMF Bit) :
    local_ps S m0 m1 st = if m0 = m1 then 1 else 1 / 2 := by
  unfold local_ps
  split_ifs with hm01
  · simp only [hm01]
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
  · exact inner_eq_half m0 m1 st S (by simp [hm01])

-- 局所的な pa (意味的安全性の REAL 実験における成功確率)
-- あなたが local_pa_eval で証明した左辺の式そのものです
noncomputable def local_pa (Enc : K → M → C) (Gen : PMF K)
    (A2 : C → St → PMF Bit) (m0 m1 : M) (st : St) : ENNReal :=
  ((randomBit.map ![m0, m1]).bind (fun m =>
      Gen.bind (fun k =>
        (A2 (Enc k m) st).bind (fun a =>
          PMF.pure (if (m, a) = (m0, 0) ∨ (m, a) = (m1, 1) then (1 : Bit) else 0))))) 1

lemma local_pa_eval (Enc : K → M → C) (Gen : PMF K) (A2 : C → St → PMF Bit) (m0 m1 : M) (st : St) :
    local_pa Enc Gen A2 m0 m1 st = if m0 = m1 then 1
      else 1 / 2 * (1 - (Gen.bind (fun k => A2 (Enc k m0) st)) 1)
         + 1 / 2 * (Gen.bind (fun k => A2 (Enc k m1) st)) 1 := by
  -- 局所的な A2 の 1 出力確率を定義
  have p0_val := (Gen.bind (fun k => A2 (Enc k m0) st)) 1
  have p1_val := (Gen.bind (fun k => A2 (Enc k m1) st)) 1
  have hS (k : K) (m : M): (A2 (Enc k m) st) 0 + (A2 (Enc k m) st) 1 = 1 := by
    have := (A2 (Enc k m) st).tsum_coe
    rw [tsum_fintype, Fin.sum_univ_two] at this; exact this
  unfold local_pa
  split_ifs with hm01
  · simp only [hm01]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Prod.mk.injEq, PMF.bind_map,
      bind_apply, uniformOfFintype_apply, Fintype.card_fin, Nat.cast_ofNat, Function.comp_apply,
      pure_apply, left_eq_ite_iff, not_or, not_and, one_ne_zero, imp_false, Classical.not_imp,
      Decidable.not_not, mul_ite, mul_one, mul_zero, tsum_bit]
    simp only [Fin.isValue, Matrix.cons_val_zero, not_true_eq_false, imp_false, zero_ne_one,
      and_false, imp_self, ↓reduceIte, not_false_eq_true, and_self,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [← two_mul, ENNReal.mul_inv_cancel_left (by norm_num : (2:ENNReal) ≠ 0) (by norm_num)]
    conv_lhs =>
      -- if [Fintype K] is not available arg 1; arg 2; arg 1; ext k; arg 2;
      arg 1; ext k; arg 2
      apply hS
    simp only [mul_one]
    exact tsum_coe Gen
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Prod.mk.injEq, PMF.bind_map,
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

-- 局所的な p0/p1 相当 (A2 が 1 を出す確率)
noncomputable def p_local (Enc : K → M → C) (Gen : PMF K)
                          (A2 : C → St → PMF Bit) (m : M) (st : St) : ENNReal :=
  (Gen.bind fun k ↦ A2 (Enc k m) st) 1



/-- Expand pa into a tsum over A1's support. -/
lemma pa_eq_tsum (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit) :
    pa Enc Gen (B1 A1) (B2 A2) = ∑' x, A1 x * local_pa Enc Gen A2 x.1 x.2.1 x.2.2 := by
  -- 1. 全ての定義を展開する
  unfold pa B1 B2
  -- 2. bind_assoc を使って A1 の bind を一番外側に持ってくる
  -- (do a <- (do b <- A1; pure f); g)  =>  (do b <- A1; g [f/a])
  simp only [bind_assoc]
  -- 3. PMF.bind_apply を使って、一番外側の bind を ∑' に変換する
  -- (A1.bind f) 1 = ∑' x, A1 x * (f x)
  -- simp only [PMF.bind_apply]

  -- 4. 各項が一致することを確認する (x : M × M × St)
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

lemma ps_eq_tsum (A1 : PMF (M × M × St)) (S : Bit → St → PMF Bit) :
    ps (B1 A1) S = ∑' x, A1 x * local_ps S x.1 x.2.1 x.2.2 := by
  unfold ps B1
  simp only [bind_assoc]
  apply tsum_congr; intro ⟨m0, m1, st⟩
  congr 2
  apply PMF.ext; intro a'
  rw [bind_apply]
  -- pa で使った simp only のセットをそのまま投入
  simp only [bind_apply, pure_apply, Bind.bind, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    Prod.mk.injEq, mul_ite, mul_one, mul_zero, tsum_fintype, Fin.sum_univ_two, ite_mul, one_mul,
    zero_mul, tsum_ite_eq, map_apply, uniformOfFintype_apply, Fintype.card_fin, Nat.cast_ofNat,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, and_true, zero_ne_one,
    and_false, or_false, one_ne_zero, false_or]

lemma p0_eq_tsum (Enc : K → M → C) (Gen : PMF K) (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit) :
    p0 Enc Gen A1 A2 = ∑' x, A1 x * p_local Enc Gen A2 x.1 x.2.2 := by
  unfold p0 p_local
  -- A1 の bind を ∑' に変えたら、あとは A1 x * の中身が一致することを示すだけ
  apply tsum_congr; intro ⟨m0, m1, st⟩
  rw [bind_apply]
  congr

lemma p1_eq_tsum (Enc : K → M → C) (Gen : PMF K) (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit) :
    p1 Enc Gen A1 A2 = ∑' x, A1 x * p_local Enc Gen A2 x.2.1 x.2.2 := by
  unfold p1 p_local
  apply tsum_congr; intro ⟨m0, m1, st⟩
  rw [bind_apply]
  congr


/-- Core Local Equality: The difference at each point. -/
lemma local_diff_eq (Enc : K → M → C) (Gen : PMF K)
    (A2 : C → St → PMF Bit) (S : Bit → St → PMF Bit) (m0 m1 : M) (st : St) :
    (local_pa Enc Gen A2 m0 m1 st).toReal - (local_ps S m0 m1 st).toReal =
    1 / 2 * (p_local Enc Gen A2 m1 st).toReal - 1 / 2 * (p_local Enc Gen A2 m0 st).toReal := by
  by_cases hm01 : m1 = m0
  · -- Case: m0 = m1
    -- local_pa, local_ps 共に 1 になり、p_local も同一になるため 0 = 0
    subst hm01
    have pa_1 : local_pa Enc Gen A2 m1 m1 st = 1 := by
      rw [local_pa_eval]; simp
    have ps_1 : local_ps S m1 m1 st = 1 := by
      rw [local_ps_eval]; simp
    simp [pa_1, ps_1]
  · -- Case: m0 ≠ m1
    have h_pa := local_pa_eval Enc Gen A2 m0 m1 st
    have h_ps := local_ps_eval m0 m1 st S
    push_neg at hm01
    simp [hm01.symm] at h_pa h_ps
    -- ENNReal から Real への変換
    rw [h_pa, h_ps]
    unfold p_local
    rw [ENNReal.toReal_add]
    · simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]
      simp only [ENNReal.toReal_ofNat, Fin.isValue, one_div, bind_apply]
      rw [ENNReal.toReal_sub_of_le]
      · rw [ENNReal.toReal_one]
        ring
      · apply PMF.tsum_mul_le_one
        exact fun x ↦ coe_le_one (A2 (Enc x m0) st) 1
      · norm_num
    · apply ENNReal.mul_ne_top (by norm_num)
      apply ENNReal.sub_ne_top (by norm_num)
    · apply ENNReal.mul_ne_top (by norm_num)
      apply PMF.tsum_mul_ne_top
      exact fun x ↦ coe_le_one (A2 (Enc x m1) st) 1


/--
The fundamental reduction:
The advantage in the semantic security game (pa - ps) is exactly
half of the advantage in the indistinguishability game (p1 - p0).

This lemma is the "global" version of the local evaluations we just proved.
It naturally handles m0 = m1 because those terms become 0 on both sides.
-/
lemma pa_sub_ps_eq_half_dist (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit) (S : Bit → St → PMF Bit) :
    (pa Enc Gen (B1 A1) (B2 A2)).toReal - (ps (B1 A1) S).toReal =
    1 / 2 * ((p1 Enc Gen A1 A2).toReal - (p0 Enc Gen A1 A2).toReal) := by
  -- 1. pa, ps, p0, p1 をすべて tsum 形式に書き換える
  rw [pa_eq_tsum, ps_eq_tsum, p0_eq_tsum, p1_eq_tsum]
  -- 2. ENNReal の tsum の .toReal を、項ごとの .toReal の tsum に変換する
  -- (PMF の和は有限なので、ENNReal.toReal_tsum が使えます)
  rw [tsum_fintype,tsum_fintype,tsum_fintype,tsum_fintype]
  rw [ENNReal.toReal_sum,ENNReal.toReal_sum,ENNReal.toReal_sum,ENNReal.toReal_sum]
  · rw [← Finset.sum_sub_distrib]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_mul]
    simp_rw [← mul_sub]
    conv_lhs => arg 2; ext a; arg 2; rw [local_diff_eq]
    conv_lhs => arg 2; ext a; arg 2; rw [one_div, ← mul_sub]
    conv_lhs => arg 2; ext a; rw [mul_comm,mul_assoc]
    rw [← Finset.mul_sum, one_div, ← Finset.sum_sub_distrib]
    congr 2; ext i
    rw [mul_comm, mul_sub]
  any_goals
    intro _ _
    apply ENNReal.mul_ne_top <;> apply PMF.apply_ne_top





/-- The absolute version of the advantage equality. -/
lemma abs_pa_sub_ps_eq_half_dist (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (M × M × St)) (A2 : C → St → PMF Bit) (S : Bit → St → PMF Bit) :
    |(pa Enc Gen (B1 A1) (B2 A2)).toReal - (ps (B1 A1) S).toReal| =
    1 / 2 * |(p1 Enc Gen A1 A2).toReal - (p0 Enc Gen A1 A2).toReal| := by
  -- pa - ps = 1/2 * (p1 - p0) さえあれば、両辺の絶対値をとるだけで証明できます
  rw [pa_sub_ps_eq_half_dist]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]

-- ============================================================
-- Section 4: Main theorem (Steps 1–5)
--
-- Step 1: by_contra + push_neg to obtain |p0 - p1| > ε
-- Step 2: apply pa_gt_half to obtain ∃ B2' with pa > 1/2*(1+ε)
-- Step 3: apply SemanticallySecure to (B1 A1, B2 B2') to obtain simulator S
-- Step 4: apply ps_le_half to obtain ps ≤ 1/2
-- Step 5: derive pa - ps > ε/2, contradicting hss_ineq
-- ============================================================

/-- Theorem 3.1: (t, α, ε/2)-Semantic Security implies (t, ε)-Indistinguishability. -/
theorem semantic_security_implies_indistinguishable
    (Enc : K → M → C) (Gen : PMF K)
    (t α : ℕ) (ε : NNReal)
    (hss : SemanticallySecure (St := St) Enc Gen t α (ε / 2)) :
    Indistinguishable (St := St) Enc Gen t ε := by
  -- 1. 識別不可能性の攻撃者 (A1, A2) を受け取る
  intro A1 _hne A2 tA1 tA2 htA

  -- 2. 意味的安全性の仮定を (B1 A1, B2 A2) に適用し、シミュレータ S を得る
  -- (この時、B1 A1 と B2 A2 の計算量は A1, A2 と同じであると仮定)
  obtain ⟨S, _tS, _htS, h_sem_advantage⟩ := hss (B1 A1) (B2 A2) tA1 tA2 htA
  -- h_sem_advantage: |pa - ps| ≤ ε / 2

  -- 3. 「意味的安全性の差」と「識別不可能性の差」の等式を呼び出す
  have h_AdvEq := abs_pa_sub_ps_eq_half_dist Enc Gen A1 A2 S

  -- 4. 等式を代入して整理する
  -- |pa - ps| ≤ ε / 2  =>  1/2 * |p1 - p0| ≤ ε / 2
  rw [h_AdvEq] at h_sem_advantage

  -- 5. 両辺を 2 倍して、目標の |p1 - p0| ≤ ε を導く
  -- ENNReal の ε / 2 を Real の (ε : ℝ) / 2 に直す必要があるかもしれません
  have : ((ε / 2 : NNReal) : ℝ) = (ε : ℝ) / 2 := rfl
  rw [this] at h_sem_advantage
  rw [abs_sub_comm] at h_sem_advantage
  linarith

end ComputationalSecurity
