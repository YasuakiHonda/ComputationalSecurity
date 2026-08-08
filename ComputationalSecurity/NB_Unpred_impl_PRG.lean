import ComputationalSecurity.DistInd
import ComputationalSecurity.BVCryptGameLib
import ComputationalSecurity.PRG_impl_NB_Unpred
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise

namespace ComputationalSecurity

open PMF
open BVCryptGame



variable {α : Type}

-- ============================================================
-- 1. Algorithm constructions
-- ============================================================

/-- A new distinguisher that negates the output of `A`. -/
noncomputable def negate_distinguisher (A : α → PMF Bit) (x : α) : PMF Bit := do
  let a ← A x
  PMF.pure (if a == 1 then 0 else 1)

/-- Negating a distinguisher's output turns its success probability into `1 - original`. -/
lemma PrDX_one_negate {α : Type} (Y : PMF α) (A : α → PMF Bit) :
    PrDX_one Y (negate_distinguisher A) = 1 - PrDX_one Y A := by
  unfold PrDX_one
  set q : PMF Bool := (do let a ← Y >>= A; PMF.pure (a == 1)) with hq
  have h_reform : (do let a ← (Y >>= negate_distinguisher A); PMF.pure (a == 1)) =
                  q.bind (fun b => PMF.pure (!b)) := by
    unfold negate_distinguisher
    simp only [bind_assoc, hq]
    simp only [Bind.bind, PMF.bind_bind, PMF.pure_bind]
    congr 1; funext a; congr 1; funext b; congr 1;
    cases h : (b == 1) <;> simp
  rw [h_reform, Pr_negate]
  unfold Pr
  rw [ENNReal.toReal_sub_of_le (PMF.coe_le_one q true) (by norm_num)]
  rfl

/-- Constructs a next-bit predictor `B` from a distinguisher `A`. -/
noncomputable def predictor_B (A : α × Bool → PMF Bit) (x : α) : PMF Bool := do
  let z ← PMF.uniformOfFintype Bool
  let a ← A (x, z)
  PMF.pure (if a == 1 then z else !z)

-- ============================================================
-- 2. Advantage and success probability (joint-distribution version)
-- ============================================================

/-- The advantage of distinguisher `A` on the joint distribution `X_joint`.
    `α` is the type of the prefix (e.g. `BitVec i`). -/
noncomputable def advantage {α : Type} (X_joint : PMF (α × Bool)) (A : α × Bool → PMF Bit) : ℝ :=
  PrDX_one X_joint A -
  PrDX_one (do let (x, _) ← X_joint; let u ← U 1; PMF.pure (x, u.getLsbD 0)) A

/-- The advantage of a negated distinguisher is the negation of the original advantage. -/
lemma advantage_negate {α : Type} (X_joint : PMF (α × Bool)) (A : α × Bool → PMF Bit) :
    advantage X_joint (negate_distinguisher A) = - advantage X_joint A := by
  unfold advantage
  rw [PrDX_one_negate, PrDX_one_negate]
  ring

/-- The success probability of predictor `B` on the joint distribution `X_joint`. -/
noncomputable def prediction_success_prob {α : Type}
      (X_joint : PMF (α × Bool)) (B : α → PMF Bool) : ℝ :=
  (Pr (do
    let (x, p_x) ← X_joint
    let b ← B x
    PMF.pure (b == p_x)
  )).toReal

-- ============================================================
-- 3. Lemma 4.2 (Prediction Lemma)
-- ============================================================

/-- The core identity behind Lemma 4.2. -/
lemma predictor_B_success_eq_half_plus_adv {α : Type} (X_joint : PMF (α × Bool))
    (A : α × Bool → PMF Bit) :
    prediction_success_prob X_joint (predictor_B A) = 1 / 2 + advantage X_joint A := by
  unfold prediction_success_prob advantage PrDX_one
  rw [bind_assoc,bind_assoc,bind_assoc]

  -- Lift the real equality to an ENNReal equality.
  have h_real_goal :
      (Pr (do let (x, p_x) ← X_joint; let b ← predictor_B A x; PMF.pure (b == p_x))).toReal
      + (Pr (do let (x, _) ← X_joint; let b ← PMF.uniformOfFintype Bool; let a ← A (x, b); PMF.pure (a == 1))).toReal
      = (1 / 2 : ℝ) + (Pr (do let (x, p_x) ← X_joint; let a ← A (x, p_x); PMF.pure (a == 1))).toReal := by
    have h_enn : (Pr (do let (x, p_x) ← X_joint; let b ← predictor_B A x; PMF.pure (b == p_x)))
               + (Pr (do let (x, _) ← X_joint; let b ← PMF.uniformOfFintype Bool; let a ← A (x, b); PMF.pure (a == 1)))
               = (1 / 2 : ENNReal) + (Pr (do let (x, p_x) ← X_joint; let a ← A (x, p_x); PMF.pure (a == 1))) := by
      unfold predictor_B
      simp only [bind_assoc, Fin.isValue]
      erw [Pr_bind, Pr_bind, Pr_bind]
      rw [← ENNReal.tsum_add]
      simp_rw [← mul_add]
      -- The complex first term matches `Pr_prediction_logic` for any `x`, `target`.
      have h_sub (x_val : α) (target_val : Bool) :
        Pr (do
          let x ← uniformOfFintype Bool
          let x_1 ← A (x_val, x)
          let b ← PMF.pure (if (x_1 == 1) = true then x else !x)
          PMF.pure (b == target_val)) =
        Pr (do
          let w ← uniformOfFintype Bool
          let a ← (fun w => A (x_val, w)) w
          PMF.pure ((if a == 1 then w else !w) == target_val)) := by
        simp only [Fin.isValue, beq_iff_eq]
        congr; funext x; congr; funext x_1;
        simp only [Bind.bind, PMF.pure_bind]

      simp_rw [h_sub]
      simp_rw [Pr_prediction_logic]
      have hq : Pr (uniformOfFintype Bool) = (1 / 2 : ENNReal) := by
        simp [Pr, PMF.uniformOfFintype_apply]
      rw [← hq]
      exact Pr_bind_add_const X_joint (uniformOfFintype Bool) _


    -- Lift `h_enn` to `ℝ` via `toReal`, distributing the sum.
    have h_toReal := congrArg ENNReal.toReal h_enn
    erw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)] at h_toReal
    erw [ENNReal.toReal_add (by norm_num) (PMF.apply_ne_top _ _)] at h_toReal
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h_toReal
    exact h_toReal
  have h_real_goal2 :
      (Pr (do let (x, p_x) ← X_joint; let b ← predictor_B A x; PMF.pure (b == p_x))).toReal
      = (1 / 2 : ℝ) + (Pr (do let (x, p_x) ← X_joint; let a ← A (x, p_x); PMF.pure (a == 1))).toReal - (Pr (do let (x, _) ← X_joint; let b ← PMF.uniformOfFintype Bool; let a ← A (x, b); PMF.pure (a == 1))).toReal := by
    exact eq_sub_of_add_eq h_real_goal
  rw [h_real_goal2]
  rw [add_sub_assoc]
  congr; funext y;
  simp only [bind_assoc]
  rw [← U1_to_bool]
  simp only [Bind.bind]
  simp only [Fin.isValue, PMF.bind_map, zero_lt_one, BitVec.getLsbD_eq_getElem, PMF.pure_bind]
  congr


/-- Lemma 4.2: complexity and success-probability guarantee for the constructed predictor. -/
lemma prediction_lemma {α : Type} (X_joint : PMF (α × Bool))
    (A : α × Bool → PMF Bit) (tA : ℕ) (ε : ℝ) (t_redB : ℕ) :
    |advantage X_joint A| > ε →
    ∃ (B : α → PMF Bool) (tB : ℕ),
      tB = tA + t_redB ∧
      prediction_success_prob X_joint B > 1 / 2 + ε := by

  intro h_abs
  have h_cases := lt_abs.mp h_abs
  cases h_cases with
  | inl h_pos => -- adv > ε
      use (predictor_B A), (tA + t_redB)
      constructor
      · rfl
      · rw [predictor_B_success_eq_half_plus_adv]
        linarith
  | inr h_neg => -- adv < -ε
      use (predictor_B (negate_distinguisher A)), (tA + t_redB)
      constructor
      · rfl
      · rw [predictor_B_success_eq_half_plus_adv, advantage_negate]
        · linarith



-- ============================================================
-- 4. Theorem 4.2 (NB-unpredictability ↔ pseudorandomness)
-- ============================================================

-- ============================================================
-- 1. Bit extraction and the isomorphism defining `X_joint`
-- ============================================================

/-- The joint distribution of `(prefix, next_bit)` extracted from `X`.
    Uses `bv_split3_i i`, converting the middle bit to `Bool`. -/
noncomputable def X_joint (X : PMF (BitVec L)) (i : Fin L) : PMF (BitVec i × Bool) :=
  X.map (fun x =>
    let triple := bv_split3_i i x
    (triple.1, triple.2.1.getLsbD 0)
  )

-- ============================================================
-- 2. Hybrid distribution definition
-- ============================================================

/-- The hybrid distribution `H X i`: prefix `i` bits from `X`, suffix from `U L`,
    joined via `bv_split_i`. -/
noncomputable def H (X : PMF (BitVec L)) (i : Fin (L + 1)) : PMF (BitVec L) :=
  do
    let x ← X
    let u ← U L
    let x_parts := bv_split_i i x
    let u_parts := bv_split_i i u
    PMF.pure ((bv_split_i i).symm (x_parts.1, u_parts.2))

/-- `Pr_predict_success` (defined directly via `X`) agrees with `prediction_success_prob`
    (defined via the joint distribution `X_joint`), for the specific index `i`. -/
lemma Pr_predict_success_eq_prediction_success_prob {L : ℕ} (X : PMF (BitVec L)) (i : Fin L)
    (B : BitVec i → PMF Bool) :
    Pr_predict_success X i B = prediction_success_prob (X_joint X i) B := by
  unfold Pr_predict_success prediction_success_prob X_joint
  congr 1
  unfold PMF.map
  simp only [Bind.bind, PMF.bind_bind]
  simp only [zero_lt_one, BitVec.getLsbD_eq_getElem, Function.comp_apply, PMF.pure_bind]
  congr 2; funext x;
  simp only [bv_split3_i_proj_pre]
  rw [← bv_split3_i_proj_bool]
  rfl

-- ============================================================
-- 3. Hybrid-argument infrastructure lemmas
-- ============================================================

/-- [Boundary 0]: `H X 0 = U L`. -/
lemma H_zero_eq_U (X : PMF (BitVec L)) : H X 0 = U L := by
  unfold H
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.sub_zero]

  calc
    (do let x ← X; let u ← U L
        let x_parts := bv_split_i 0 x
        let u_parts := bv_split_i 0 u
        PMF.pure ((bv_split_i 0).symm (x_parts.1, u_parts.2)))
    -- Step 1: `x_parts.1 = u_parts.1` since `BitVec 0` is a subsingleton.
    _ = (do let x ← X; let u ← U L
            let u_parts := bv_split_i 0 u
            PMF.pure ((bv_split_i 0).symm (u_parts.1, u_parts.2))) := by
        congr; funext x; congr; funext u
        have h_pre : (bv_split_i 0 x).1 = (bv_split_i 0 u).1 := by
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
          apply Subsingleton.elim
        simp only [h_pre]
    -- Step 2: `symm` applied to `(u_parts.1, u_parts.2)` recovers `u`.
    _ = (do let x ← X; let u ← U L; PMF.pure u) := by
        congr; funext x; congr; funext u
        simp only [Prod.mk.eta, Equiv.symm_apply_apply]
    -- Step 3: `pure`-ing the sampled value is just `U L` (`bind_pure`).
    _ = (do let x ← X; U L) := by
        congr; funext x
        exact PMF.bind_pure (U L)
    -- Step 4: discard the unused sample `x` (`bind_const`).
    _ = U L := by
        exact PMF.bind_const X (U L)


/-- [Boundary L]: `H X (Fin.last L) = X`. -/
lemma H_L_eq_X (X : PMF (BitVec L)) : H X (Fin.last L) = X := by
  unfold H
  simp only [Fin.val_last]

  calc
    (do let x ← X; let u ← U L
        let x_parts := bv_split_i (Fin.last L) x
        let u_parts := bv_split_i (Fin.last L) u
        PMF.pure ((bv_split_i (Fin.last L)).symm (x_parts.1, u_parts.2)))
    -- Step 1: `u_parts.2 = x_parts.2` since the suffix `BitVec 0` is a subsingleton.
    _ = (do let x ← X; let u ← U L
            let x_parts := bv_split_i (Fin.last L) x
            PMF.pure ((bv_split_i (Fin.last L)).symm (x_parts.1, x_parts.2))) := by
        congr; funext x; congr; funext u
        have h_suf : (bv_split_i (Fin.last L) u).2 = (bv_split_i (Fin.last L) x).2 := by
          simp only [Fin.val_last]
          apply Subsingleton.elim
        simp only [h_suf]
    -- Step 2: `symm` applied to `(x_parts.1, x_parts.2)` recovers `x`.
    _ = (do let x ← X; let u ← U L; PMF.pure x) := by
        congr; funext x; congr; funext u
        simp only [Prod.mk.eta, Equiv.symm_apply_apply]
    -- Step 3: discard the unused sample `u` (`bind_const`).
    _ = (do let x ← X; PMF.pure x) := by
        congr; funext x
        exact PMF.bind_const (U L) (PMF.pure x)
    -- Step 4: `pure`-ing the sampled value is just `X` itself (`bind_pure`).
    _ = X := by
        exact PMF.bind_pure X


/-- Unfolds `H X i.castSucc` into the three-way `bv_split3_i` form
    (prefix from `X`; bit and suffix uniform). -/
lemma H_step_equiv_curr (X : PMF (BitVec L)) (i : Fin L) :
    H X ⟨i.castSucc, by omega⟩ = (do
      let x ← X; let u_bit ← U 1; let u_suf ← U (L - i - 1)
      let x_pre := (bv_split3_i i x).1
      PMF.pure ((bv_split3_i i).symm (x_pre, u_bit, u_suf))) := by
  unfold H
  calc
    (do let x ← X; let u ← U L
        let x_parts := bv_split_i (i.castSucc : Fin (L+1)) x
        let u_parts := bv_split_i (i.castSucc : Fin (L+1)) u
        PMF.pure ((bv_split_i (i.castSucc : Fin (L+1))).symm (x_parts.1, u_parts.2)))
    -- Step 1: split `U L` via `U_split3_i`.
    _ = (do
          let x ← X
          let u_pre ← U i; let u_bit ← U 1; let u_suf ← U (L - i - 1)
          PMF.pure ((bv_split_i (i.castSucc : Fin (L+1))).symm
            ((bv_split_i (i.castSucc : Fin (L+1)) x).1,
             (bv_split_i (i.castSucc : Fin (L+1))
               ((bv_split3_i i).symm (u_pre, u_bit, u_suf))).2))) := by
        congr 1; funext x
        rw [U_split3_i i]
        simp only [bind_assoc, pure_bind_do]
        rfl
    -- Step 2: rewrite the suffix component via `bv_split_i_castSucc_eq_split3_i`.
    _ = (do
          let x ← X
          let u_pre ← U i; let u_bit ← U 1; let u_suf ← U (L - i - 1)
          PMF.pure ((bv_split_i (i.castSucc : Fin (L+1))).symm
            ((bv_split_i (i.castSucc : Fin (L+1)) x).1,
            (suf_as_bit_suf i).symm (u_bit, u_suf)))) := by
        congr 1; funext x; congr 1; funext u_pre; congr 1; funext u_bit; congr 1; funext u_suf
        congr 2
        have h_apply := congrArg (bv_split_i (i.castSucc : Fin (L+1)))
          (bv_split_i_castSucc_eq_split3_i i u_pre u_bit u_suf)
        rw [Equiv.apply_symm_apply] at h_apply
        rw [eq_comm] at h_apply
        congr 1
        exact congrArg Prod.snd h_apply
    _ = (do
          let x ← X
          let u_bit ← U 1; let u_suf ← U (L - i - 1)
          PMF.pure ((bv_split_i (i.castSucc : Fin (L+1))).symm
            ((bv_split_i (i.castSucc : Fin (L+1)) x).1,
             (suf_as_bit_suf i).symm (u_bit, u_suf)))) := by
        congr 1; funext x
        rw [bind_unused]
    -- Step 3: replace `bv_split_i` by `bv_split3_i` via the compatibility lemma.
    _ = (do
          let x ← X
          let u_bit ← U 1; let u_suf ← U (L - i - 1)
          PMF.pure ((bv_split3_i i).symm
            ((bv_split_i (i.castSucc : Fin (L+1)) x).1, u_bit, u_suf))) := by
        congr 1; funext x; congr 1; funext u_bit; congr 1; funext u_suf
        congr 1
        exact bv_split_i_castSucc_eq_split3_i i _ u_bit u_suf
    -- Step 4: replace the prefix component with its `bv_split3_i` form.
    _ = (do
          let x ← X
          let u_bit ← U 1; let u_suf ← U (L - i - 1)
          let x_pre := (bv_split3_i i x).1
          PMF.pure ((bv_split3_i i).symm (x_pre, u_bit, u_suf))) := by
        congr 1; funext x; congr 1; funext u_bit; congr 1; funext u_suf
        rw [bv_split_i_castSucc_fst_eq_split3_i_fst]

/-- Unfolds `H X i.succ` into the three-way `bv_split3_i` form
    (prefix and bit from `X`; suffix uniform). -/
lemma H_step_equiv_next (X : PMF (BitVec L)) (i : Fin L) :
    H X ⟨i.succ, by omega⟩ = (do
      let x ← X; let u_suf ← U (L - i - 1)
      let (x_pre, x_bit, _) := bv_split3_i i x
      PMF.pure ((bv_split3_i i).symm (x_pre, x_bit, u_suf))) := by
  unfold H
  calc
    (do let x ← X; let u ← U L
        let x_parts := bv_split_i (i.succ : Fin (L+1)) x
        let u_parts := bv_split_i (i.succ : Fin (L+1)) u
        PMF.pure ((bv_split_i (i.succ : Fin (L+1))).symm (x_parts.1, u_parts.2)))
    -- Step 1: split `U L` via `U_split_i` and drop the unused prefix.
    _ = (do
          let x ← X
          let u_suf ← U (L - i - 1)
          PMF.pure ((bv_split_i (i.succ : Fin (L+1))).symm
            ((bv_split_i (i.succ : Fin (L+1)) x).1, u_suf))) := by
        congr 1; funext x
        rw [U_split_i (i.succ : Fin (L+1))]
        simp only [bind_assoc, pure_bind_do]
        simp only [bv_join_i, Equiv.apply_symm_apply]
        rw [bind_unused]
        rfl
    -- Step 2: replace the prefix component with the `(prefix, bit)` pair from `bv_split3_i`.
    _ = (do
          let x ← X
          let u_suf ← U (L - i - 1)
          PMF.pure ((bv_split_i (i.succ : Fin (L+1))).symm
            ((pre_as_pre_bit i).symm ((bv_split3_i i x).1, (bv_split3_i i x).2.1), u_suf))) := by
        congr 1; funext x; congr 1; funext u_suf
        congr 2; congr
        exact bv_split_i_succ_fst_eq_pre_as_pre_bit_symm i x
    -- Step 3: replace `bv_split_i` by `bv_split3_i` via the compatibility lemma.
    _ = (do
          let x ← X
          let u_suf ← U (L - i - 1)
          PMF.pure ((bv_split3_i i).symm ((bv_split3_i i x).1, (bv_split3_i i x).2.1, u_suf))) := by
        congr 1; funext x; congr 1; funext u_suf; congr 1
        exact bv_split_i_succ_eq_split3_i i _ _ u_suf
    -- Step 4: match the `let`-pattern notation.
    _ = (do
          let x ← X; let u_suf ← U (L - i - 1)
          let (x_pre, x_bit, _) := bv_split3_i i x
          PMF.pure ((bv_split3_i i).symm (x_pre, x_bit, u_suf))) := rfl

/-- The difference between `H X i` and `H X (i+1)` equals the advantage of
    `A_prime` on `X_joint X i`. -/
lemma H_step_diff_eq_advantage (X : PMF (BitVec L)) (i : Fin L) (A : BitVec L → PMF Bit) :
    let A_prime := fun (pair : BitVec i × Bool) => do
      let suf ← U (L - i - 1)
      let b_vec := bv_to_bool.symm pair.2
      A ((bv_split3_i i).symm (pair.1, b_vec, suf))
    |PrDX_one (H X i.succ) A - PrDX_one (H X ⟨i, by omega⟩) A| = |advantage (X_joint X i) A_prime| := by
  intro A_prime
  -- 1. Unfold `H X i`/`H X (i+1)` via the bridge lemmas.
  have h_curr := H_step_equiv_curr X i
  have h_next := H_step_equiv_next X i

  have h_Pr_next : PrDX_one (H X i.succ) A = PrDX_one (X_joint X i) A_prime := by
    have h_enn : Pr (do let x ← H X i.succ; let a ← A x; PMF.pure (a == 1)) =
               Pr (do let pair ← X_joint X i; let a ← A_prime pair; PMF.pure (a == 1)) := by
      calc
        Pr (do let x ← H X i.succ; let a ← A x; PMF.pure (a == 1))
        -- Step 1: unfold `H X (i+1)` via `H_step_equiv_next`.
        _ = Pr (do
              let x ← X; let u ← U L
              let (x_pre, x_bit, _) := bv_split3_i i x
              let (_, _, u_suf) := bv_split3_i i u
              let a ← A ((bv_split3_i i).symm (x_pre, x_bit, u_suf))
              PMF.pure (a == 1)) := by
                rw [h_next]
                simp only [Equiv.toFun_as_coe, Fin.isValue, bind_assoc]
                congr; funext x;
                rw [U_split3_i i]
                simp only [Fin.isValue, bind_assoc]
                simp only [pure_bind_do]
                simp only [bv_join3_i, Equiv.apply_symm_apply]
                simp only [bind_unused]

        -- Step 2: split `U L` via `U_split3_i`.
        _ = Pr (do
              let x ← X
              let _u_pre ← U i; let _u_bit ← U 1; let u_suf ← U (L - i - 1)
              let (x_pre, x_bit, _) := bv_split3_i i x
              let a ← A ((bv_split3_i i).symm (x_pre, x_bit, u_suf))
              PMF.pure (a == 1)) := by
            simp_rw [U_split3_i i, bind_assoc, pure_bind_do]
            simp only [bv_join3_i]
            simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply, Fin.isValue, bind_unused]
        -- Step 3: drop the unused `_u_pre`, `_u_bit` via `bind_unused`.
        _ = Pr (do
              let x ← X; let u_suf ← U (L - i - 1)
              let (x_pre, x_bit, _) := bv_split3_i i x
              let a ← A ((bv_split3_i i).symm (x_pre, x_bit, u_suf))
              PMF.pure (a == 1)) := by
            simp only [bind_unused]
        -- Step 4: repackage the `X` sampling as `X_joint`.
        _ = Pr (do
              let pair ← X_joint X i
              let a ← A_prime pair
              PMF.pure (a == 1)) := by
            unfold X_joint A_prime
            unfold PMF.map
            simp only [bind_bind_do, Function.comp_apply, pure_bind_do, bind_assoc]
            simp only [Equiv.toFun_as_coe, Fin.isValue, zero_lt_one, BitVec.getLsbD_eq_getElem]
            congr 2; funext x; congr 1; funext u_suf; congr 5;
            rw [← bv_to_bool.left_inv ((bv_split3_i i) x).2.1]
            simp only [bv_to_bool]
            simp_all
            split
            · next h => simp_all only [BitVec.getElem_one, decide_true, ↓reduceIte]
            · next h => simp_all only [BitVec.getElem_zero, Bool.false_eq_true, ↓reduceIte]
    unfold PrDX_one
    simp
    exact congrArg ENNReal.toReal h_enn

  have h_Pr_curr : PrDX_one (H X i.castSucc) A =
      PrDX_one (do let (pre, _) ← X_joint X i; let u ← U 1; PMF.pure (pre, u.getLsbD 0)) A_prime := by
    have h_enn : Pr (do let x ← H X i.castSucc; let a ← A x; PMF.pure (a == 1)) =
               Pr (do let pair ← X_joint X i; let u ← U 1; let a ← A_prime (pair.1, u.getLsbD 0); PMF.pure (a == 1)) := by
      calc
        Pr (do let x ← H X i.castSucc; let a ← A x; PMF.pure (a == 1))
        -- 1. unfold `H X i` via `H_step_equiv_curr`.
        _ = Pr (do
              let x ← X; let u ← U L
              let x_pre := (bv_split3_i i x).1
              let (_, u_bit, u_suf) := bv_split3_i i u
              let a ← A ((bv_split3_i i).symm (x_pre, u_bit, u_suf))
              PMF.pure (a == 1)) := by
                simp only [h_curr, bind_assoc]
                congr 2; funext x
                simp only [U_split3_i i, bind_assoc, pure_bind_do]
                simp only [Equiv.toFun_as_coe, Prod.mk.eta]
                simp only [bv_join3_i, Equiv.apply_symm_apply]
                simp only [bind_unused]
        -- 2. split `U L` via `U_split3_i`.
        _ = Pr (do
              let x ← X
              let _u_pre ← U i; let u_bit ← U 1; let u_suf ← U (L - i - 1)
              let x_pre := (bv_split3_i i x).1
              let a ← A ((bv_split3_i i).symm (x_pre, u_bit, u_suf))
              PMF.pure (a == 1)) := by
                simp_rw [U_split3_i i, bind_assoc, pure_bind_do,Prod.mk.eta]
                simp only [bv_join3_i, Equiv.apply_symm_apply]
        -- 3. drop the unused `_u_pre`.
        _ = Pr (do
              let x ← X; let u_bit ← U 1; let u_suf ← U (L - i - 1)
              let x_pre := (bv_split3_i i x).1
              let a ← A ((bv_split3_i i).symm (x_pre, u_bit, u_suf))
              PMF.pure (a == 1)) := by
            simp only [bind_unused]

        -- 4. repackage as `X_joint` and feed `u_bit` to `A_prime`.
        _ = Pr (do
              let pair ← X_joint X i
              let u ← U 1
              let a ← A_prime (pair.1, u.getLsbD 0)
              PMF.pure (a == 1)) := by
            unfold X_joint A_prime
            simp only [bind_assoc]
            simp [Bind.bind]; congr; funext pair; congr; funext u_bit; congr; funext u_suf
            congr;
            exact (Equiv.symm_apply_eq bv_to_bool.symm).mp rfl
    unfold PrDX_one
    apply congrArg ENNReal.toReal
    simp only [bind_assoc]
    simp only [h_enn]
    simp only [pure_bind_do]


  -- Substitute into `advantage`'s definition.
  unfold advantage
  rw [h_Pr_next]
  erw [h_Pr_curr]


-- ============================================================
-- 4. Theorem 4.2, main body
-- ============================================================

/-- Theorem 4.2 (contrapositive): not pseudorandom ⇒ next-bit predictable.
    `t_redH`/`t_redB` are the complexity overheads of building the hybrid
    distinguisher and the predictor. -/
theorem unpredictability_implies_pseudorandomness {L : ℕ} {X : PMF (BitVec L)}
    (t : ℕ) (ε : NNReal) (t_redH t_redB : ℕ) (hL : L > 0) :
    -- Hypothesis: an adversary distinguishing with advantage `ε * L` at complexity `t`.
    ¬ DistIndistinguishable X (U L) t (ε * L) →
    -- Conclusion: a next-bit predictor with advantage `ε/2` at complexity `t + t_redH + t_redB`.
    ¬ NextBitUnpredictable X (t + t_redH + t_redB) ε := by
  -- A. Extract the distinguisher `A`.
  intro h_not_pr
  unfold DistIndistinguishable at h_not_pr
  push_neg at h_not_pr
  obtain ⟨A, tA, htA, h_adv_A⟩ := h_not_pr

  -- B. Locate the hybrid boundary `i`.
  have h_total_adv : |PrDX_one (H X 0) A - PrDX_one (H X (Fin.last L)) A| > ((ε * L : NNReal) : ℝ) := by
    rw [abs_sub_comm]
    rw [H_L_eq_X, H_zero_eq_U]
    exact h_adv_A

  -- Locate the hybrid boundary directly via the `Fin`-indexed hybrid lemma.
  obtain ⟨i_fin, h_adv_step⟩ := hybrid_lemma_fin hL (H X) t (ε * L) A h_total_adv

  -- C. Construct the one-bit distinguisher `A'` via `bv_split3_i.symm`.
  let A_prime := fun (pair : BitVec i_fin × Bool) => do
    let suf ← U (L - i_fin - 1)
    -- convert `Bool` to `BitVec 1` via `bv_to_bool.symm`, avoiding raw bit manipulation
    let b_vec := bv_to_bool.symm pair.2
    A ((bv_split3_i i_fin).symm (pair.1, b_vec, suf))

  -- D. Evaluate `A'`'s advantage via `H_step_diff_eq_advantage`.
  have h_adv_A' : |advantage (X_joint X i_fin) A_prime| > (ε : ℝ) := by
    rw [← H_step_diff_eq_advantage X i_fin A]
    rw [abs_sub_comm]
    norm_cast at h_adv_step
    have h_cancel : (ε * ↑L / ↑L).toReal = ↑ε := by
      congr
      refine mul_div_cancel_right₀ ε ?_
      aesop
    rw [h_cancel] at h_adv_step
    exact h_adv_step


  -- E. Apply the prediction lemma to obtain `B` from `A'`.
  let tA' := tA + t_redH

  obtain ⟨B, tB, htB, h_succ_B⟩ := prediction_lemma
                (X_joint X i_fin) A_prime tA' (ε / 2) t_redB (by
                    have : ε.toReal ≥ ε.toReal / 2 := by exact NNReal.half_le_self ε
                    linarith [this, h_adv_A'])

  -- F. Assemble the conclusion.
  unfold NextBitUnpredictable
  push_neg
  use i_fin, B, tB
  constructor
  · -- complexity bound `tB ≤ t + t_redH + t_redB`.
    rw [htB]
    omega
  · rw [Pr_predict_success_eq_prediction_success_prob]
    exact h_succ_B




end ComputationalSecurity
