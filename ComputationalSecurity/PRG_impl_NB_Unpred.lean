/-
  PRG_impl_NB_Unpred.lean

  Formalizes the direction "pseudorandomness implies next-bit unpredictability"
  of Theorem 4.2 from the textbook.

  Main definitions:
    - Pr_predict_success : probability that algorithm A correctly predicts the
        (i+1)-th bit of a sample from X, given the first i bits.
    - NextBitUnpredictable : Definition 4.5; no efficient algorithm predicts
        the next bit with probability greater than 1/2 + ε/2.
    - predictor_to_distinguisher : reduction turning a next-bit predictor into
        a distribution distinguisher.

  Main results:
    - PrDX_one_U_predictor_eq_half : for the true uniform distribution U_L,
        every predictor succeeds with probability exactly 1/2.
    - pseudorandom_implies_unpredictable : (t+t_extract, ε/2)-pseudorandomness
        implies (t, ε)-next-bit unpredictability.

  Authors: Yasuaki Honda
-/
import ComputationalSecurity.DistInd
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise

namespace ComputationalSecurity

open PMF
open BVCryptGame

/-- A helper definition for the probability that algorithm A successfully predicts
    the (i+1)-th bit given the first i bits of a distribution X. -/
noncomputable def Pr_predict_success {L : ℕ}
    (X : PMF (BitVec L)) (i : Fin L) (A : BitVec i → PMF (Bool)) : ℝ :=
  (Pr (do
    let x ← X
    let x_pre := x.extractLsb' (L - i) i
    let x_bit := x.getLsbD (L - i - 1)
    let a ← A x_pre
    PMF.pure (a == x_bit)
  )).toReal

/-- Definition 4.5: (t, ε)-Next-Bit Unpredictability.
    A distribution X is next-bit unpredictable if no algorithm A with complexity ≤ t
    can predict the next bit with probability greater than 1/2 + ε/2 = 1/2 * (1 + ε). -/
def NextBitUnpredictable {L : ℕ} (X : PMF (BitVec L)) (t : ℕ) (ε : NNReal) : Prop :=
  ∀ (i : Fin L) (A : BitVec i → PMF (Bool)) (tA : ℕ),
    tA ≤ t →
    Pr_predict_success X i A ≤ (1 / 2 : ℝ) + (ε : ℝ) / 2

/-- The distinguisher constructed from a predicting algorithm A.
    It returns 1 if A successfully predicts the (i+1)-th bit, and 0 otherwise. -/
noncomputable
def predictor_to_distinguisher {L : ℕ} (i : Fin L)
    (A : BitVec i → PMF (Bool)) (x : BitVec L) : PMF Bit := do
  let x_pre := x.extractLsb' (L - i) i
  let x_bit := x.getLsbD (L - i - 1)
  let a ← A x_pre
  PMF.pure (if a == x_bit then 1 else 0)

/-- Lemma 1: The probability of predicting success is equal to the probability
    that the constructed distinguisher D outputs 1. -/
lemma Pr_predict_success_eq_PrDX_one {L : ℕ} (X : PMF (BitVec L)) (i : Fin L)
    (A : BitVec i → PMF (Bool)) :
    Pr_predict_success X i A = PrDX_one X (predictor_to_distinguisher i A) := by
  unfold Pr_predict_success PrDX_one predictor_to_distinguisher
  congr 2
  simp only [bind_assoc]
  congr; funext x
  congr; funext a
  -- The equality reduces to proving:
  -- (a == x.extractLsb' (L - i - 1) 1) = ((if a == x.extractLsb' (L - i - 1) 1 then 1 else 0) == 1)
  -- Since `a == ...` is a Bool, we can just do case analysis on it (true or false).
  cases (a == x.getLsbD (L - i - 1))
  · simp only [Bind.bind,Bool.false_eq_true, ↓reduceIte, Fin.isValue]
    simp only [Fin.isValue, PMF.pure_bind, Fin.reduceBEq]
  · simp only [Bind.bind,↓reduceIte, Fin.isValue]
    simp only [Fin.isValue, PMF.pure_bind, BEq.rfl]


/-- Mapping a uniform `L`-bit sample to `(prefix, bit)` equals independent sampling:
    the upper `i` bits are uniform over `BitVec i`, and the selected bit is a uniform
    coin flip, with both drawn independently.
    This is the core probabilistic decomposition used in `PrDX_one_U_predictor_eq_half`. -/
lemma U_map_pre_bit {L : ℕ} (i : Fin L) :
    (U L).map (fun x => (x.extractLsb' (L - i) i, x.getLsbD (L - i - 1))) =
    (do
      let pre ← U i
      let b ← PMF.uniformOfFintype Bool
      PMF.pure (pre, b)
    ) := by
  calc
    (U L).map (fun x => (x.extractLsb' (L - i) i, x.getLsbD (L - i - 1)))
    _ = (U L).map (fun x =>
          let triple := bv_split3_i i x
          (triple.1, triple.2.1.getLsbD 0)) := by
        congr; funext x
        simp only [bv_split3_i_proj_pre, bv_split3_i_proj_bool]
    -- Step 2: split `U L` via `U_split3_i`, pushing `map` down into the `pure` in the `do`-block.
    _ = (do
          let pre ← U i
          let bit ← U 1
          let suf ← U (L - i - 1)
          let triple := bv_split3_i i (bv_join3_i i (pre, bit, suf))
          PMF.pure (triple.1, triple.2.1.getLsbD 0)) := by
        rw [U_split3_i i]
        simp only [map_bind_do, map_pure_do]
    _ = (do
          let pre ← U i
          let bit ← U 1
          let suf ← U (L - i - 1)
          PMF.pure (pre, bit.getLsbD 0)) := by
        simp only [bv_join3_i, Equiv.apply_symm_apply]
    _ = (do
          let pre ← U i
          let bit ← U 1
          PMF.pure (pre, bit.getLsbD 0)) := by
        simp only [bind_unused]
    _ = (do
          let pre ← U i
          let b ← PMF.uniformOfFintype Bool
          PMF.pure (pre, b)) := by
        -- Convert `U 1` back via `bv_to_bool` (mapping to `U_Bool`).
        congr 1; funext pre
        rw [← U1_to_bool];
        simp only [zero_lt_one, BitVec.getLsbD_eq_getElem, bind_map_do]
        simp only [bv_to_bool]
        simp only [zero_lt_one, BitVec.getLsbD_eq_getElem, BitVec.ofNat_eq_ofNat, Equiv.coe_fn_mk]

/-- Core lemma: for the true uniform distribution `U L`, every next-bit predictor
    succeeds with probability exactly 1/2, regardless of the index `i` or algorithm `A`. -/
lemma PrDX_one_U_predictor_eq_half {L : ℕ} (i : Fin L)
    (A : BitVec i → PMF Bool) :
    PrDX_one (U L) (predictor_to_distinguisher i A) = 1 / 2 := by
  rw [← Pr_predict_success_eq_PrDX_one]
  calc
    Pr_predict_success (U L) i A
      = (Pr (do
          -- 1. Extract (prefix, bit) from x via map.
          let pair ← (U L).map (fun x => (x.extractLsb' (L - i) i, x.getLsbD (L - i - 1)))
          let a ← A pair.1
          PMF.pure (a == pair.2)
        )).toReal := by
          unfold Pr_predict_success
          congr 2
          simp only [PMF.map, Bind.bind]
          simp only [Function.comp_def]
          simp only [PMF.bind_bind]
          simp only [PMF.pure_bind]
    _ = (Pr (do
          -- 2. Replace the joint sample with two independent samples via U_map_pre_bit.
          let pair ← do
            let pre ← U i
            let b ← PMF.uniformOfFintype Bool
            PMF.pure (pre, b)
          let a ← A pair.1
          PMF.pure (a == pair.2)
        )).toReal := by
          congr 1
          rw [U_map_pre_bit i]
          simp only [bind_assoc]
    _ = (Pr (do
          let a ← (do
            let pre ← U i
            A pre)
          let b ← PMF.uniformOfFintype Bool
          PMF.pure (a == b)
        )).toReal := by
          congr 2
          simp only [bind_assoc]
          simp only [Bind.bind, PMF.pure_bind]
          congr; funext x
          rw [PMF.bind_comm]
    _ = ((1 / 2 : ENNReal)).toReal := by
          congr 1
          exact Pr_comparison_uniform_bit _
    _ = 1 / 2 := by norm_num


/-- Converse of Theorem 4.2: Pseudorandomness implies Next-Bit Unpredictability.
    If X is (t + t_extract, ε/2)-indistinguishable from U_L,
    then X is (t, ε)-next-bit unpredictable. -/
theorem pseudorandom_implies_unpredictable {L : ℕ} (X : PMF (BitVec L))
    (t : ℕ) (ε : NNReal) (t_extract : ℕ) :
    DistIndistinguishable X (U L) (t + t_extract) (ε / 2) →
    NextBitUnpredictable X t ε := by
  intro h_indist
  unfold NextBitUnpredictable
  intro i A tA htA

  -- Build a distinguisher D from the predictor A.
  let D := predictor_to_distinguisher i A
  let tD := tA + t_extract
  have htD : tD ≤ t + t_extract := Nat.add_le_add_right htA t_extract

  -- Apply the pseudorandomness hypothesis to D.
  have h_bound := h_indist D tD htD

  have h_eq1 : Pr_predict_success X i A = PrDX_one X D :=
    Pr_predict_success_eq_PrDX_one X i A
  have h_eq2 : PrDX_one (U L) D = 1 / 2 :=
    PrDX_one_U_predictor_eq_half i A

  rw [← h_eq1, h_eq2] at h_bound

  -- Align NNReal and ℝ division.
  have h_cast : ((ε / 2 : NNReal) : ℝ) = (ε : ℝ) / 2 := by
    push_cast
    rfl
  rw [h_cast] at h_bound

  -- |Pr_predict_success - 1/2| ≤ ε/2 implies Pr_predict_success ≤ 1/2 + ε/2.
  have h_abs := le_of_abs_le h_bound
  linarith

end ComputationalSecurity
