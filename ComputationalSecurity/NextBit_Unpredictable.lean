/-
  NextBit_Unpredictable.lean

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

  Key infrastructure (proved here):
    - castEquiv       : canonical equivalence BitVec n ≃ BitVec m when n = m.
    - tripleEquiv     : equivalence BitVec L ≃ BitVec i × BitVec 1 × BitVec (L-i-1)
                        splitting an L-bit vector into prefix, one bit, and suffix.
    - tripleEquiv_apply : characterizes tripleEquiv component-wise via extractLsb'/getLsbD.
    - U_map_pre_bit   : mapping a uniform L-bit sample to (prefix, bit) equals
                        independent sampling of the prefix and a uniform coin.

  Authors: Yasuaki Honda
-/
import ComputationalSecurity.DistInd
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise

namespace ComputationalSecurity

open PMF

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


/-- Canonical equivalence between `BitVec n` and `BitVec m` when `n = m`,
    given by `BitVec.cast`. -/
def castEquiv {n m : ℕ} (h : n = m) : BitVec n ≃ BitVec m where
  toFun x := x.cast h
  invFun x := x.cast h.symm
  left_inv x := by simp
  right_inv x := by simp

/-- Equivalence splitting a `BitVec L` into three independent parts:
    the upper `i` bits (prefix), one middle bit, and the lower `L-i-1` bits (suffix).
    This is the key structural decomposition underlying `U_map_pre_bit`. -/
def tripleEquiv {L : ℕ} (i : Fin L) :
    BitVec L ≃ BitVec i × BitVec 1 × BitVec (L - i - 1) :=
  calc BitVec L
    _ ≃ BitVec (i + (L - i)) := castEquiv (by omega)
    _ ≃ BitVec i × BitVec (L - i) := bitvec_equiv i (L - i)
    _ ≃ BitVec i × BitVec (1 + (L - i - 1)) :=
            Equiv.prodCongr (Equiv.refl _) (castEquiv (by omega))
    _ ≃ BitVec i × (BitVec 1 × BitVec (L - i - 1)) :=
            Equiv.prodCongr (Equiv.refl _) (bitvec_equiv 1 (L - i - 1))


/-- Characterizes `tripleEquiv` component-wise:
    the first component equals `extractLsb'` (the upper `i` bits),
    and the second component equals the single-bit encoding of `getLsbD`. -/
lemma tripleEquiv_apply {L : ℕ} (i : Fin L) (x : BitVec L) (pre : BitVec i) (b : Bool) :
    (pre = x.extractLsb' (L - i) i ∧ x.getLsbD (L - i - 1) = b) ↔
    ((tripleEquiv i x).1 = pre ∧ (tripleEquiv i x).2.1 = if b then 1 else 0) := by

  -- 1. The first component matches extractLsb'.
  have h_part1 : (tripleEquiv i x).1 = x.extractLsb' (L - i) i := by
    dsimp [tripleEquiv, Equiv.trans, bitvec_equiv, castEquiv, Equiv.prodCongr]
    apply BitVec.eq_of_getLsbD_eq; intro j
    simp only [BitVec.getLsbD_extractLsb']
    erw [BitVec.getLsbD_cast]
    · aesop
    · omega

  -- 2. The second component matches the 1-bit extraction.
  have h_part2 : (tripleEquiv i x).2.1 = x.extractLsb' (L - i - 1) 1 := by
    dsimp [tripleEquiv, Equiv.trans, bitvec_equiv, castEquiv, Equiv.prodCongr]
    apply BitVec.eq_of_getLsbD_eq; intro j
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast, Nat.lt_one_iff, zero_add]
    aesop

  -- 3. Equivalence between the Bool equality and the BitVec 1 equality.
  have h_bool : (x.getLsbD (L - i - 1) = b) ↔ (x.extractLsb' (L - i - 1) 1 = if b then 1 else 0) := by
    constructor
    · -- (→) の証明：b で場合分けし、両方のブランチを同時に simp で潰す
      intro h
      apply BitVec.eq_of_getLsbD_eq; intro j _
      have hj : j = 0 := by omega
      cases b <;> simp [hj, h]
    · -- (←) の証明：congrArg で 0番目のビットを取り出し、両ブランチを同時に潰す
      intro h
      have h0 := congrArg (fun v => BitVec.getLsbD v 0) h
      cases b <;> simp [zero_lt_one, BitVec.getLsbD_eq_getElem, BitVec.getElem_extractLsb', add_zero]
                        at h0 <;> exact h0

  -- 4. Combine the three facts.
  rw [h_part1, h_part2, ← h_bool]
  exact and_congr eq_comm Iff.rfl


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
    -- Step 1: Rewrite .map as a do-expression.
    _ = (do
          let x ← U L
          PMF.pure (x.extractLsb' (L - i) i, x.getLsbD (L - i - 1)))
        := by rfl  -- PMF.map unfolds to bind/pure by definition.
    -- Step 1.5: Rewrite the projection functions via tripleEquiv (U L is still one sample).
    _ = (do
          let x ← U L
          let pre := (tripleEquiv i x).1
          let b_vec := (tripleEquiv i x).2.1
          let rest := (tripleEquiv i x).2.2
          PMF.pure (pre, b_vec.getLsbD 0))
        := by congr 1; funext x; congr 1
              simp only [zero_lt_one, BitVec.getLsbD_eq_getElem, Prod.mk.injEq]
              have h := (tripleEquiv_apply i x (x.extractLsb' (L - i) i)
                        (x.getLsbD (L - i - 1))).mp ⟨rfl, rfl⟩
              -- h : (tripleEquiv i x).1 = x.extractLsb' (L-i) i
              --   ∧ (tripleEquiv i x).2.1 = if x.getLsbD (L-i-1) then 1 else 0
              obtain ⟨h1, h2⟩ := h
              constructor
              · exact h1.symm
              · rw [h2]
                cases x.getLsbD (L - i - 1) <;> rfl
    -- Step 2: Replace the single U L sample with three independent samples
    --          using the equivalence tripleEquiv and uniformOfFintype_eq_bind3_of_equiv.
    _ = (do
          let pre ← U i
          let b_vec ← U 1
          let rest ← U (L - i - 1)
          PMF.pure (pre, b_vec.getLsbD 0))
        := by unfold U
              rw [uniformOfFintype_eq_bind3_of_equiv (tripleEquiv i)]
              simp only [Equiv.invFun_as_coe, Bind.bind]
              simp only [zero_lt_one, BitVec.getLsbD_eq_getElem, bind_bind, PMF.pure_bind,
                Equiv.apply_symm_apply, bind_const]
              congr; funext a; congr; funext b;
              change PMF.map (Function.const _ (a, b[0])) (PMF.uniformOfFintype _)
                      = PMF.pure (a, b[0])
              exact PMF.map_const (uniformOfFintype (BitVec (L - ↑i - 1))) (a, b[0])
    -- Step 3: Drop the unused `rest` sample.
    _ = (do
          let pre ← U i
          let b_vec ← U 1
          PMF.pure (pre, b_vec.getLsbD 0))
        := by congr 1; ext pre
              congr 1; ext b_vec
              congr ; ext b; congr ;
              -- PMF.bind_const: (do let _ ← p; q) = q
              exact PMF.bind_const (U (L - i - 1)) (PMF.pure (pre, b.getLsbD 0))
    -- Step 4: Convert U 1 to the uniform distribution over Bool via boolEquiv.
    _ = (do
          let pre ← U i
          let b ← PMF.uniformOfFintype Bool
          PMF.pure (pre, b))
        := by congr 1; funext pre
              rw [U1_eq_map_boolEquiv]
              simp only [Bind.bind]
              simp only [zero_lt_one, BitVec.getLsbD_eq_getElem, PMF.bind_map]
              congr; funext b
              simp only [Function.comp_apply]
              congr
              cases b <;> rfl


/-- For any distribution `AnyDist` over `Bool`, guessing against an independent
    uniform coin flip succeeds with probability exactly 1/2. -/
lemma Pr_AnyDist_eq_uniform_coin (AnyDist : PMF Bool) :
    Pr (do
      let a ← AnyDist
      let x_bit ← PMF.uniformOfFintype Bool
      PMF.pure (a == x_bit)
    ) = 1 / 2 := by
  unfold Pr
  simp only [Bind.bind, PMF.bind_apply]
  rw [tsum_bool]
  simp only [tsum_bool]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, PMF.pure_apply]
  simp only [BEq.rfl, ↓reduceIte, mul_one, beq_true, Bool.true_eq_false, mul_zero, add_zero,
    beq_false, Bool.not_true, zero_add, one_div]
  rw [← add_mul, ← tsum_bool, PMF.tsum_coe, one_mul]

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
          -- 3. Flatten via bind_assoc to reach the form required by Pr_AnyDist_eq_uniform_coin.
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
          -- 4. Apply Pr_AnyDist_eq_uniform_coin.
          congr 1
          exact Pr_AnyDist_eq_uniform_coin _
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
