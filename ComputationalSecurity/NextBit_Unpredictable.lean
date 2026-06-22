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


/-- 長さが等しい BitVec 同士のキャスト同型 -/
def castEquiv {n m : ℕ} (h : n = m) : BitVec n ≃ BitVec m where
  toFun x := x.cast h
  invFun x := x.cast h.symm
  left_inv x := by simp
  right_inv x := by simp

/-- あなたのアイデア：BitVec L と 3つの BitVec の直積の完全な同型！ -/
def tripleEquiv {L : ℕ} (i : Fin L) :
    BitVec L ≃ BitVec i.val × BitVec 1 × BitVec (L - i.val - 1) :=
  calc BitVec L
    _ ≃ BitVec (i.val + (L - i.val)) := castEquiv (by omega)
    _ ≃ BitVec i.val × BitVec (L - i.val) := bitvec_equiv i.val (L - i.val)
    _ ≃ BitVec i.val × BitVec (1 + (L - i.val - 1)) :=
            Equiv.prodCongr (Equiv.refl _) (castEquiv (by omega))
    _ ≃ BitVec i.val × (BitVec 1 × BitVec (L - i.val - 1)) :=
            Equiv.prodCongr (Equiv.refl _) (bitvec_equiv 1 (L - i.val - 1))


lemma tripleEquiv_apply {L : ℕ} (i : Fin L) (x : BitVec L) (pre : BitVec i.val) (b : Bool) :
    (pre = x.extractLsb' (L - i.val) i.val ∧ x.getLsbD (L - i.val - 1) = b) ↔
    ((tripleEquiv i x).1 = pre ∧ (tripleEquiv i x).2.1 = if b then 1 else 0) := by

  -- 1. 第1成分が extractLsb' に一致することの証明
  have h_part1 : (tripleEquiv i x).1 = x.extractLsb' (L - i.val) i.val := by
    dsimp [tripleEquiv, Equiv.trans, bitvec_equiv, castEquiv, Equiv.prodCongr]
    apply BitVec.eq_of_getLsbD_eq; intro j
    simp only [BitVec.getLsbD_extractLsb']
    erw [BitVec.getLsbD_cast]
    · aesop
    · omega

  -- 2. 第2成分が 1ビットの抽出に一致することの証明
  have h_part2 : (tripleEquiv i x).2.1 = x.extractLsb' (L - i.val - 1) 1 := by
    dsimp [tripleEquiv, Equiv.trans, bitvec_equiv, castEquiv, Equiv.prodCongr]
    apply BitVec.eq_of_getLsbD_eq; intro j
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast, Nat.lt_one_iff, zero_add]
    aesop

  -- 3. Bool の等式と BitVec 1 の等式の同値性の証明
  have h_bool : (x.getLsbD (L - i.val - 1) = b) ↔ (x.extractLsb' (L - i.val - 1) 1 = if b then 1 else 0) := by
    constructor
    · -- (→) の証明：b で場合分けし、両方のブランチを同時に simp で潰す
      intro h
      apply BitVec.eq_of_getLsbD_eq; intro j _
      have hj : j = 0 := by omega
      cases b <;> simp [hj, h]
    · -- (←) の証明：congrArg で 0番目のビットを取り出し、両ブランチを同時に潰す
      intro h
      have h0 := congrArg (fun v => BitVec.getLsbD v 0) h
      cases b <;> simp [zero_lt_one, BitVec.getLsbD_eq_getElem, BitVec.getElem_extractLsb', add_zero] at h0 <;> exact h0

  -- 4. 組み上げ
  rw [h_part1, h_part2, ← h_bool]
  exact and_congr eq_comm Iff.rfl


lemma U_map_pre_bit {L : ℕ} (i : Fin L) :
    (U L).map (fun x => (x.extractLsb' (L - i.val) i.val, x.getLsbD (L - i.val - 1))) =
    (do
      let pre ← U i.val
      let b ← PMF.uniformOfFintype Bool
      PMF.pure (pre, b)
    ) := by
  calc
    (U L).map (fun x => (x.extractLsb' (L - i.val) i.val, x.getLsbD (L - i.val - 1)))
    -- Step 1: .map を do文に変換
    _ = (do
          let x ← U L
          PMF.pure (x.extractLsb' (L - i.val) i.val, x.getLsbD (L - i.val - 1)))
        := by rfl  -- PMF.map の定義展開（map = bind ∘ pure ∘ f、機械的）
    -- Step 1.5: x を tripleEquiv で分解した形に「書き換える」（まだ U L は1回のサンプリングのまま）
    _ = (do
          let x ← U L
          let pre := (tripleEquiv i x).1
          let b_vec := (tripleEquiv i x).2.1
          let rest := (tripleEquiv i x).2.2
          PMF.pure (pre, b_vec.getLsbD 0))
        := by congr 1; funext x; congr 1
              simp only [zero_lt_one, BitVec.getLsbD_eq_getElem, Prod.mk.injEq]
              have h := (tripleEquiv_apply i x (x.extractLsb' (L - i.val) i.val)
                        (x.getLsbD (L - i.val - 1))).mp ⟨rfl, rfl⟩
              -- h : (tripleEquiv i x).1 = x.extractLsb' (L - i.val) i.val ∧
              --     (tripleEquiv i x).2.1 = if x.getLsbD (L - i.val - 1) then 1 else 0
              obtain ⟨h1, h2⟩ := h
              constructor
              · exact h1.symm
              · rw [h2]
                cases x.getLsbD (L - i.val - 1) <;> rfl
    -- Step 2: U L が「pre, bit, rest の3分割」と同型であることを使い、3つの独立サンプリングに変形
    _ = (do
          let pre ← U i.val
          let b_vec ← U 1
          let rest ← U (L - i.val - 1)
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
    -- Step 3: 使われない rest を削除する
    _ = (do
          let pre ← U i.val
          let b_vec ← U 1
          PMF.pure (pre, b_vec.getLsbD 0))
        := by congr 1; ext pre
              congr 1; ext b_vec
              congr ; ext b; congr ;
              -- 確率の文法simp: let _ ← p; q = q
              exact PMF.bind_const (U (L - i.val - 1)) (PMF.pure (pre, b.getLsbD 0))
    -- Step 4: U 1 を Bool の一様分布に変換する
    _ = (do
          let pre ← U i.val
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
  -- 一様分布の確率(1/2)と、pureの確率(if文)を展開
  simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, PMF.pure_apply]
  -- Boolの比較 (false == false, false == true 等) と 0, 1 の掛け算を簡約
  -- これにより、各項が AnyDist a * (1/2 * 1 + 1/2 * 0) のように整理される
  simp only [BEq.rfl, ↓reduceIte, mul_one, beq_true, Bool.true_eq_false, mul_zero, add_zero,
    beq_false, Bool.not_true, zero_add, one_div]
  -- 式は AnyDist false * (1 / 2) + AnyDist true * (1 / 2) になるので、1/2 でくくる
  rw [← add_mul, ← tsum_bool, PMF.tsum_coe, one_mul]

/-- Lemma 2 (Core Lemma): Given the true uniform distribution U_L,
    the probability that any algorithm A correctly predicts the next bit is exactly 1/2. -/
lemma PrDX_one_U_predictor_eq_half {L : ℕ} (i : Fin L)
    (A : BitVec i → PMF Bool) :
    PrDX_one (U L) (predictor_to_distinguisher i A) = 1 / 2 := by
  rw [← Pr_predict_success_eq_PrDX_one]

  calc
    Pr_predict_success (U L) i A
      = (Pr (do
          -- 1. x への依存を map で (x_pre, x_bit) のペアに抽出する
          let pair ← (U L).map (fun x => (x.extractLsb' (L - i.val) i.val, x.getLsbD (L - i.val - 1)))
          let a ← A pair.1
          PMF.pure (a == pair.2)
        )).toReal := by
          -- ここは Pr_predict_success の定義と PMF.bind_map などで自明に変形できます
          unfold Pr_predict_success
          congr 2
          simp only [PMF.map, Bind.bind]
          simp only [Function.comp_def]
          simp only [PMF.bind_bind]
          simp only [PMF.pure_bind]
    _ = (Pr (do
          -- 2. あなたのアイデア！ペアを「独立な2つの分布」に置き換える
          let pair ← do
            let pre ← U i.val
            let b ← PMF.uniformOfFintype Bool
            PMF.pure (pre, b)
          let a ← A pair.1
          PMF.pure (a == pair.2)
        )).toReal := by
          -- ここで先ほどのペア抽出補題を適用します
          congr 1
          rw [U_map_pre_bit i]
          simp only [bind_assoc]
    _ = (Pr (do
          -- 3. あとはモナド結合則 (bind_assoc) で AnyDist の形に持ち込むだけ
          let a ← (do
            let pre ← U i.val
            A pre)
          let b ← PMF.uniformOfFintype Bool
          PMF.pure (a == b)
        )).toReal := by
          -- 結合則だけで通ります
          congr 2
          simp only [bind_assoc]
          simp only [Bind.bind, PMF.pure_bind]
          congr; funext x
          rw [PMF.bind_comm]
    _ = ((1 / 2 : ENNReal)).toReal := by
          -- 4. 独立して証明した AnyDist の補題を適用
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

  -- Construct a distinguisher D from the predicting algorithm A.
  let D := predictor_to_distinguisher i A
  let tD := tA + t_extract
  have htD : tD ≤ t + t_extract := Nat.add_le_add_right htA t_extract

  -- Apply the pseudorandomness assumption (DistIndistinguishable) to D.
  have h_bound := h_indist D tD htD

  have h_eq1 : Pr_predict_success X i A = PrDX_one X D :=
    Pr_predict_success_eq_PrDX_one X i A
  have h_eq2 : PrDX_one (U L) D = 1 / 2 :=
    PrDX_one_U_predictor_eq_half i A

  rw [← h_eq1, h_eq2] at h_bound

  -- Cast the division of NNReal to the division of ℝ to align the expressions.
  have h_cast : ((ε / 2 : NNReal) : ℝ) = (ε : ℝ) / 2 := by
    push_cast
    rfl
  rw [h_cast] at h_bound

  -- h_bound is |Pr_predict_success X i hi A - 1 / 2| ≤ ε / 2.
  -- We want to show Pr_predict_success X i hi A ≤ 1 / 2 + ε / 2.
  -- This trivially follows from the property of absolute value (x - y ≤ |x - y|) and linarith.
  have h_abs := le_of_abs_le h_bound
  linarith

end ComputationalSecurity
