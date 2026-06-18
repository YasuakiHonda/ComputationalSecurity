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
  -- Expand all definitions
  unfold Pr_predict_success PrDX_one predictor_to_distinguisher

  -- We want to prove equality inside `.toReal` and `Pr`.
  -- `congr 2` strips off `.toReal` and `Pr`, leaving the inner PMF Bool to be compared.
  congr 2

  -- Flatten the nested `bind` operations using monad associativity and `pure_bind`
  simp only [bind_assoc]

  -- Step inside the binders `fun x => ...` and `fun a => ...`
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

def bit0Set (n : Nat) (i : Fin n) : Finset (BitVec n) :=
  Finset.univ.filter (fun x => x.getLsbD i = false)

def bit1Set (n : Nat) (i : Fin n) : Finset (BitVec n) :=
  Finset.univ.filter (fun x => x.getLsbD i = true)

theorem card_bit0_eq_card_bit1 (n : Nat) (i : Fin n) :
    (bit0Set n i).card = (bit1Set n i).card := by
  have hmask : (BitVec.twoPow n i).getLsbD i = true := by
    simp only [BitVec.getLsbD_twoPow, decide_true, Bool.and_true, i.isLt]
  apply Finset.card_bij (fun x _ => x ^^^ BitVec.twoPow n i)
  · -- bit0Set → bit1Set
    intro x hx
    simp only [bit0Set, bit1Set, Finset.mem_filter, Finset.mem_univ,
               true_and] at *
    simp only [BitVec.getLsbD_xor, hx, hmask]
    simp
  · -- 単射
    intro x _ y _ h
    exact (BitVec.xor_left_inj _).mp h
  · -- 全射
    intro y hy
    refine ⟨y ^^^ BitVec.twoPow n i, ?_, ?_⟩
    · simp only [bit0Set, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [bit1Set, Finset.mem_filter, Finset.mem_univ,
                 true_and] at hy
      simp only [BitVec.getLsbD_xor, hy, hmask]
      simp only [bne_self_eq_false]
    · simp [BitVec.xor_assoc, BitVec.xor_self]

theorem pow_sub_one_eq (n x : Nat) (hnpos : 0 < n)
              (h : 2 ^ n = 2 * x) : 2 ^ (n - 1) = x := by
  -- 1. n が 0 かそれ以外（succ m）かで場合分けする
  cases n with
  | zero =>
    contradiction
  | succ m =>
    rw [Nat.pow_succ'] at h
    have : m+1-1=m := by exact Nat.add_sub_self_right m 1
    rw [this]
    omega

lemma card_bitVec_getLsb_eq (n : ℕ) (hnpos : 0 < n) (i : Fin n) (b : Bool) :
    (Finset.univ.filter (fun x : BitVec n => x.getLsbD i = b)).card = 2 ^ (n - 1) := by
  -- bit0Set ∪ bit1Set = univ、共通部分は空 を使う
  have hi : i<n := by exact i.isLt
  have huniv : bit0Set n i ∪ bit1Set n i = Finset.univ := by
    ext x
    simp [bit0Set, bit1Set, Finset.mem_filter]
  have hdisj : Disjoint (bit0Set n i) (bit1Set n i) := by
    simp [Finset.disjoint_filter, bit0Set, bit1Set]
  have hcard : (bit0Set n i).card = (bit1Set n i).card :=
    card_bit0_eq_card_bit1 n i
  have htotal : (Finset.univ : Finset (BitVec n)).card = 2 ^ n := by
    simp [card_bitvec]  -- 名前要確認
  -- b = false と b = true で場合分け
  cases b
  · -- b = false: card (bit0Set) = 2^(n-1)
    change (bit0Set n i).card = 2 ^ (n - 1)
    have := Finset.card_union_of_disjoint hdisj
    rw [huniv, htotal, ← hcard] at this
    have add_self_two_mul (a : Nat): a+a=2*a := by ring
    rw [add_self_two_mul] at this
    apply pow_sub_one_eq at this
    · rw [this]
    · exact hnpos
  · -- b = true: card (bit1Set) = 2^(n-1)
    change (bit1Set n i).card = 2 ^ (n - 1)
    have := Finset.card_union_of_disjoint hdisj
    rw [huniv, htotal, hcard] at this
    have add_self_two_mul (a : Nat): a+a=2*a := by ring
    rw [add_self_two_mul] at this
    apply pow_sub_one_eq at this
    · rw [this]
    · exact hnpos



lemma uniform_bitVec_getLsbD_uniform (n : ℕ) (hnpos : 0 < n) (i : Fin n) :
    (U n).map (fun x => x.getLsbD i.val) =
    PMF.uniformOfFintype Bool := by
  unfold U
  apply PMF.ext
  intro b
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply]
  -- tsum を Finset.sum に変換
  rw [tsum_fintype]
  simp only [Fintype.card_bool, Nat.cast_ofNat, card_bitvec]
  have h_one_mul_a: ((@Nat.cast ENNReal) (2 ^ n))⁻¹ = (↑(2 ^ n))⁻¹*(1:Nat) := by
    norm_cast
    rw [mul_one]
  have h_zero_mul_a: (0:ENNReal) = (↑(2 ^ n))⁻¹*0 := by rw [mul_zero]
  rw [h_one_mul_a, h_zero_mul_a]
  simp_rw [← mul_ite, ← Finset.mul_sum]
  have hsum : ∑ x : BitVec n, (if b = x.getLsbD i.val then 1 else 0 : ENNReal) = 2^(n-1) := by
    have : ∑ x : BitVec n, (if b = x.getLsbD i.val then 1 else 0 : ENNReal) =
         (Finset.univ.filter (fun x : BitVec n => x.getLsbD i.val = b)).card := by
      rw [← Finset.sum_boole]
      congr 1; ext x; simp [eq_comm]
    rw [this]
    conv_lhs =>
      arg 1; arg 1; arg 1; ext x;
    rw [card_bitVec_getLsb_eq n hnpos i]
    norm_cast
  simp only [Nat.cast_one]
  rw [hsum]
  have hn : n = (n - 1) + 1 := (Nat.succ_pred_eq_of_pos hnpos).symm
  nth_rw 1 [hn]
  rw [pow_succ]
  rw [ENNReal.mul_inv]
  · rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel]
    · rw [one_mul]
    · exact Ne.symm (NeZero.ne' (2 ^ (n - 1)))
    · exact Ne.symm (not_eq_of_beq_eq_false rfl)
  · left; exact Ne.symm (NeZero.ne' (2 ^ (n - 1)))
  · right; exact Ne.symm (NeZero.ne' 2)

/-- XORを用いた全単射。x と mask の XOR は自身の逆関数になる。 -/
def xor_equiv {L : ℕ} (mask : BitVec L) : BitVec L ≃ BitVec L where
  toFun x := x ^^^ mask
  invFun x := x ^^^ mask
  left_inv x := by simp [BitVec.xor_assoc, BitVec.xor_self]
  right_inv x := by simp [BitVec.xor_assoc, BitVec.xor_self]

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

/-- tripleEquiv による抽出は、extractLsb' や getLsbD の条件と完全に一致する -/
lemma tripleEquiv_apply {L : ℕ} (i : Fin L) (x : BitVec L) (pre : BitVec i.val) (b : Bool) :
    (pre = x.extractLsb' (L - i.val) i.val ∧ x.getLsbD (L - i.val - 1) = b) ↔
    ((tripleEquiv i x).1 = pre ∧ (tripleEquiv i x).2.1 = if b then 1 else 0) := by
  -- ここは bitvec_equiv の toFun の定義を展開するだけで証明可能です
  -- 1. 第1成分が extractLsb' に完全に一致することの証明
  have h_part1 : (tripleEquiv i x).1 = x.extractLsb' (L - i.val) i.val := by
    -- Equiv の合成を展開して計算を進める魔法のコマンド
    dsimp [tripleEquiv, Equiv.trans, bitvec_equiv, castEquiv, Equiv.prodCongr]
    -- あとは BitVec.eq_of_getLsbD_eq と simp で各ビットを比較すれば終わります
    apply BitVec.eq_of_getLsbD_eq
    intro j
    simp only [BitVec.getLsbD_extractLsb']
    erw [BitVec.getLsbD_cast]
    · aesop
    · omega

  -- 2. 第2成分が 1ビットの抽出に完全に一致することの証明
  have h_part2 : (tripleEquiv i x).2.1 = x.extractLsb' (L - i.val - 1) 1 := by
    dsimp [tripleEquiv, Equiv.trans, bitvec_equiv, castEquiv, Equiv.prodCongr]
    -- 同様に BitVec.eq_of_getLsbD_eq と simp [BitVec.getLsbD_extractLsb'] で終わります
    apply BitVec.eq_of_getLsbD_eq
    intro j
    simp only [BitVec.getLsbD_extractLsb']
    simp only [BitVec.getLsbD_cast]
    simp only [Nat.lt_one_iff, BitVec.getLsbD_extractLsb', zero_add]
    aesop

  -- 3. 1ビットの BitVec の等式と、Bool の等式の同値性の証明
  have h_bool : (x.getLsbD (L - i.val - 1) = b) ↔ (x.extractLsb' (L - i.val - 1) 1 = if b then 1 else 0) := by
    -- b が true か false かで場合分け (cases b) し、
    -- BitVec.eq_of_getLsbD_eq でインデックス j=0 のみを比較すれば証明できます
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat]
      constructor
      · intro h
        apply BitVec.eq_of_getLsbD_eq
        intro j h_j
        have hj : j = 0 := by omega
        simp [hj, h]
      · intro h
        have h0 := congrArg (fun v => BitVec.getLsbD v 0) h
        simp only [zero_lt_one, BitVec.getLsbD_eq_getElem, BitVec.getElem_extractLsb', add_zero,
          BitVec.getElem_zero] at h0
        exact h0
    · simp only [↓reduceIte, BitVec.ofNat_eq_ofNat]
      constructor
      · intro h
        apply BitVec.eq_of_getLsbD_eq
        intro j h_j
        have hj : j = 0 := by omega
        simp [hj, h]
      · intro h
        have h0 := congrArg (fun v => BitVec.getLsbD v 0) h
        simp only [zero_lt_one, BitVec.getLsbD_eq_getElem, BitVec.getElem_extractLsb', add_zero,
          BitVec.getElem_one, decide_true] at h0
        exact h0
  -- 4. 組み上げ：用意した3つの事実で右辺を書き換える
  rw [h_part1, h_part2, ← h_bool]
  -- 残るゴールは (pre = X ∧ Y = b) ↔ (X = pre ∧ Y = b) になる
  -- 左側の等式の左右が逆になっているだけなので、eq_comm で反転させて終了！
  exact and_congr eq_comm Iff.rfl


lemma card_bitVec_pre_bit (L : ℕ) (i : Fin L) (pre : BitVec i.val) (b : Bool) :
    (Finset.univ.filter (fun x : BitVec L =>
      pre = x.extractLsb' (L - i.val) i.val ∧
      x.getLsbD (L - i.val - 1) = b)).card = 2 ^ (L - i.val - 1) := by
  -- 1. 目標のサイズを持つ基準の集合(univ)のサイズに書き換える
  have h_target_card : (Finset.univ : Finset (BitVec (L - i.val - 1))).card = 2 ^ (L - i.val - 1) := by
    simp [card_bitvec]
  rw [← h_target_card]

  let b_vec : BitVec 1 := if b then 1 else 0

  -- 2. card_bij を使って「条件を満たす集合」と「下位ビットの集合」の全単射を構築する
  symm
  apply Finset.card_bij (fun s _ => (tripleEquiv i).symm (pre, b_vec, s))

  · -- [Well-definedness] 抽出した要素が対象集合 (univ) に含まれるか（自明）
    intro s _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [tripleEquiv_apply]
    simp [tripleEquiv]
    exact ite_cond_congr rfl

  · -- [Injectivity] 単射性: 下位ビットが等しいなら元の x も等しいことの証明
    intro s1 _ s2 _ h_eq
    have h_prod_eq : (pre, b_vec, s1) = (pre, b_vec, s2) := (tripleEquiv i).symm.injective h_eq
    injection h_prod_eq with _ h_rest
    injection h_rest with _ h_s

  · -- [Surjectivity] 全射性: 任意の下位ビット s に対し、条件を満たす x が存在することの証明
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [tripleEquiv_apply] at hx

    let s := (tripleEquiv i x).2.2
    use s
    refine ⟨Finset.mem_univ _, ?_⟩

    have h_reconstruct : (pre, b_vec, s) = tripleEquiv i x := by
      apply Prod.ext
      · exact hx.1.symm
      · apply Prod.ext
        · aesop
        · rfl
    rw [h_reconstruct]
    exact (tripleEquiv i).symm_apply_apply x

/-- U L を (x_pre, x_bit) のペアに map したものは、
    独立な U i.val と一様コイントス (U 1) の直積分布に完全に等しい -/
lemma U_map_pre_bit {L : ℕ} (i : Fin L) :
    (U L).map (fun x => (x.extractLsb' (L - i.val) i.val, x.getLsbD (L - i.val - 1))) =
    (do
      let pre ← U i.val
      let b ← PMF.uniformOfFintype Bool
      PMF.pure (pre, b)
    ) := by
  apply PMF.ext
  intro ⟨pre, b⟩
  simp only [PMF.map_apply, Bind.bind, PMF.bind_apply, PMF.pure_apply, PMF.uniformOfFintype_apply]
  rw [tsum_fintype]
  simp only [U, PMF.uniformOfFintype_apply, card_bitvec, Fintype.card_bool]
  -- LHS: (2^L)⁻¹ * #{x | extractLsb'=pre ∧ getLsbD=b}
  -- RHS: (2^i)⁻¹ * (2)⁻¹
  -- 必要: #{x : BitVec L | extractLsb'(L-i,i)=pre ∧ getLsbD(L-i-1)=b} = 2^(L-i-1)
  simp only [Prod.mk.injEq, Nat.cast_pow, Nat.cast_ofNat, tsum_bool]
  simp only [mul_ite, mul_one, mul_zero, tsum_fintype, ← Finset.mul_sum]

  have hcard : ∀ (b : Bool),
    ∑ x : BitVec L, (if pre = x.extractLsb' (L - i.val) i.val ∧
                          x.getLsbD (L - i.val - 1) = b
                      then ((2^L):ENNReal)⁻¹ else 0) = ((2^i.val))⁻¹ * 2⁻¹ := by
      intro b
      have h1: ((2 ^ L):ENNReal)⁻¹ = (2 ^ L)⁻¹ * 1 := by rw [mul_one]
      have h2: 0 = ((2 ^ L):ENNReal)⁻¹*0 := by rw [mul_zero]
      rw [h1, h2]
      simp only [← mul_ite, ← Finset.mul_sum]
      rw [show ∑ i_1 : BitVec L, (if pre = i_1.extractLsb' (L - i.val) i.val ∧
          i_1.getLsbD (L - i.val - 1) = b then (1:ENNReal) else 0) =
          ↑(Finset.univ.filter (fun x : BitVec L =>
            pre = x.extractLsb' (L - i.val) i.val ∧
            x.getLsbD (L - i.val - 1) = b)).card from by
        simp [← Finset.sum_boole]
        exact
          Fintype.sum_congr
            (fun a ↦
              if pre = BitVec.extractLsb' (L - ↑i) (↑i) a ∧ a.getLsbD (L - ↑i - 1) = b then 1
              else 0)
            (fun a ↦
              if pre = BitVec.extractLsb' (L - ↑i) (↑i) a ∧ a.getLsbD (L - ↑i - 1) = b then 1
              else 0)
            (congrFun rfl)]
      rw [card_bitVec_pre_bit L i pre b]
      push_cast
      have hL : L = i.val + 1 + (L - i.val - 1) := by omega
      have h_pow : (2 : ENNReal) ^ L =
            ((2 : ENNReal) ^ i.val * 2) * (2 : ENNReal) ^ (L - i.val - 1) := by
        symm
        calc ((2 : ENNReal) ^ i.val * 2) * (2 : ENNReal) ^ (L - i.val - 1)
          _ = ((2 : ENNReal) ^ i.val * (2 : ENNReal) ^ 1) * (2 : ENNReal) ^ (L - i.val - 1) := by
            rw [pow_one]
          _ = (2 : ENNReal) ^ (i.val + 1) * (2 : ENNReal) ^ (L - i.val - 1) := by rw [← pow_add]
          _ = (2 : ENNReal) ^ (i.val + 1 + (L - i.val - 1)) := by rw [← pow_add]
          _ = (2 : ENNReal) ^ L := by
                congr 1
                omega
      rw [h_pow]
      have h_inv : (((2 : ENNReal) ^ i.val * 2) * (2 : ENNReal) ^ (L - i.val - 1))⁻¹ =
                  ((2 : ENNReal) ^ i.val * 2)⁻¹ * ((2 : ENNReal) ^ (L - i.val - 1))⁻¹ := by
        apply ENNReal.mul_inv
        · left
          apply mul_ne_zero
          · exact ENNReal.pow_ne_zero (by norm_num) _
          · norm_num
        · left
          exact Ne.symm (not_eq_of_beq_eq_false rfl)
      rw [h_inv]
      rw [mul_assoc]
      have h_cancel : ((2 : ENNReal) ^ (L - i.val - 1))⁻¹ * (2 : ENNReal) ^ (L - i.val - 1) = 1 := by
        apply ENNReal.inv_mul_cancel
        · exact ENNReal.pow_ne_zero (by norm_num) _  -- 0 ではない
        · norm_num
      rw [h_cancel, mul_one]
      have h_inv2 : ((2 : ENNReal) ^ i.val * 2)⁻¹ = ((2 : ENNReal) ^ i.val)⁻¹ * 2⁻¹ := by
        apply ENNReal.mul_inv
        · left
          exact ENNReal.pow_ne_zero (by norm_num) _  -- 0 ではない
        · right
          exact Ne.symm (NeZero.ne' 2)
      rw [h_inv2]

  cases b
  · simp only [Bool.false_eq, and_true]
    simp only [Bool.true_eq_false, and_false, ↓reduceIte, add_zero, Finset.sum_ite_eq,
      Finset.mem_univ]
    -- ⊢ (∑ x, if pre = BitVec.extractLsb' (L - ↑i) (↑i) x ∧ x.getLsbD (L - ↑i - 1) = false then (2 ^ L)⁻¹ else 0) = (2 ^ ↑i)⁻¹ * 2⁻¹
    exact hcard false
  · simp only [Bool.true_eq, and_true]
    simp only [Bool.false_eq_true, and_false, ↓reduceIte, zero_add, Finset.sum_ite_eq,
      Finset.mem_univ]
    -- ⊢ (∑ x, if pre = BitVec.extractLsb' (L - ↑i) (↑i) x ∧ x.getLsbD (L - ↑i - 1) = true then (2 ^ L)⁻¹ else 0) = (2 ^ ↑i)⁻¹ * 2⁻¹
    exact hcard true

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
  rw [← add_mul, ← tsum_bool, tsum_coe, one_mul]

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
          simp only [bind_bind, PMF.pure_bind]
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
