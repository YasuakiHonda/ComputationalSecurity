import ComputationalSecurity.DistInd
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise

namespace ComputationalSecurity

open PMF

/-- A helper definition for the probability that algorithm A successfully predicts
    the (i+1)-th bit given the first i bits of a distribution X. -/
noncomputable def Pr_predict_success {L : ℕ}
    (X : PMF (BitVec L)) (i : Fin L) (A : BitVec i → PMF (BitVec 1)) : ℝ :=
  (Pr (do
    let x ← X
    let x_pre := x.extractLsb' (L - i) i
    let x_bit := x.extractLsb' (L - i - 1) 1
    let a ← A x_pre
    PMF.pure (a == x_bit)
  )).toReal

/-- Definition 4.5: (t, ε)-Next-Bit Unpredictability.
    A distribution X is next-bit unpredictable if no algorithm A with complexity ≤ t
    can predict the next bit with probability greater than 1/2 + ε/2 = 1/2 * (1 + ε). -/
def NextBitUnpredictable {L : ℕ} (X : PMF (BitVec L)) (t : ℕ) (ε : NNReal) : Prop :=
  ∀ (i : Fin L) (A : BitVec i → PMF (BitVec 1)) (tA : ℕ),
    tA ≤ t →
    Pr_predict_success X i A ≤ (1 / 2 : ℝ) + (ε : ℝ) / 2

/-- The distinguisher constructed from a predicting algorithm A.
    It returns 1 if A successfully predicts the (i+1)-th bit, and 0 otherwise. -/
noncomputable
def predictor_to_distinguisher {L : ℕ} (i : Fin L)
    (A : BitVec i → PMF (BitVec 1)) (x : BitVec L) : PMF Bit := do
  let x_pre := x.extractLsb' (L - i) i
  let x_bit := x.extractLsb' (L - i - 1) 1
  let a ← A x_pre
  PMF.pure (if a == x_bit then 1 else 0)

/-- Lemma 1: The probability of predicting success is equal to the probability
    that the constructed distinguisher D outputs 1. -/
lemma Pr_predict_success_eq_PrDX_one {L : ℕ} (X : PMF (BitVec L)) (i : Fin L)
    (A : BitVec i → PMF (BitVec 1)) :
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
  cases (a == x.extractLsb' (L - i - 1) 1)
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
    (PMF.uniformOfFintype (BitVec n)).map (fun x => x.getLsbD i.val) =
    PMF.uniformOfFintype Bool := by
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

/-- Lemma 2 (Core Lemma): Given the true uniform distribution U_L,
    the probability that any algorithm A correctly predicts the next bit is exactly 1/2. -/
lemma PrDX_one_U_predictor_eq_half {L : ℕ} (i : Fin L)
    (A : BitVec i → PMF (BitVec 1)) :
    PrDX_one (U L) (predictor_to_distinguisher i A) = 1 / 2 := by
  sorry


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
