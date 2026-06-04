import ComputationalSecurity.Defs
import ComputationalSecurity.DistInd
import Mathlib.Data.BitVec
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise

namespace ComputationalSecurity

instance (n : ℕ) : Fintype (BitVec n) :=
  Fintype.ofEquiv (Fin (2^n)) {
    toFun := BitVec.ofFin
    invFun := BitVec.toFin
    left_inv := fun _ => rfl
    right_inv := fun x => by cases x; rfl
  }

open PMF

/-!
# Theorem 4.1: PRG Sequential Extension

This file formalizes the construction of an L-bit PRG from a 1-bit PRG
using the sequential construction described in Prof. Yasunaga's textbook (Figure 4.2).
The security is proven via a hybrid argument.
-/

/-- BitVec (n+m) is equivalent to BitVec n × BitVec m via concat/split. -/
private def bitvec_equiv (n m : ℕ) : BitVec (n + m) ≃ BitVec n × BitVec m :=
  { toFun    := fun v => (v.extractLsb' m n, v.extractLsb' 0 m)
    invFun   := fun p => p.1 ++ p.2
    left_inv := fun v => by apply BitVec.eq_of_toNat_eq; simp
    right_inv := fun p => by
      ext1
      · simp [BitVec.extractLsb'_append_eq_left]
      · simp [BitVec.extractLsb'_append_eq_right] }

section Construction

variable {n : ℕ}

/--
Splits an (n+1)-bit vector into the upper 1 bit (output) and the lower n bits (next seed).
Defined via bitvec_equiv for easy reasoning.
-/
def split_next (v : BitVec (n + 1)) : BitVec 1 × BitVec n :=
  -- n+1 を 1+n と見なして、上位1ビットと下位nビットに分ける
  let v_aligned : BitVec (1 + n) := v.cast (by omega)
  let p := bitvec_equiv 1 n v_aligned
  (p.1, p.2)

/--
The executable recursive function for extending a 1-bit PRG to L-bits.
G_ext sequentially applies G, collecting 1 bit each time and passing the rest as a seed.
-/
def G_ext (G : BitVec n → BitVec (n + 1)) : (L : ℕ) → BitVec n → BitVec L
  | 0, _ => BitVec.zero 0
  | l + 1, s =>
    let res := G s
    let (bit, s_next) := split_next res
    bit ++ G_ext G l s_next |>.cast (by omega)

/-- The extended PRG function G' : {0,1}^n -> {0,1}^L. -/
def G' (G : BitVec n → BitVec (n + 1)) (L : ℕ) (s : BitVec n) : BitVec L :=
  G_ext G L s

/-- The distribution of the extended PRG G'. -/
noncomputable def G'_dist
    (G : BitVec n → BitVec (n + 1)) (L : ℕ) : PMF (BitVec L) :=
  (U n).map (G' G L)

end Construction

section Lemmas

/--
Indistinguishability is preserved under monadic bind if it holds for every choice
from the first distribution.
-/
lemma DistIndistinguishable_bind {α β : Type} [Fintype α] [Fintype β]
    (X : PMF α) (Y1 Y2 : α → PMF β) (t : ℕ) (ε : NNReal) :
    (∀ a, DistIndistinguishable (Y1 a) (Y2 a) t ε) →
    DistIndistinguishable (X >>= Y1) (X >>= Y2) t ε := by
  intro h_indist D tD h_tD
  unfold DistIndistinguishable at h_indist
  have h_linear (Y : α → PMF β) :
      PrDX_one (X >>= Y) D = ∑ a, (X a).toReal * (PrDX_one (Y a) D) := by
    unfold PrDX_one Pr
    simp only [bind_assoc]
    erw [PMF.bind_apply]
    simp only [tsum_fintype]
    rw [ENNReal.toReal_sum]
    · simp_rw [ENNReal.toReal_mul]
    · intro a _
      apply ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  rw [h_linear Y1, h_linear Y2, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    |∑ a, (X a).toReal * (PrDX_one (Y1 a) D - PrDX_one (Y2 a) D)|
      ≤ ∑ a, |(X a).toReal * (PrDX_one (Y1 a) D - PrDX_one (Y2 a) D)| := by
        apply Finset.abs_sum_le_sum_abs
      _ = ∑ a, (X a).toReal * |PrDX_one (Y1 a) D - PrDX_one (Y2 a) D| := by
        congr; funext a
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ ∑ a, (X a).toReal * (ε : ℝ) := by
          apply Finset.sum_le_sum; intro a _
          apply mul_le_mul_of_nonneg_left (h_indist a D tD h_tD) ENNReal.toReal_nonneg
      _ = (ε : ℝ) := by
          rw [← Finset.sum_mul]
          have h_tsum : ∑ a, X a = ∑' a, X a := (tsum_fintype _).symm
          rw [← ENNReal.toReal_sum]
          · rw [h_tsum, tsum_coe]; simp
          · intro a _; apply PMF.apply_ne_top

private lemma card_bitvec (n : ℕ) : Fintype.card (BitVec n) = 2^n := by
  have : Fintype.card (BitVec n) = Fintype.card (Fin (2^n)) :=
    Fintype.card_congr ⟨BitVec.toFin, BitVec.ofFin,
      fun x => by cases x; rfl, fun _ => rfl⟩
  simp [this]

private lemma tsum_append_eq (n m : ℕ) (c : BitVec (n + m)) (b1 : BitVec n) :
    ∑' b2 : BitVec m, (if b1 ++ b2 = c then 1 else 0 : ENNReal)
    = if b1 = c.extractLsb' m n then 1 else 0 := by
  rw [tsum_fintype]
  by_cases h : b1 = c.extractLsb' m n
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single (c.extractLsb' 0 m)]
    · simp [BitVec.extractLsb'_append_extractLsb']
    · intro b2 _ hne
      rw [if_neg]; intro heq; apply hne
      have := congr_arg (BitVec.extractLsb' 0 m) heq
      simp [BitVec.extractLsb'_append_eq_right] at this; exact this
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg h]
    apply Finset.sum_eq_zero; intro b2 _
    rw [if_neg]; intro heq; apply h
    have := congr_arg (BitVec.extractLsb' m n) heq
    simp [BitVec.extractLsb'_append_eq_left] at this; exact this

/-- Sampling (n+m) bits is equivalent to sampling n bits and then m bits concatenated. -/
lemma U_add_dist (n m : ℕ) :
    U (n + m) = (do let b1 ← U n; let b2 ← U m; return b1 ++ b2) := by
  change U (n + m) = (U n).bind (fun b1 => (U m).map (fun b2 => b1 ++ b2))
  apply PMF.ext; intro c
  simp only [U, PMF.uniformOfFintype_apply, PMF.bind_apply, PMF.map_apply, card_bitvec]
  simp_rw [ENNReal.tsum_mul_left]
  simp only [Nat.cast_pow, Nat.cast_ofNat, tsum_fintype]
  rw [Finset.sum_eq_single (c.extractLsb' m n)]
  · rw [Finset.sum_eq_single (c.extractLsb' 0 m)]
    · simp only [BitVec.extractLsb'_append_extractLsb', ↓reduceIte]
      rw [pow_add]
      apply ENNReal.mul_inv
        (Or.inl (ENNReal.pow_ne_zero (by norm_num) n))
        (Or.inr (ENNReal.pow_ne_zero (by norm_num) m))
    · intro b2 _ hne; rw [if_neg]; intro heq; apply hne
      have := congr_arg (BitVec.extractLsb' 0 m) heq
      simp [BitVec.extractLsb'_append_eq_right] at this; exact this.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b1 _ hne; simp; intro i; by_contra
    rw [this] at hne; exact hne BitVec.extractLsb'_append_eq_left.symm
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Summing over BitVec (n+m) equals the double sum over BitVec n and BitVec m. -/
private lemma sum_bitvec_split (n m : ℕ) {f : BitVec (n + m) → ENNReal} :
    ∑ v : BitVec (n + m), f v = ∑ v1 : BitVec n, ∑ v2 : BitVec m, f (v1 ++ v2) := by
  have key : ∑ v : BitVec (n + m), f v =
      ∑ p : BitVec n × BitVec m, f (p.1 ++ p.2) :=
    Fintype.sum_equiv (bitvec_equiv n m) _ _ (fun v => by simp [bitvec_equiv])
  rw [key, Fintype.sum_prod_type]

/-- BitVec (1+n) and BitVec (n+1) are equivalent via cast. -/
private def bitvec_add_comm_equiv (n : ℕ) : BitVec (1 + n) ≃ BitVec (n + 1) :=
  { toFun   := fun v => v.cast (by omega)
    invFun  := fun v => v.cast (by omega)
    left_inv  := fun v => by simp
    right_inv := fun v => by simp }

/-- Summing over BitVec (n+1) equals the double sum over BitVec 1 and BitVec n. -/
private lemma sum_bitvec_n_plus_one (n : ℕ) {f : BitVec (n + 1) → ENNReal} :
    ∑ v : BitVec (n + 1), f v
    = ∑ b1 : BitVec 1, ∑ b2 : BitVec n, f ((b1 ++ b2).cast (by omega)) := by
  calc ∑ v : BitVec (n + 1), f v
      = ∑ v : BitVec (1 + n), f (v.cast (by omega)) := by
          apply Fintype.sum_equiv (bitvec_add_comm_equiv n).symm
          intro v; simp [bitvec_add_comm_equiv]
    _ = ∑ b1 : BitVec 1, ∑ b2 : BitVec n, f ((b1 ++ b2).cast (by omega)) :=
          sum_bitvec_split 1 n

/-- split_next (b ++ s) = (b, s): splitting a concatenation recovers the parts.
    教科書の規約（MSBが収穫ビット）に合わせ、b を左側（先頭）に配置します。 -/
private lemma split_next_append (b : BitVec 1) (s : BitVec n) :
    split_next ((b ++ s).cast (by omega)) = (b, s) := by
  -- split_next の定義を展開して計算します
  unfold split_next
  -- bitvec_equiv 1 n の右逆写像の性質 (p.1 ++ p.2 をバラすと p.1 と p.2 に戻る) を使います
  simp only [BitVec.cast_cast]
  exact (bitvec_equiv 1 n).right_inv (b, s)

end Lemmas


section SecurityProof

variable {n : ℕ} (G : BitVec n → BitVec (n + 1)) (L : ℕ)

/--
The i-th Hybrid distribution H_i for the proof of Theorem 4.1.
H_i consists of (L-i) random bits followed by i PRG bits.
- Hybrid 0 = U_L
- Hybrid L = G' distribution
-/
noncomputable def Hybrid (i : ℕ) : PMF (BitVec L) :=
  if h : i <= L then
    do
      let u_pre ← U (L - i)      -- 前方は (L-i) ビットの乱数
      let seed ← U n
      let suffix := G' G i seed  -- 後方は i ビットのPRG出力
      return (u_pre ++ suffix).cast (by omega)
  else
    G'_dist G L -- デフォルト値（ここに来ることはない）

/--
  あなたの図にある関数 F。
  n+1 ビットの入力 v を split_next し、1ビット収穫し、
  残りの seed から k-1 ビットを G_ext で生成する。
-/
def F_step (G : BitVec n → BitVec (n + 1)) (k : ℕ) (v : BitVec (n + 1)) : BitVec k :=
  match k with
  | 0 => BitVec.zero 0
  | k' + 1 =>
    let (b, s_next) := split_next v
    -- b は 1 bit, G_ext は k' bit。合計 1 + k' = k bit。
    (b ++ G_ext G k' s_next).cast (by omega)

/-- G_ext の 1ステップ展開と F_step の定義が一致することを示す補題 -/
lemma G_prime_step_eq_F_step (s : BitVec n) (k : ℕ) :
    G' G (k + 1) s = F_step G (k + 1) (G s) := by
  unfold G' G_ext F_step
  simp only [split_next]

#check @BitVec.extractLsb'_append_extractLsb'
#check BitVec.cast_eq

lemma h_split_U (i L : Nat) (hL : i < L) : U (L - i) = do
      let pre ← U (L - (i + 1))
      let b   ← U 1
      return (pre ++ b).cast (by omega) := by
  let P := L - (i + 1)
  have h_len : L - i = P + 1 := by omega
  apply PMF.ext; intro x
  simp only [U, PMF.uniformOfFintype_apply, card_bitvec, Nat.cast_pow, Nat.cast_ofNat]
  simp only [Bind.bind, Pure.pure, PMF.bind_apply, PMF.pure_apply, tsum_fintype]
  simp only [U, PMF.uniformOfFintype_apply, card_bitvec]
  simp_rw [← Finset.mul_sum, ← mul_assoc]
  rw [← ENNReal.mul_inv]
  · norm_cast
    have : 2 ^ (L - (i + 1)) * 2 ^ 1 = 2^(L-i) := by aesop
    rw [this]
    have (a b : ENNReal) (hnez : a ≠ 0) (hnet : a ≠ ⊤ ): a = a * b ↔ b=1 := by
      constructor
      · intro h
        exact (ENNReal.mul_eq_left hnez hnet).mp (id (Eq.symm h))
      · intro h
        rw [h,mul_one]
    rw [this]
    · -- ⊢ ∑ x_1, ∑ x_2, ↑(if x = BitVec.cast ⋯ (x_1 ++ x_2) then 1 else 0) = 1
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      set x' := x.cast h_len with hx'
      rw [show x = x'.cast h_len.symm from by norm_cast]
      rw [Finset.sum_eq_single (x.extractLsb' 1 P)]
      · rw [Finset.sum_eq_single (x.extractLsb' 0 1)]
        · rw [if_pos]
          exact congrArg (BitVec.cast (by omega)) BitVec.extractLsb'_append_extractLsb' |>.symm
        · intro b _ hne
          simp
          intro heq
          apply hne
          have := congr_arg (BitVec.extractLsb' 0 1) heq
          erw [BitVec.extractLsb'_append_eq_right] at this
          exact this.symm
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro b _ hne
        apply Finset.sum_eq_zero
        intro b2 _
        simp
        intro heq
        apply hne
        have := congr_arg (BitVec.extractLsb' 1 P) heq
        erw [BitVec.extractLsb'_append_eq_left] at this
        exact this.symm
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [ENNReal.inv_ne_zero]
      exact ENNReal.natCast_ne_top (2 ^ (L - i))
    · rw [ENNReal.inv_ne_top]
      norm_cast
      exact NeZero.ne (2 ^ (L - i))
  · right; norm_num
  · right; norm_num

/-- Hybrid i を「共通の乱数prefix + U(n+1)からF_stepで生成」の形に書き換える -/
lemma step_equiv_random (hi : i < L) :
    Hybrid G L i = do
        let pre ← U (L - (i + 1))
        let v   ← U (n + 1)
        return (pre ++ F_step G (i + 1) v).cast (by omega) := by
  unfold Hybrid
  simp only [show i ≤ L from by omega, ↓reduceDIte]

  rw [h_split_U i L hi]
  -- do記法を展開して整理
  simp_rw [bind_assoc]
  apply PMF.ext; intro x
  erw [PMF.bind_apply, PMF.bind_apply]
  simp_rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply congr_fun _ x
  simp only [LawfulMonad.bind_pure_comp, LawfulMonad.pure_bind, DFunLike.coe_fn_eq]
  erw [← LawfulMonad.bind_pure_comp]
  simp_rw [← LawfulMonad.bind_pure_comp]
  apply PMF.ext; intro y
  erw [PMF.bind_apply, tsum_fintype]
  erw [PMF.bind_apply, tsum_fintype]
  rw [show (∑ a_1 : BitVec (n+1), _) = ∑ x : BitVec 1, ∑ a_1 : BitVec n, _
      from sum_bitvec_n_plus_one n]
  apply Finset.sum_congr rfl
  intro b _
  erw [PMF.bind_apply, tsum_fintype]
  simp only [show (Pure.pure : BitVec L → PMF (BitVec L)) = PMF.pure from rfl]
  simp only [PMF.pure_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hU : (U 1) b * (U n) x = (U (n+1)) (BitVec.cast (by omega) (b ++ x)) := by
    simp [U, PMF.uniformOfFintype_apply, card_bitvec, pow_add, mul_comm]
    rw [ENNReal.mul_inv]
    · left; norm_num
    · left; norm_num
  rw [← mul_assoc, hU]
  congr 1
  simp [F_step, split_next_append]
  congr 1
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_cast, BitVec.toNat_append, G']
  rw [Nat.shiftLeft_succ, Nat.shiftLeft_or_distrib , Nat.or_assoc]
  congr 1





/-- Hybrid (i+1) を「共通の乱数prefix + (U n).map GからF_stepで生成」の形に書き換える -/
lemma step_equiv_prg (hi : i < L) :
    Hybrid G L (i + 1) =
      do
        let pre ← U (L - (i + 1))
        let v   ← (U n).map G
        return (pre ++ F_step G (i + 1) v).cast (by omega) := by
  unfold Hybrid
  simp only [show i + 1 ≤ L from hi, ↓reduceDIte]
  -- G' G (i+1) s = F_step G (i+1) (G s) を使って書き換え
  simp_rw [G_prime_step_eq_F_step]
  congr 1
  funext pre
  simp_rw [PMF.map]
  apply PMF.ext
  intro x
  simp only [LawfulMonad.bind_pure_comp]
  change ((fun a ↦ BitVec.cast ⋯ (pre ++ F_step G (i + 1) (G a))) <$> U n) x =
       ((fun a ↦ BitVec.cast ⋯ (pre ++ F_step G (i + 1) a)) <$> (U n).map G) x
  erw [Functor.map_map]


/--
  Lemma: A single step of the hybrid argument for PRG extension.
-/
lemma Sequential_Extension_Step
    (n L : ℕ) (G : BitVec n → BitVec (n + 1)) (i : ℕ) (hi : i < L)
    (t : ℕ) (ε : NNReal) (cost_G : ℕ)
    (h_G_secure : DistIndistinguishable ((U n).map G) (U (n + 1)) (t + L * cost_G) (ε / L)) :
    DistIndistinguishable (Hybrid G L i) (Hybrid G L (i + 1)) t (ε / L) := by
  rw [step_equiv_random G L hi, step_equiv_prg G L hi]
  apply DistIndistinguishable_bind
  intro pre
  apply closure (tA := 0)
  rw [add_zero]
  rw [DistIndistinguishable_comm]
  intro D tD htD
  exact h_G_secure D tD (htD.trans (Nat.le_add_right t _))


/-- Theorem 4.1: PRG Sequential Extension Theorem. -/
theorem PRG_Sequential_Extension
    (n L : ℕ) (hL : L > 0)
    (G : BitVec n → BitVec (n + 1))
    (t : ℕ) (ε : NNReal) (cost_G : ℕ)
    (h_G_secure : DistIndistinguishable ((U n).map G) (U (n + 1)) (t + L * cost_G) (ε / L)) :
    DistIndistinguishable ((U n).map (G' G L)) (U L) t ε := by

  have h_end : U L = Hybrid G L 0 := by
    unfold Hybrid; simp [zero_le, Nat.sub_zero]
    apply PMF.ext; intro x
    simp only [Bind.bind, PMF.bind_apply, tsum_fintype]
    have h_inner (i : BitVec L) : ((fun _ : BitVec n => i) <$> U n) x = if i = x then 1 else 0 := by
      -- ここで erw を使って map の定義を展開します
      erw [PMF.map_apply]
      simp only [U, PMF.uniformOfFintype_apply, card_bitvec, Nat.cast_pow, Nat.cast_ofNat, tsum_fintype]
      erw [Finset.sum_const]
      simp [Finset.card_univ, smul_ite, nsmul_eq_mul, card_bitvec, Nat.cast_pow, Nat.cast_ofNat, ENNReal.mul_inv_cancel]
      simp_rw [eq_comm]
    simp only [h_inner]
    simp only [U, PMF.uniformOfFintype_apply, card_bitvec, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Finset.mul_sum]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b h_b hne
      simp [hne]
    · simp

  -- Hybrid L は PRGビットが L 個、乱数ビットが L-L = 0 個
  -- つまり、完全に G' (PRG) の分布と一致する
  have h_start : (U n).map (G' G L) = Hybrid G L L := by
    unfold Hybrid
    simp only [U, Std.le_refl, ↓reduceDIte, LawfulMonad.bind_pure_comp]
    simp only [Bind.bind,]
    apply PMF.ext; intro x
    simp only [PMF.map_apply, PMF.bind_apply, U, PMF.uniformOfFintype_apply, card_bitvec]
    -- BitVec (L - L) の要素は唯一つ (BitVec.zero (L - L)) しかないことを利用して和を解消
    simp only [Nat.cast_pow, Nat.cast_ofNat, tsum_fintype, tsub_self, pow_zero, Nat.cast_one,
      inv_one, one_mul]
    rw [Finset.sum_eq_single (BitVec.zero (L - L))]
    · simp only [BitVec.zero_eq]
      erw [PMF.map_apply, tsum_fintype]
      congr; funext a
      simp only [uniformOfFintype_apply, card_bitvec, Nat.cast_pow, Nat.cast_ofNat]
      congr
      apply BitVec.eq_of_toNat_eq
      simp
    · intro b h_b hne;
      absurd hne
      apply BitVec.eq_of_toNat_eq
      have h_lt := b.isLt
      -- 2^(L - L) = 2^0 = 1 なので、b.toNat < 1 となる
      have h_pow : 2 ^ (L - L) = 1 := by simp
      rw [h_pow] at h_lt
      have : b.toNat = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h_lt)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h

  rw [h_start, h_end]
  have : DistIndistinguishable (Hybrid G L L) (Hybrid G L 0) t ε ↔
         DistIndistinguishable (Hybrid G L 0) (Hybrid G L L) t ε := by
    unfold DistIndistinguishable
    simp_rw [abs_sub_comm] -- |a - b| = |b - a| を利用
  rw [this]

  -- ハイブリッド論法の推移律を適用
  -- 通常の transitivity 補題が |H_L - H_0| ≤ Σ |H_{i+1} - H_i| を示す形式であることを想定
  apply transitivity (Hybrid G L) L t ε hL
  intro i hi
  -- 各ステップ i において、Hybrid (i+1) と Hybrid i が ε/L 以内で区別不能であることを示す
  -- ※ Sequential_Extension_Step は「1つPRGビットを増やす」ステップを証明するはずなので
  --   (i+1) と i の関係を証明する形になります
  exact Sequential_Extension_Step n L G i hi t ε cost_G h_G_secure

end SecurityProof

end ComputationalSecurity
