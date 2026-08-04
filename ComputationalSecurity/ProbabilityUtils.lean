/-
  Shared probability utilities for computational security proofs.
  Reference: Textbook Chapter 3, "Computational Security".

  Provides the following building blocks used throughout the project:
    - Bit (= Fin 2): the two-element type representing a single bit.
    - randomBit: the uniform PMF over Bit.
    - Pr: the probability that a PMF Bool outputs true.
    - tsum_bit, randomBit_apply: basic lemmas about Bit and randomBit.
    - Pr_bind, Pr_compl: rewriting rules for Pr under bind and complement.
    - PMF.tsum_mul_le_one, PMF.tsum_mul_ne_top: boundedness lemmas for
      expected values of functions bounded by 1.
    - formula1: an ENNReal algebraic identity used in the Guessing Lemma proof.
    - Fintype (BitVec n): instance for finite type over n-bit vectors.
    - U: the uniform distribution over {0,1}^n.
    - card_bitvec: cardinality of BitVec n is 2^n.
    - tsum_append_eq: sum over BitVec m of indicator for concatenation equality.
    - U_add_dist: uniform distribution over n+m bits equals sequential sampling.
    - sum_bitvec_split: splitting a sum over BitVec (n+m) into a double sum.
    - bitvec_add_comm_equiv: equivalence swapping summation order for BitVec.
    - sum_bitvec_n_plus_one: splitting a sum over BitVec (n+1) into a double sum.
    - h_split_U: splitting U (L-i) into a prefix and a 1-bit suffix.
    - uniformOfFintype_map_equiv: uniform distribution is preserved under equivalences.
    - boolEquiv: equivalence Bool ≃ BitVec 1 via the least-significant bit.
    - U1_eq_map_boolEquiv: U 1 equals the uniform Bool distribution mapped via boolEquiv.
    - uniformOfFintype_prod_eq_bind: uniform distribution over α × β equals
      independent sampling of each component.
    - uniformOfFintype_eq_bind3_of_equiv: uniform distribution over α, given an
      equivalence α ≃ β × γ × δ, equals three independent binds.

  Authors: Yasuaki Honda
-/

import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.BitVec
import ComputationalSecurity.BVCryptGameLib

open BVCryptGame

export BVCryptGame (Bit)
-- abbrev Bit := Fin 2

open BigOperators

/-- The sum of a function over all bits (0 and 1) can be expressed
    as the sum of its values at 0 and 1. -/
theorem tsum_bit {f : Bit → ENNReal} : (∑' (b : Bit), f b) = f 0 + f 1 := by
  rw [tsum_fintype]
  rw [Fin.sum_univ_two]


export BVCryptGame (randomBit)

/-- The probability that `randomBit` outputs either 0 or 1 is 1/2. -/
theorem randomBit_apply (b : Bit) : randomBit b = 1/2 := by
  rw [randomBit, PMF.uniformOfFintype_apply]
  simp only [one_div, Fintype.card_fin, Nat.cast_two]

-- ============================================================
-- Pr and related lemmas
-- ============================================================

export BVCryptGame (Pr)
-- notation "Pr" => BVCryptGame.Pr
-- noncomputable def Pr := BVCryptGame.Pr
--attribute [simp] BVCryptGame.Pr

export BVCryptGame (Pr_bind)

export BVCryptGame (Pr_compl)

-- ============================================================
-- Boundedness lemmas for PMF expected values
-- ============================================================

/-- The expectation of a function bounded by 1 is itself bounded by 1.
    This is a general version of the 'probability is at most 1' principle. -/
lemma PMF.tsum_mul_le_one {α : Type*} (p : PMF α) (f : α → ENNReal) (hf : ∀ x, f x ≤ 1) :
    (∑' x, p x * f x) ≤ 1 := by
  calc (∑' x, p x * f x)
    -- For each term, p x * f x ≤ p x * 1 = p x.
    _ ≤ ∑' x, p x := by
      apply ENNReal.tsum_le_tsum
      exact fun a ↦ mul_le_of_le_one_right' (hf a)
    -- By definition of PMF, ∑' x, p x = 1.
    _ = 1         := p.tsum_coe

/-- A useful corollary: the expectation of any bounded function is never top (infinity). -/
lemma PMF.tsum_mul_ne_top {α : Type*} (p : PMF α) (f : α → ENNReal) (hf : ∀ x, f x ≤ 1) :
    (∑' x, p x * f x) ≠ ⊤ :=
  ne_top_of_le_ne_top (by norm_num) (p.tsum_mul_le_one f hf)

-- ============================================================
-- Algebraic identity for the Guessing Lemma
-- ============================================================

/-- Algebraic identity used in the Guessing Lemma proof.
    Rewrites the expression `1/2 * (1 - A) + 1/2 * B`
    as `1/2 + 1/2 * (B - A)`, reflecting the step
      Pr[correct guess] = 1/2 + 1/2 * (Pr[A outputs 1 | X 1] - Pr[A outputs 1 | X 0]).
    Requires `A ≤ 1`, `A ≤ B`, and `B ≠ ⊤` to handle `ENNReal` subtraction correctly. -/
lemma formula1 (A B : ENNReal)
    (hA : A ≤ 1) (hAB : A ≤ B) (hBnotT : B ≠ ⊤) :
    1/2 * (1 - A) + 1/2 * B = 1/2 + 1/2 * (B - A) := by
  have hAnotT : A ≠ ⊤ := ne_top_of_le_ne_top hBnotT hAB
  rw [← ENNReal.toReal_eq_toReal_iff'
    (ENNReal.Finiteness.add_ne_top
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.sub_ne_top (by norm_num)))
      (ENNReal.mul_ne_top (by norm_num) hBnotT))
    (ENNReal.Finiteness.add_ne_top (by norm_num)
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.sub_ne_top hBnotT)))]
  rw [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hA,
      ENNReal.toReal_mul, ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le hAB, ENNReal.toReal_div, ENNReal.toReal_one]
  · simp only [ENNReal.toReal_ofNat, one_div]; ring
  · exact hBnotT
  · norm_num
  · exact ENNReal.mul_ne_top (by norm_num) (ENNReal.sub_ne_top hBnotT)
  · norm_num
  · exact ENNReal.mul_ne_top (by norm_num) (ENNReal.sub_ne_top (by norm_num))
  · exact ENNReal.mul_ne_top (by norm_num) hBnotT

-- ============================================================
-- BitVec Fintype instance and uniform distribution
-- ============================================================

namespace ComputationalSecurity

open PMF

export BVCryptGame (U)

-- ============================================================
-- BitVec combinatorial lemmas
-- ============================================================


export BVCryptGame (card_bitvec)


/-- The sum over `b2 : BitVec m` of `if b1 ++ b2 = c then 1 else 0`
    equals 1 iff `b1` matches the high bits of `c`, else 0. -/
lemma tsum_append_eq (n m : ℕ) (c : BitVec (n + m)) (b1 : BitVec n) :
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

/- Sampling `n+m` uniform bits equals sampling `n` bits then `m` bits and concatenating. -/
export BVCryptGame(U_add_dist)

/-- A sum over `BitVec (n+m)` equals the double sum over `BitVec n` and `BitVec m`. -/
lemma sum_bitvec_split (n m : ℕ) {f : BitVec (n + m) → ENNReal} :
    ∑ v : BitVec (n + m), f v = ∑ v1 : BitVec n, ∑ v2 : BitVec m, f (v1 ++ v2) := by
  have key : ∑ v : BitVec (n + m), f v =
      ∑ p : BitVec n × BitVec m, f (p.1 ++ p.2) :=
    Fintype.sum_equiv (bv_split n m) _ _ (fun v => by simp [bv_split])
  rw [key, Fintype.sum_prod_type]

/- Equivalence swapping the summation order for `BitVec (1+n)` and `BitVec (n+1)`. -/
export BVCryptGame (bitvec_add_comm_equiv)
export BVCryptGame (bv_one_add_comm_equiv)

/-- A sum over `BitVec (n+1)` equals the double sum over `BitVec 1` and `BitVec n`. -/
lemma sum_bitvec_n_plus_one (n : ℕ) {f : BitVec (n + 1) → ENNReal} :
    ∑ v : BitVec (n + 1), f v
    = ∑ b1 : BitVec 1, ∑ b2 : BitVec n, f ((b1 ++ b2).cast (by omega)) := by
  calc ∑ v : BitVec (n + 1), f v
      = ∑ v : BitVec (1 + n), f (v.cast (by omega)) := by
          apply Fintype.sum_equiv (bitvec_add_comm_equiv n).symm
          intro v; simp [bitvec_add_comm_equiv]
          congr
    _ = ∑ b1 : BitVec 1, ∑ b2 : BitVec n, f ((b1 ++ b2).cast (by omega)) :=
          sum_bitvec_split 1 n

/- Splitting U (L-i) into a `(L-i-1)`-bit prefix and a 1-bit suffix. -/
export BVCryptGame(h_split_U)

/- The uniform distribution over `α` is preserved under any equivalence `e : α ≃ β`:
    mapping by `e` yields the uniform distribution over `β`. -/
export BVCryptGame (uniformOfFintype_map_equiv)

/- Equivalence between `Bool` and `BitVec 1` via the least-significant bit:
    `true` maps to `1#1` and `false` maps to `0#1`. -/
abbrev boolEquiv := bv_to_bool.symm

/-- `boolEquiv` applied to the bit extracted via `getLsbD 0` recovers the original `BitVec 1`.
Bridges the definitional equality between `boolEquiv.symm` and `BitVec.getLsbD 0` into a
syntactically usable simp lemma. -/
@[simp] theorem boolEquiv_apply_getLsbD (v : BitVec 1) :
    bv_to_bool.symm (v.getLsbD 0) = v := Equiv.apply_symm_apply bv_to_bool.symm v

/-- The uniform distribution `U 1` over `BitVec 1` equals the uniform distribution
    over `Bool` mapped through `boolEquiv`. -/
lemma U1_eq_map_boolEquiv :
    U 1 = (PMF.uniformOfFintype Bool).map boolEquiv := by
  unfold U
  rw [@uniformOfFintype_map_equiv]


export BVCryptGame(U1_getLsbD_eq_uniformBool)

/-- The uniform distribution over a product type `α × β` equals independent sampling:
    first draw `a` uniformly from `α`, then draw `b` uniformly from `β`.
    This is the fundamental decomposition underlying `uniformOfFintype_eq_bind3_of_equiv`. -/
lemma uniformOfFintype_prod_eq_bind {α β : Type*}
        [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    PMF.uniformOfFintype (α × β) =
      (PMF.uniformOfFintype α).bind (fun a => (PMF.uniformOfFintype β).map (Prod.mk a)) := by
  apply PMF.ext
  intro ⟨a, b⟩
  rw [PMF.bind_apply]
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply]
  rw [tsum_fintype]
  rw [Finset.sum_eq_single a]
  · simp only [Fintype.card_prod]
    rw [tsum_fintype, Finset.sum_eq_single b]
    · push_cast
      rw [ENNReal.mul_inv]
      · simp only [↓reduceIte]
      · simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
        ENNReal.natCast_ne_top, or_self]
      · simp only [ne_eq, ENNReal.natCast_ne_top, not_false_eq_true, Nat.cast_eq_zero,
        Fintype.card_ne_zero, or_self]
    · intro b' _ hne
      simp only [Prod.mk.injEq, true_and, ite_eq_right_iff, ENNReal.inv_eq_zero,
        ENNReal.natCast_ne_top, imp_false]
      exact Ne.intro (id (Ne.symm hne))
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a' _ hne
    simp only [tsum_fintype]
    simp only [Prod.mk.injEq, mul_eq_zero, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top,
      Finset.sum_eq_zero_iff, Finset.mem_univ, ite_eq_right_iff, imp_false, not_and, forall_const,
      forall_apply_eq_imp_iff, false_or]
    exact Ne.intro (id (Ne.symm hne))
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Given an equivalence `e : α ≃ β × γ × δ`, the uniform distribution over `α`
    equals three nested independent binds over `β`, `γ`, and `δ`.
    Proved by applying `uniformOfFintype_map_equiv` and `uniformOfFintype_prod_eq_bind` twice,
    without descending to `tsum`. -/
lemma uniformOfFintype_eq_bind3_of_equiv {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Nonempty α] [Nonempty β] [Nonempty γ] [Nonempty δ]
    (e : α ≃ β × γ × δ) :
    PMF.uniformOfFintype α =
      (PMF.uniformOfFintype β).bind (fun b =>
        (PMF.uniformOfFintype γ).bind (fun c =>
          (PMF.uniformOfFintype δ).bind (fun d =>
            PMF.pure (e.invFun (b, c, d))))) := by
  rw [← uniformOfFintype_map_equiv e.symm]
  rw [uniformOfFintype_prod_eq_bind (α := β) (β := γ × δ)]
  simp only [uniformOfFintype_prod_eq_bind (α := γ) (β := δ)]
  simp only [PMF.map, PMF.map]
  simp only [bind_bind, Function.comp_apply, PMF.pure_bind, Equiv.invFun_as_coe]




end ComputationalSecurity
