import Mathlib.Data.BitVec
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# BVCryptGameLib

A library for high-level game-based cryptographic proofs using BitVec and PMFs.
This library avoids low-level tsum/sum calculations by using isomorphisms (Equiv).
-/

noncomputable section

namespace BVCryptGame

open PMF

/-! ### Layer 1: BitVec Structural Layer (Equivalences) -/

/-- BitVec 0 is equivalent to the Unit type. -/
def bv_0_equiv_unit : BitVec 0 ≃ Unit where
  toFun _ := ()
  invFun _ := 0#0
  left_inv v := by
    apply BitVec.eq_of_toNat_eq
    have h := v.isLt
    simp at h
    rw [h, BitVec.toNat_zero]
  right_inv _ := rfl

/-- BitVec 0 is a Subsingleton (contains only one element). -/
instance : Subsingleton (BitVec 0) :=
  Equiv.subsingleton bv_0_equiv_unit


/-- `BitVec n` is a finite type with `2^n` elements. -/
instance (n : ℕ) : Fintype (BitVec n) :=
  Fintype.ofEquiv (Fin (2^n)) (BitVec.equivFin.symm.toEquiv)


/-- The cardinality of `BitVec n` is `2^n`. -/
@[simp] theorem card_bitvec (n : ℕ) : Fintype.card (BitVec n) = 2^n := by
  have : Fintype.card (BitVec n) = Fintype.card (Fin (2^n)) :=
        Fintype.ofEquiv_card BitVec.equivFin.symm.toEquiv
  simp only [this, Fintype.card_fin]

/-- `BitVec n` is always inhabited (e.g., by the zero vector). -/
instance (n : ℕ) : Nonempty (BitVec n) := ⟨BitVec.zero n⟩

/-- Canonical equivalence between `BitVec n` and `BitVec m` when `n = m`. -/
def bv_cast_equiv {n m : ℕ} (h : n = m) : BitVec n ≃ BitVec m where
  toFun x := x.cast h
  invFun x := x.cast h.symm
  left_inv x := by simp
  right_inv x := by simp

/-- `BitVec (1+n) ≃ BitVec (n+1)`. Deprecated: use `bitvec_add_comm_equiv` instead. -/
def bv_one_add_comm_equiv (n : ℕ) : BitVec (1 + n) ≃ BitVec (n + 1) := @bv_cast_equiv (1+n) (n+1) (by omega)
abbrev bitvec_add_comm_equiv := bv_one_add_comm_equiv

/-- Any BitVec with length (L - L) is also a Subsingleton.
    This is essential for the boundary cases in hybrid arguments. -/
instance (L : ℕ) : Subsingleton (BitVec (L - L)) :=
  Equiv.subsingleton (bv_cast_equiv (Nat.sub_self L))

/-- Splitting `BitVec (n + m)` into `BitVec n × BitVec m` using MSB and LSB. -/
def bv_split (n m : ℕ) : BitVec (n + m) ≃ BitVec n × BitVec m where
  toFun v := (v.extractLsb' m n, v.extractLsb' 0 m)
  invFun p := p.1 ++ p.2
  left_inv := fun v => by apply BitVec.eq_of_toNat_eq
                          simp only [BitVec.extractLsb'_append_extractLsb']
  right_inv := fun p => by
    ext1
    · simp [BitVec.extractLsb'_append_eq_left]
    · simp [BitVec.extractLsb'_append_eq_right]

abbrev bitvec_equiv := bv_split

/-- Splitting `BitVec L` into `BitVec i × BitVec (L - i)` for `i < L`. -/
def bv_split_i {L : ℕ} (i : Fin (L + 1)) : BitVec L ≃ BitVec i × BitVec (L - i) := by
  trans BitVec (i + (L - i))
  · exact bv_cast_equiv (by omega)
  trans BitVec i × BitVec (L - i)
  · exact bv_split i (L - i)
  rfl

/-- Joining `BitVec n` and `BitVec m` into `BitVec (n + m)`. -/
def bv_join (n m : ℕ) : BitVec n × BitVec m ≃ BitVec (n + m) :=
  (bv_split n m).symm

/-- Joining `BitVec i` and `BitVec (L - i)` into `BitVec L`. -/
def bv_join_i {L : ℕ} (i : Fin (L + 1)) : BitVec i × BitVec (L - i) ≃ BitVec L :=
  (bv_split_i i).symm

/-- Splitting `BitVec (n + m + k)` into three parts. -/
def bv_split3 (n m k : ℕ) : BitVec (n + m + k) ≃ BitVec n × BitVec m × BitVec k := by
  -- Step 1: Fix the parenthesis ( (n+m)+k to n+(m+k) )
  trans BitVec (n + (m + k))
  · exact bv_cast_equiv (Nat.add_assoc n m k)
  -- Step 2: Split the first part ( n+(m+k) to n × (m+k) )
  trans BitVec n × BitVec (m + k)
  · exact bv_split n (m + k)
  -- Step 3: Split the second part ( n × (m+k) to n × (m × k) )
  · exact Equiv.prodCongr (Equiv.refl _) (bv_split m k)

/-- Joining three BitVecs into one. -/
def bv_join3 (n m k : ℕ) : BitVec n × BitVec m × BitVec k ≃ BitVec (n + m + k) :=
  (bv_split3 n m k).symm

/-- Split a BitVec into prefix (i bits), a single bit, and suffix (L-i-1 bits).
    This is specifically designed for hybrid arguments. -/
def bv_split3_i {L : ℕ} (i : Fin L) :
    BitVec L ≃ BitVec i × BitVec 1 × BitVec (L - i - 1) := by
  trans BitVec (i + 1 + (L - i - 1))
  · exact bv_cast_equiv (by omega)
  trans BitVec i × BitVec 1 × BitVec (L - i - 1)
  · exact bv_split3 i 1 (L - i - 1)
  rfl

/-- The join version of bv_split3_i. -/
def bv_join3_i {L : ℕ} (i : Fin L) :
    BitVec i × BitVec 1 × BitVec (L - i - 1) ≃ BitVec L:= (bv_split3_i i).symm

theorem bv_split3_i_proj_pre {L : ℕ} (i : Fin L) (x : BitVec L) :
  (bv_split3_i i x).1 = x.extractLsb' (L - i) i := by
  unfold bv_split3_i bv_split3 bv_split bv_cast_equiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast]
  congr; omega

theorem bv_split3_i_proj_bit {L : ℕ} (i : Fin L) (x : BitVec L) :
  (bv_split3_i i x).2.1 = x.extractLsb' (L - i - 1) 1 := by
  unfold bv_split3_i bv_split3 bv_split bv_cast_equiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast]

/-- Bridge between BitVec 1 and Bool for the middle bit. -/
theorem bv_split3_i_proj_bool {L : ℕ} (i : Fin L) (x : BitVec L) :
  (bv_split3_i i x).2.1.getLsbD 0 = x.getLsbD (L - i - 1) := by
  rw [bv_split3_i_proj_bit]
  simp only [zero_lt_one, BitVec.getLsbD_eq_getElem, BitVec.getElem_extractLsb', add_zero]

/-- The suffix `BitVec (L - i)` obtained by `bv_split_i` at `i.castSucc`, viewed as a
    joined `(bit, shorter-suffix)` pair via the length-matching cast. -/
noncomputable def suf_as_bit_suf {L : ℕ} (i : Fin L) :
    BitVec (L - (i.castSucc : Fin (L+1))) ≃ BitVec 1 × BitVec (L - i - 1) :=
  (bv_cast_equiv (by simp only [Fin.val_castSucc]; omega)).trans (bv_split 1 (L - i - 1))

/-- Compatibility between `bv_split_i` (at `i.castSucc`) and `bv_split3_i` (at `i`).
    The sole place where the two splitting schemes are reconciled bit-by-bit. -/
lemma bv_split_i_castSucc_eq_split3_i {L : ℕ} (i : Fin L)
    (p : BitVec i) (b : BitVec 1) (s : BitVec (L - i - 1)) :
    (bv_split_i (i.castSucc : Fin (L + 1))).symm (p, (suf_as_bit_suf i).symm (b, s)) =
    (bv_split3_i i).symm (p, b, s) := by
  apply BitVec.eq_of_toNat_eq
  unfold bv_split_i suf_as_bit_suf bv_split3_i bv_split3 bv_split bv_cast_equiv
  simp only [Equiv.symm_trans_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Equiv.coe_fn_symm_mk]
  simp only [BitVec.toNat_cast, BitVec.toNat_append]
  simp only [Fin.val_castSucc, Equiv.coe_refl, Prod.map_apply, id_eq, BitVec.toNat_append]
  erw [BitVec.toNat_append, BitVec.toNat_cast, BitVec.toNat_append]
  · have h_exp : 1 + (L - i - 1) = L - (i : ℕ) := by omega
    rw [h_exp]
  · rfl

/-- Corollary: the prefix component agrees between the two-way split (at i.castSucc)
    and the three-way split (at i). Derived purely from `bv_split_i_castSucc_eq_split3_i`
    via `Equiv` manipulation — no bit-level reasoning needed here. -/
lemma bv_split_i_castSucc_fst_eq_split3_i_fst {L : ℕ} (i : Fin L) (x : BitVec L) :
    (bv_split_i (i.castSucc : Fin (L + 1)) x).1 = (bv_split3_i i x).1 := by
  have h := bv_split_i_castSucc_eq_split3_i i
    (bv_split3_i i x).1 (bv_split3_i i x).2.1 (bv_split3_i i x).2.2
  simp only [Prod.mk.eta, Equiv.symm_apply_apply] at h
  -- h : (bv_split_i i_curr).symm ((bv_split3_i i x).1, (suf_as_bit_suf i).symm (...)) = x
  have h2 := congrArg (bv_split_i (i.castSucc : Fin (L + 1))) h
  rw [Equiv.apply_symm_apply] at h2
  exact congrArg Prod.fst h2.symm

/-- The prefix `BitVec (i+1)` obtained by `bv_split_i` at `i.succ`, viewed as a
    joined `(shorter-prefix, bit)` pair via the length-matching cast. -/
noncomputable def pre_as_pre_bit {L : ℕ} (i : Fin L) :
    BitVec ((i.succ : Fin (L+1)) : ℕ) ≃ BitVec i × BitVec 1 :=
  (bv_cast_equiv (by simp only [Fin.val_succ])).trans (bv_split i 1)

/-- Compatibility between the two-way split `bv_split_i` (at i.succ) and the
    three-way split `bv_split3_i` (at i): joining the prefix and the bit from
    `bv_split3_i` agrees with the prefix component of `bv_split_i` at i+1.
    This is the mirror image of `bv_split_i_castSucc_eq_split3_i`. -/
lemma bv_split_i_succ_eq_split3_i {L : ℕ} (i : Fin L)
    (p : BitVec i) (b : BitVec 1) (s : BitVec (L - i - 1)) :
    (bv_split_i (i.succ : Fin (L + 1))).symm ((pre_as_pre_bit i).symm (p, b), s) =
    (bv_split3_i i).symm (p, b, s) := by
  apply BitVec.eq_of_toNat_eq
  unfold bv_split_i pre_as_pre_bit bv_split3_i bv_split3 bv_split bv_cast_equiv
  simp only [Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.refl_symm, Equiv.refl_apply, Equiv.coe_fn_symm_mk]
  erw [BitVec.toNat_append, BitVec.toNat_cast, BitVec.toNat_append]
  simp only [Fin.val_succ, Equiv.coe_refl, Prod.map_apply, id_eq, BitVec.cast_cast,
    BitVec.toNat_cast, BitVec.toNat_append]
  generalize hp : p.toNat = pn
  generalize hb : b.toNat = bn
  generalize hs : s.toNat = sn
  have h_exp : L - (↑i + 1) = L - ↑i - 1 := by omega
  rw [h_exp, Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add, Nat.or_assoc]

/-- Corollary: the prefix component of the two-way split (at i.succ) agrees with
    the joined (prefix, bit) pair from the three-way split (at i), via `pre_as_pre_bit`.
    Derived purely from `bv_split_i_succ_eq_split3_i` via `Equiv` manipulation. -/
lemma bv_split_i_succ_fst_eq_pre_as_pre_bit_symm {L : ℕ} (i : Fin L) (x : BitVec L) :
    (bv_split_i (i.succ : Fin (L + 1)) x).1 =
    (pre_as_pre_bit i).symm ((bv_split3_i i x).1, (bv_split3_i i x).2.1) := by
  have h := bv_split_i_succ_eq_split3_i i
    (bv_split3_i i x).1 (bv_split3_i i x).2.1 (bv_split3_i i x).2.2
  simp only [Prod.mk.eta, Equiv.symm_apply_apply] at h
  have h2 := congrArg (bv_split_i (i.succ : Fin (L + 1))) h
  rw [Equiv.apply_symm_apply] at h2
  rw [eq_comm] at h2
  exact congrArg Prod.fst h2

/-- Equivalence between `BitVec 1` and `Bool`. -/
def bv_to_bool : BitVec 1 ≃ Bool where
  toFun v := v.getLsbD 0
  invFun b := if b then 1 else 0
  left_inv v := by
    -- 1. Apply extensionality on `BitVec` bits.
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    -- 2. Length is 1, so `j = 0`.
    have hj0 : j = 0 := by omega
    simp [hj0]
    -- 3. Case on `v.getLsbD 0`.
    cases v.getLsbD 0 <;> aesop
  right_inv b := by cases b <;> rfl

/-- Bit is defined as Fin 2, representing the elements {0, 1}. -/
abbrev Bit := Fin 2

/-- Explicitly naming the bits for clarity. -/
def Bit.zero : Bit := 0
def Bit.one : Bit := 1

/-- Equivalence between BitVec 1 and Bit (Fin 2). -/
def bv_to_bit : BitVec 1 ≃ Bit := by
  exact BitVec.equivFin.toEquiv

/-- Equivalence between Bool and Bit.
    true maps to 1, false maps to 0. -/
def bool_to_bit : Bool ≃ Bit where
  toFun b := if b then 1 else 0
  invFun i := if i == 1 then true else false
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl


/-! ### Layer 2: General PMF Infrastructure -/

namespace PMF
/-- Independent product of two probability mass functions. -/
def prod {α β : Type*} (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind (fun a => q.map (Prod.mk a))
end PMF

/-- Theorem: Uniformity is preserved under isomorphism (mapping an Equiv). -/
theorem U_map_equiv {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (e : α ≃ β) :
  (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  apply PMF.ext
  intro b

  rw [PMF.map_apply, PMF.uniformOfFintype_apply]
  rw [tsum_eq_single (e.symm b)]
  · simp only [Equiv.apply_symm_apply, ite_true]
    rw [PMF.uniformOfFintype_apply]
    congr
    exact Fintype.card_congr e
  · intro a ha
    have : e a ≠ b := by
      intro h_eq
      exact ha ((Equiv.eq_symm_apply e).mpr h_eq)
    simp only [uniformOfFintype_apply, ite_eq_right_iff, ENNReal.inv_eq_zero,
      ENNReal.natCast_ne_top, imp_false, ne_eq]
    exact Ne.intro (id (Ne.symm this))

/-- Theorem: Product of two uniform distributions is uniform on the product type. -/
theorem uniformOfFintype_prod_eq_prod {α β : Type*}
      [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    PMF.uniformOfFintype (α × β) = PMF.prod (PMF.uniformOfFintype α) (PMF.uniformOfFintype β) := by
  apply PMF.ext
  intro ⟨a_target, b_target⟩

  rw [PMF.uniformOfFintype_apply]

  unfold PMF.prod
  rw [PMF.bind_apply]

  rw [tsum_eq_single a_target]
  · rw [PMF.uniformOfFintype_apply, PMF.map_apply]
    rw [tsum_eq_single b_target]
    · simp only [ite_true, PMF.uniformOfFintype_apply]
      rw [Fintype.card_prod]
      rw [← ENNReal.mul_inv]
      · norm_cast
      · simp [Fintype.card_ne_zero]
      · simp [Fintype.card_ne_zero]
    · intro b hb
      simp only [Prod.mk.injEq, true_and, uniformOfFintype_apply, ite_eq_right_iff,
        ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, imp_false]
      exact Ne.intro (id (Ne.symm hb))
  · intro a ha
    rw [PMF.map_apply]
    simp only [uniformOfFintype_apply, Prod.mk.injEq, tsum_fintype, mul_eq_zero,
      ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, Finset.sum_eq_zero_iff, Finset.mem_univ,
      ite_eq_right_iff, imp_false, not_and, forall_const, forall_apply_eq_imp_iff, false_or]
    exact Ne.intro (id (Ne.symm ha))


/-! ### Layer 3: BitVec Uniform Distribution Layer (U n) -/

/-- The uniform distribution over `α` is preserved under any equivalence `e : α ≃ β`:
    mapping by `e` yields the uniform distribution over `β`. -/
lemma uniformOfFintype_map_equiv {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  apply PMF.ext
  intro b
  simp only [map_apply, uniformOfFintype_apply]
  rw [Fintype.card_congr e.symm]
  rw [tsum_eq_single (e.symm b)]
  · simp only [Equiv.apply_symm_apply, ↓reduceIte]
  · intro c hc
    have : b ≠ e c := by
      by_contra;
      rw [this] at hc
      simp at hc
    simp only [this, ↓reduceIte]

/-- Shortcut for the uniform distribution over `BitVec n`. -/
def U (n : ℕ) : PMF (BitVec n) := PMF.uniformOfFintype (BitVec n)

/-- Uniform distribution is preserved over `bv_cast`. -/
theorem U_cast {n m : ℕ} (h : n = m) :
    U n = (U m).map (bv_cast_equiv h).symm := by
  unfold U
  rw [U_map_equiv (bv_cast_equiv h).symm]

/-- The uniform distribution on BitVec 0 is just 'pure' of the empty bitvector. -/
theorem U_0_eq_pure : U 0 = PMF.pure 0#0 := by
  apply PMF.ext
  intro x
  simp [U, PMF.uniformOfFintype_apply]
  exact BitVec.of_length_zero

/-- The uniform distribution on BitVec (L - L) is also a 'pure' distribution. -/
theorem U_sub_self_eq_pure (L : ℕ) :
    U (L - L) = PMF.pure (bv_cast_equiv (Nat.sub_self L).symm 0#0) := by
  rw [U_cast (Nat.sub_self L), U_0_eq_pure]
  simp [PMF.pure_map]
  congr

/-- Sampling `U (n + m)` is equivalent to sampling `U n` and `U m` independently and joining. -/
theorem U_split (n m : ℕ) :
    U (n + m) = (do let x ← U n; let y ← U m; PMF.pure (bv_join n m (x, y))) := by
  unfold U
  rw [← U_map_equiv (bv_join n m)]
  rw [uniformOfFintype_prod_eq_prod]
  unfold PMF.prod PMF.map
  simp only [bind_bind, Function.comp_apply, PMF.pure_bind]
  rfl

/-- Inverse of `U_split`: Joining two independent samples results in a larger uniform sample. -/
theorem U_join (n m : ℕ) :
    (do let x ← U n; let y ← U m; PMF.pure (bv_join n m (x, y))) = U (n + m) := by
  rw [U_split n m]

theorem U_join_append (n m : ℕ) :
  (do let x ← U n; let y ← U m; PMF.pure (x ++ y)) = U (n + m) := by
  rw [U_split n m]
  rfl

/-- Sampling `n+m` uniform bits equals sampling `n` bits then `m` bits and concatenating. -/
lemma U_add_dist (n m : ℕ) :
    U (n + m) = (do let b1 ← U n; let b2 ← U m; return b1 ++ b2) := by
    simp only [← U_join_append]
    rfl


/-- Decomposition of a uniform sample into three parts. -/
theorem U_split3 (n m k : ℕ) :
  U (n + m + k) = (do let x ← U n; let y ← U m; let z ← U k; PMF.pure (bv_join3 n m k (x, y, z)))
    := by
  rw [U_cast (Nat.add_assoc n m k)]
  rw [U_split n (m + k)]
  rw [U_split m k]
  simp only [bind_assoc]
  erw [PMF.map_bind]
  congr; funext x
  erw [PMF.map_bind]
  congr; funext y
  erw [PMF.map_bind]
  congr; funext z
  erw [PMF.map_bind]
  simp only [PMF.pure_bind, PMF.pure_map]
  congr 1


/-- The core lemma for hybrid arguments: splitting a uniform L-bit sample. -/
theorem U_split3_i {L : ℕ} (i : Fin L) :
    U L = (do let x ← U i; let b ← U 1;
              let y ← U (L - i - 1);
              PMF.pure (bv_join3_i i (x, b, y))) := by
  have h_len : L = i + 1 + (L - i - 1) := by omega
  calc
    U L
    _ = (U (i + 1 + (L - i - 1))).map (bv_cast_equiv (by omega)).symm := by rw [U_cast]
    _ = (do
          let x ← U i
          let b ← U 1
          let y ← U (L - i - 1)
          PMF.pure (bv_join3 i 1 (L - i - 1) (x, b, y))
        ).map (bv_cast_equiv h_len).symm := by rw [U_split3]
    _ = (do
          let x ← U i
          let b ← U 1
          let y ← U (L - i - 1)
          PMF.pure ((bv_cast_equiv h_len).symm (bv_join3 i 1 (L - i - 1) (x, b, y)))) := by
        erw [PMF.map_bind]; congr; funext x
        erw [PMF.map_bind]; congr; funext b
        erw [PMF.map_bind]; congr; funext y
        simp only [PMF.pure_map]
    _ = (do let x ← U i; let b ← U 1; let y ← U (L - i - 1); PMF.pure (bv_join3_i i (x, b, y))) := by
        rfl

/-- Sampling `U L` is equivalent to sampling `U i` and `U (L - i)` independently and joining. -/
theorem U_split_i {L : ℕ} (i : Fin (L + 1)) :
  U L = (do let x ← U i; let y ← U (L - i); PMF.pure (bv_join_i i (x, y))) := by
  rw [U_cast (n := L) (m := i + (L - i)) (by omega)]
  rw [U_split i (L - i)]
  erw [map_bind]; congr; funext a
  erw [map_bind]; congr; funext x
  simp only [PMF.pure_map]; congr 1

/-- Joining two independent uniform samples results in a larger uniform sample. -/
theorem U_join_i {L : ℕ} (i : Fin (L + 1)) :
  (do let x ← U i; let y ← U (L - i); PMF.pure (bv_join_i i (x, y))) = U L := by
  rw [U_split_i i]

/-- Variant of `U_split_i` using the explicit append operator `++`.
    This is useful for matching raw game code. -/
theorem U_split_append_i {L : ℕ} (i : Fin (L + 1)) :
    U (i + (L-i)) = (do let x ← U i; let y ← U (L - i); PMF.pure (x ++ y)) := by
  rw [U_join_append]

/-- Variant of `U_join_i` using the explicit append operator `++`. -/
theorem U_join_append_i {L : ℕ} (i : Fin (L + 1)) :
    (do let x ← U i; let y ← U (L - i); PMF.pure (x ++ y)) = U (i + (L-i)) := by
  rw [U_split_append_i]

/-- Converting a uniform `BitVec 1` into a uniform `Bool` (coin flip). -/
theorem U1_to_bool :
  (U 1).map bv_to_bool = PMF.uniformOfFintype Bool := by
  rw [U_cast (Nat.add_zero 1)]
  erw [PMF.map_bind]
  unfold U
  simp only [Function.comp_apply]
  simp only [Nat.add_zero]
  simp only [PMF.pure_map]
  change (uniformOfFintype (BitVec 1)).map
              (fun a => bv_to_bool ((bv_cast_equiv (Nat.add_zero 1)).symm a)) = _
  erw [U_map_equiv (bv_to_bool)]

/-- randomBit is the uniform distribution over Bit {0, 1}. -/
noncomputable abbrev randomBit : PMF Bit :=
  PMF.uniformOfFintype Bit

/-- U 1 is equivalent to randomBit when mapped through bv_to_bit. -/
theorem U1_to_randomBit :
  (U 1).map bv_to_bit = randomBit := by
  unfold U randomBit
  -- Since bv_to_bit is an Equiv, uniformity is preserved.
  rw [U_map_equiv bv_to_bit]

/-- The uniform distribution over Bool is equivalent to randomBit when mapped. -/
theorem bool_to_randomBit :
  (PMF.uniformOfFintype Bool).map bool_to_bit = randomBit := by
  unfold randomBit
  -- Since bool_to_bit is an Equiv, uniformity is preserved.
  rw [U_map_equiv bool_to_bit]

/-! ### Layer 4: Game Transformation Layer -/

/-- `do`-notation compatible version of `PMF.bind_bind`. Needed because the outer `do` block
desugars to `Bind.bind` while the inner `p.bind f` uses `PMF.bind` explicitly, so
`PMF.bind_bind` alone fails to rewrite via `rw`/`erw`/`simp`. -/
@[simp] theorem bind_bind_do {α β γ : Type} (p : PMF α) (f : α → PMF β) (g : β → PMF γ) :
    (do let pair ← p.bind f; g pair) = (do let x ← p; let pair ← f x; g pair) :=
  PMF.bind_bind p f g

/-- `do`-notation compatible version of `PMF.pure_bind`. Needed because `do`-notation
desugars to `Bind.bind`/`Pure.pure`, which does not syntactically match `PMF.bind`/`PMF.pure`,
so `PMF.pure_bind` alone fails to rewrite inside a `do` block via `rw`/`erw`/`simp`. -/
@[simp] theorem pure_bind_do {α β : Type} (a : α) (f : α → PMF β) :
    (do let x ← PMF.pure a; f x) = f a := PMF.pure_bind a f

/-- Removing an unused sampling from a game. -/
@[simp] theorem bind_unused {α β} (m : PMF α) (b : PMF β) :
  (do let _ ← m; b) = b := PMF.bind_const m b

/-- `do`-notation compatible version of `PMF.map_bind`.
    Moves `map` inside a `do` block. -/
@[simp] theorem map_bind_do {α β γ : Type} (p : PMF α) (f : α → PMF β) (g : β → γ) :
    (do let x ← p; f x).map g = (do let x ← p; (f x).map g) := by
  simp [Bind.bind, PMF.map]

/-- `do`-notation compatible version of `PMF.map_pure`.
    Combines `map` with the final `pure` of a `do` block. -/
@[simp] theorem map_pure_do {α β : Type} (x : α) (f : α → β) :
    (PMF.pure x).map f = PMF.pure (f x) := by
  exact pure_map f x

/-- `do`-notation compatible version of `PMF.bind_map`.
    Flattens a `bind` of a `map` into a single `do` block. -/
@[simp] theorem bind_map_do {α β γ : Type} (p : PMF α) (f : α → β) (g : β → PMF γ) :
    (do let x ← p.map f; g x) = (do let a ← p; g (f a)) := by
  rw [map]
  simp only [bind_bind_do, Function.comp_apply, pure_bind_do]

/-- Commutativity of two independent samplings. -/
theorem bind_comm {α β γ} (ma : PMF α) (mb : PMF β) (f : α → β → PMF γ) :
  (do let a ← ma; let b ← mb; f a b) = (do let b ← mb; let a ← ma; f a b) :=
  PMF.bind_comm ma mb f

/-- Pr: the probability that a PMF Bool outputs true. -/
noncomputable def Pr (p : PMF Bool) : ENNReal := p true

/-- Pr distributes over bind as an expected value. -/
lemma Pr_bind (p : PMF α) (f : α → PMF Bool) :
    Pr (p.bind f) = ∑' a, p a * Pr (f a) := by
  simp [Pr, PMF.bind_apply]

/-- Pr of a PMF equals 1 minus the probability of the complemented PMF. -/
lemma Pr_compl (p : PMF Bool) :
    Pr p = 1 - (p.bind (fun b => PMF.pure (!b))) true := by
  have h := p.tsum_coe
  rw [tsum_bool, add_comm] at h
  simp only [Pr, PMF.bind_apply, PMF.pure_apply,
             tsum_bool, Bool.not_true, Bool.not_false, ↓reduceIte]
  apply ENNReal.eq_sub_of_add_eq' (by norm_num)
  simp only [mul_one, Bool.true_eq_false, ↓reduceIte, mul_zero, add_zero, h]

/-- The reverse direction of `Pr_compl`: the probability of the negated event
    equals one minus the original probability. -/
lemma Pr_negate (p : PMF Bool) :
    Pr (p.bind (fun b => PMF.pure (!b))) = 1 - Pr p := by
  unfold Pr
  have h := p.tsum_coe
  rw [tsum_bool, add_comm] at h
  simp only [PMF.bind_apply, PMF.pure_apply, tsum_bool,
             Bool.not_true, Bool.not_false, ↓reduceIte]
  apply ENNReal.eq_sub_of_add_eq' (by norm_num)
  simp only [mul_one, Bool.true_eq_false, ↓reduceIte, mul_zero, add_zero]
  rw [add_comm]; exact h

/-- For any boolean `a`, the function `(a == ·)` is an equivalence of Bool. -/
def bool_beq_equiv (a : Bool) : Bool ≃ Bool where
  toFun b := (a == b)
  invFun b := (a == b)  -- (a == (a == b)) is equal to b
  left_inv b := by cases a <;> cases b <;> rfl
  right_inv b := by cases a <;> cases b <;> rfl

/-- Probability of correctly guessing an independent uniform bit is exactly 1/2. -/
theorem Pr_comparison_uniform_bit (AnyDist : PMF Bool) :
    Pr (do  let a ← AnyDist
            let b ← PMF.uniformOfFintype Bool
            PMF.pure (a == b)) = 1/2 := by
  calc
    Pr (do  let a ← AnyDist;
            let x_bit ← PMF.uniformOfFintype Bool;
            PMF.pure (a == x_bit))
    _ = Pr (do let a ← AnyDist; PMF.uniformOfFintype Bool) := by
        congr 1
        congr 1; funext a
        change (PMF.uniformOfFintype Bool).map (bool_beq_equiv a) = _
        rw [U_map_equiv]
    -- The sampled `a` is now unused, so it can be dropped.
    _ = Pr (PMF.uniformOfFintype Bool) := by rw [bind_unused]
    _ = 1 / 2 := by simp [Pr, PMF.uniformOfFintype_apply]

/-- Core identity behind the predictor-to-distinguisher conversion:
    `Pr[B succeeds] + Pr[A outputs 1 on random] = 1/2 + Pr[A outputs 1 on real]`. -/
theorem Pr_prediction_logic (f : Bool → PMF Bit) (target : Bool) :
  Pr (do let w ← PMF.uniformOfFintype Bool; let a ← f w; PMF.pure ((if a == 1 then w else !w) == target)) +
  Pr (do let w ← PMF.uniformOfFintype Bool; let a ← f w; PMF.pure (a == 1)) =
  1 / 2 + Pr (do let a ← f target; PMF.pure (a == 1)) := by

  simp only [Pr, Bind.bind, PMF.bind_apply, PMF.pure_apply, PMF.uniformOfFintype_apply, Fintype.card_bool]
  simp only [tsum_bool, Nat.cast_ofNat]
  cases target <;>
  simp [← mul_add]
  · have : ((f false) 1 + (f true) 0 + ((f false) 1 + (f true) 1))
          = ((f false) 1 + (f false) 1 + ( (f true) 1 + (f true) 0)) := by ring
    rw [this]
    have : (f true) 1 + (f true) 0 = 1 := by
      rw [← tsum_coe (f true)]
      simp only [tsum_fintype]
      rw [Fin.sum_univ_two, add_comm]
    rw [this]
    ring_nf; congr;
    rw [mul_right_comm]
    rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  · have : ((f false) 0 + (f true) 1 + ((f false) 1 + (f true) 1))
          = ((f false) 0 + (f false) 1 + ( (f true) 1 + (f true) 1)) := by ring
    rw [this]
    have : (f false) 0 + (f false) 1 = 1 := by
      rw [← tsum_coe (f false)]
      simp only [tsum_fintype]
      rw [Fin.sum_univ_two, add_comm]
    rw [this]
    ring_nf; congr;
    rw [mul_right_comm]
    rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- Splitting U (L-i) into a `(L-i-1)`-bit prefix and a 1-bit suffix. -/
lemma h_split_U (i L : Nat) (hL : i < L) : U (L - i) = do
      let pre ← U (L - (i + 1))
      let b   ← U 1
      return (pre ++ b).cast (by omega) := by
  let n := L - (i+1)
  let m := 1
  have h_len : L - i = n + m := by omega
  calc
    U (L - i)
    _ = (U (n + m)).map (bv_cast_equiv h_len).symm := by rw [U_cast h_len]
    _ = (do let x ← U n; let y ← U m; PMF.pure (x ++ y)).map (bv_cast_equiv h_len).symm := by
        rw [U_split n m]
        rfl
    _ = do let x ← U n; let y ← U m; return ((x ++ y).cast h_len.symm) := by
        simp only [map_bind_do, map_pure_do]
        rfl

/-- Extracting one bit from `U 1` is the same as sampling from the uniform `Bool` distribution. -/
lemma U1_getLsbD_eq_uniformBool {α : Type} (f : Bool → PMF α) :
    (do let u ← U 1; f (u.getLsbD 0)) =
    (do let b ← PMF.uniformOfFintype Bool; f b) := by
  calc
    (do let u ← U 1; f (u.getLsbD 0))
    -- 1. `getLsbD 0` is exactly `bv_to_bool`'s definition.
    _ = (do let u ← U 1; f (bv_to_bool u)) := by
        simp only [bv_to_bool]
        simp only [zero_lt_one, BitVec.getLsbD_eq_getElem, BitVec.ofNat_eq_ofNat, Equiv.coe_fn_mk]
    _ = (do let b ← (U 1).map bv_to_bool; f b) := by
        rw [← bind_map_do]
    _ = (do let b ← PMF.uniformOfFintype Bool; f b) := by
        rw [U1_to_bool]

end BVCryptGame
