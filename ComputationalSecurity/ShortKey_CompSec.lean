/-
  Definitions and theorems for short-key computational security.
  Includes the ciphertext distribution `Enc_dist`, indistinguishability-based
  perfect secrecy, the one-time pad (OTP), and the security transfer theorem
  showing that replacing a uniform key with a PRG preserves computational security.

  Some definitions are adapted from the PerfectSecrecy2 repository by Yasuaki Honda.

  Reference: Chapter 4, "Pseudorandomness"
  Authors: Yasuaki Honda
-/
import ComputationalSecurity.DistInd
import ComputationalSecurity.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ComputationalSecurity

variable {M K C : Type}

/-- The distribution of ciphertexts obtained by encrypting `msg` under a key
    sampled from `Gen`.
    Formally: `(Enc_dist Enc Gen msg) c = Pr[k ← Gen; Enc k msg = c]`. -/
noncomputable
def Enc_dist (Enc : K → M → C) (Gen : PMF K) (msg : M) : PMF C :=
  do
    let k ← Gen
    PMF.pure (Enc k msg)

/-- Indistinguishability-based definition of perfect secrecy.
    An encryption scheme `(Enc, Gen)` achieves perfect secrecy if for every pair of
    messages `m1, m2` and every ciphertext `c`, the probability that `c` is the
    encryption of `m1` equals that of `m2`. -/
def ind_perfect_secrecy (Enc : K → M → C) (Gen : PMF K) :=
  ∀ (msg1 msg2 : M) (c : C),
    (Enc_dist Enc Gen msg1) c = (Enc_dist Enc Gen msg2) c

/-- Security Transfer Theorem (generalization of Prop. 4.4 in the textbook).
    If `Enc` is perfectly secret under the uniform key distribution `U m`,
    then replacing the key with the output of a PRG `G` yields a scheme whose
    ciphertext distributions are computationally indistinguishable (`DistIndistinguishable`)
    for any pair of messages. -/
theorem security_transfer
    (n m : ℕ) [Fintype (BitVec n)] [Fintype (BitVec m)]
    (Enc : (BitVec m) → M → C)
    (G : BitVec n → BitVec m)
    (t t_enc : ℕ) (ε : NNReal)
    (h_perf : ind_perfect_secrecy Enc (U m))
    (h_prg : IsPRG G (t + t_enc) (ε / 2)) :
    ∀ m0 m1, DistIndistinguishable
        (Enc_dist Enc (PMF.map G (U n)) m0)
        (Enc_dist Enc (PMF.map G (U n)) m1) t ε := by
  intro m0 m1

  let P0 := Enc_dist Enc (PMF.map G (U n)) m0
  let P1 := Enc_dist Enc (PMF.map G (U n)) m1
  let Q0 := Enc_dist Enc (U m) m0
  let Q1 := Enc_dist Enc (U m) m1

  -- Q0 = Q1 follows from perfect secrecy.
  have h_Q0_Q1 : Q0 = Q1 := by
    apply PMF.ext
    intro c
    exact h_perf m0 m1 c

  let A (msg : M) : BitVec m → PMF C := fun k => PMF.pure (Enc k msg)

  -- Rewrite Enc_dist as a monadic bind to apply the closure theorem.
  have h_Enc_bind (Gen : PMF (BitVec m)) (msg : M) :
      Enc_dist Enc Gen msg = Gen >>= A msg := by
    simp [Enc_dist, A, Bind.bind]

  -- P0 ≈ Q0 and P1 ≈ Q1 follow from the PRG property via closure (Prop. 4.1).
  have h_P0_Q0 : DistIndistinguishable P0 Q0 t (ε / 2) := by
    unfold P0 Q0
    rw [h_Enc_bind (PMF.map G (U n)) m0, h_Enc_bind (U m) m0]
    apply closure (PMF.map G (U n)) (U m) (A m0) t t_enc (ε / 2)
    exact h_prg.right

  have h_P1_Q1 : DistIndistinguishable P1 Q1 t (ε / 2) := by
    unfold P1 Q1
    rw [h_Enc_bind (PMF.map G (U n)) m1, h_Enc_bind (U m) m1]
    apply closure (PMF.map G (U n)) (U m) (A m1) t t_enc (ε / 2)
    exact h_prg.right

  -- 2. Define the Hybrid Sequence (length l = 2)
  -- X 0 = P0, X 1 = Q0 (= Q1), X 2 = P1
  let X : ℕ → PMF C := fun i =>
    match i with
    | 0 => P0
    | 1 => Q0
    | _ => P1

  -- 3. Apply the transitivity lemma
  apply transitivity X 2 t ε (by norm_num)

  -- 4. Prove that adjacent steps are ε/2-indistinguishable
  intro i hi
  interval_cases i
  · -- Step 0: P0 ≈ Q0 (ε/2)
    change DistIndistinguishable P0 Q0 t (ε / 2)
    simp_rw [P0, Q0]
    rw [h_Enc_bind (PMF.map G (U n)) m0, h_Enc_bind (U m) m0]
    apply closure (PMF.map G (U n)) (U m) (A m0) t t_enc (ε / 2)
    exact h_prg.right
  · -- Step 1: Q0 ≈ P1 (ε/2)
    change DistIndistinguishable Q0 P1 t (ε / 2)
    rw [h_Q0_Q1] -- Q0 = Q1
    simp_rw [P1, Q1]
    -- Since Q0 = Q1, this is equivalent to Q1 ≈ P1
    rw [h_Enc_bind (U m) m1, h_Enc_bind (PMF.map G (U n)) m1]
    -- Use the symmetry of indistinguishability if needed, or re-apply closure
    -- DistIndistinguishable is symmetric, or apply closure directly:
    rw [DistIndistinguishable_comm] -- Assume this lemma exists in your library
    apply closure (PMF.map G (U n)) (U m) (A m1) t t_enc (ε / 2)
    exact h_prg.right

/-- Fixed-message indistinguishability: for any fixed pair of messages `m0` and `m1`,
    no adversary with complexity at most `t` can distinguish their ciphertext distributions
    with advantage greater than `ε`.
    This is the per-message-pair version of `Indistinguishable` (Definition 3.5). -/
def FixedMessageIndistinguishable
    (Enc : K → M → C) (Gen : PMF K) (t : ℕ) (ε : NNReal) : Prop :=
  ∀ (m0 m1 : M), DistIndistinguishable (Enc_dist Enc Gen m0) (Enc_dist Enc Gen m1) t ε


/-- Equivalence between fixed-message and adversarial indistinguishability.
    `FixedMessageIndistinguishable` holds if and only if `Indistinguishable` holds
    for all state types `St`. The forward direction uses an expectation argument;
    the reverse direction uses a reduction with `St = Unit`. -/
theorem indistinguishability_equivalence
    (Enc : K → M → C) (Gen : PMF K) (t : ℕ) (ε : NNReal)
    [Fintype M] [Fintype K] [Fintype C] [DecidableEq C] :
    FixedMessageIndistinguishable Enc Gen t ε ↔
    (∀ (St : Type) [Fintype St] [Inhabited St], Indistinguishable Enc Gen t ε (St := St)) := by
  constructor
  · -- Forward: Fixed-Message → Adversarial (expectation argument).
    intro h_fixed St _ _ A1 A2 tA1 tA2 h_t

    let adv_at (m0 m1 : M) (st : St) :=
      (PrDX_one (Enc_dist Enc Gen m0) (fun c => A2 c st)) -
      (PrDX_one (Enc_dist Enc Gen m1) (fun c => A2 c st))

    -- Expand the adversarial advantage as a weighted sum over A1's outputs.
    have h_expand : (p0 Enc Gen A1 A2).toReal - (p1 Enc Gen A1 A2).toReal =
                    ∑ x, (A1 x).toReal * adv_at x.1 x.2.1 x.2.2 := by
      simp only [adv_at]
      have toReal_bind_apply {α β : Type} [Fintype α] (p : PMF α) (f : α → PMF β) (b : β) :
          ((p >>= f) b).toReal = ∑ a, (p a).toReal * (f a b).toReal := by
        simp only [bind, PMF.bind_apply, tsum_fintype]
        rw [ENNReal.toReal_sum]
        · simp_rw [ENNReal.toReal_mul]
        · intro a _
          apply ENNReal.mul_ne_top <;> apply PMF.apply_ne_top

      have h_p0 : (p0 Enc Gen A1 A2).toReal =
            ∑ x, (A1 x).toReal * (PrDX_one (Enc_dist Enc Gen x.1) (fun c => A2 c x.2.2)) := by
        unfold p0 PrDX_one Enc_dist Pr
        rw [toReal_bind_apply]
        congr
        funext x
        congr 1
        simp only [Fin.isValue, bind_assoc]
        congr 1
        conv_rhs =>
          arg 1; arg 2; ext k; arg 2; ext c;
        conv_rhs =>
          arg 1; arg 2;
          ext k
          simp only [Bind.bind, Pure.pure]
          simp only [PMF.pure_bind]
        erw [PMF.bind_apply, PMF.bind_apply]
        simp only [Fin.isValue, tsum_fintype, PMF.bind_apply, PMF.pure_apply, Bool.true_eq,
          beq_iff_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

      have h_p1 : (p1 Enc Gen A1 A2).toReal =
            ∑ x, (A1 x).toReal * (PrDX_one (Enc_dist Enc Gen x.2.1) (fun c => A2 c x.2.2)) := by
        unfold p1 PrDX_one Enc_dist Pr
        rw [toReal_bind_apply]
        congr; funext x
        congr 1
        simp only [Fin.isValue, bind_assoc]
        congr 1
        conv_rhs =>
          arg 1; arg 2; ext k; arg 2; ext c;
        conv_rhs =>
          arg 1; arg 2;
          ext k
          simp only [Bind.bind, Pure.pure]
          simp only [PMF.pure_bind]
        erw [PMF.bind_apply, PMF.bind_apply]
        simp only [Fin.isValue, tsum_fintype, PMF.bind_apply, PMF.pure_apply, Bool.true_eq,
          beq_iff_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

      rw [h_p0, h_p1]
      rw [← Finset.sum_sub_distrib]
      congr
      funext x
      rw [mul_sub]

    rw [h_expand]
    calc
      |∑ x, (A1 x).toReal * adv_at x.1 x.2.1 x.2.2|
        ≤ ∑ x, |(A1 x).toReal * adv_at x.1 x.2.1 x.2.2| := by
          apply Finset.abs_sum_le_sum_abs
        _ = ∑ x, (A1 x).toReal * |adv_at x.1 x.2.1 x.2.2| := by
          congr; funext x
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        _ ≤ ∑ x, (A1 x).toReal * (ε : ℝ) := by
          apply Finset.sum_le_sum
          intro x _
          apply mul_le_mul_of_nonneg_left
          · exact h_fixed x.1 x.2.1 (fun c => A2 c x.2.2) tA2 (by linarith)
          · exact ENNReal.toReal_nonneg
        _ = (ε : ℝ) := by
          refine
            Real.arith_mean_weighted_of_constant Finset.univ (fun i ↦ (A1 i).toReal) (fun i ↦ ↑ε) ↑ε
              ?_ fun i a ↦ congrFun rfl
          simp only
          rw [← ENNReal.toReal_sum]
          · have : ∑ x, A1 x = ∑' x, A1 x := by
              rw [tsum_eq_sum]; norm_num
            rw [this, PMF.tsum_coe A1]
            norm_cast
          · intro a ha
            exact PMF.apply_ne_top A1 a

  · -- Reverse: Adversarial → Fixed-Message (reduction with St = Unit).
    intro h_adv_all m0 m1 D tD h_tD

    specialize h_adv_all Unit

    -- Construct a point-mass adversary A1' concentrating on the target pair (m0, m1).
    let A1' : PMF (M × M × Unit) := PMF.pure (m0, m1, ())
    let A2' (c : C) (_ : Unit) : PMF Bit := D c

    -- The advantage of A1' equals the fixed-message advantage.
    have h_adv_eq : |(p0 Enc Gen A1' A2').toReal - (p1 Enc Gen A1' A2').toReal| =
                    |(PrDX_one (Enc_dist Enc Gen m0) D) -
                     (PrDX_one (Enc_dist Enc Gen m1) D)| := by
      have h_p0_eq_m0 : (p0 Enc Gen A1' A2').toReal = PrDX_one (Enc_dist Enc Gen m0) D := by
        simp only [p0, PrDX_one, Pr, A1', A2', Enc_dist]
        simp only [Bind.bind, Bind.bind]
        simp only [PMF.pure_bind, Fin.isValue, PMF.bind_apply, tsum_fintype, PMF.bind_bind,
          PMF.pure_apply, Bool.true_eq, beq_iff_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte]
      have h_p1_eq_m1 : (p1 Enc Gen A1' A2').toReal = PrDX_one (Enc_dist Enc Gen m1) D := by
        simp only [p1, PrDX_one, Pr, A1', A2', Enc_dist]
        simp only [Bind.bind, Bind.bind]
        simp only [PMF.pure_bind, Fin.isValue, PMF.bind_apply, tsum_fintype, PMF.bind_bind,
          PMF.pure_apply, Bool.true_eq, beq_iff_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte]
      rw [h_p0_eq_m0, h_p1_eq_m1]

    rw [← h_adv_eq]
    apply h_adv_all A1' A2' 0 tD (by linarith)

/--
The fundamental security transfer theorem from perfect secrecy to computational indistinguishability.
It proves that an encryption scheme achieving perfect secrecy under a truly uniform key distribution
remains computationally indistinguishable (Definition 3.5) when the key is instead sampled
from a Pseudorandom Generator (PRG). This reduction connects the PRG's security and the
scheme's perfect secrecy to the adversarial indistinguishability definition.
-/
theorem IndPS_PRG_implies_Computational_Indistinguishability
      (n m : ℕ) [Fintype (BitVec n)] [Fintype (BitVec m)]
      [Fintype M] [Fintype C] [DecidableEq C]
      (Enc : (BitVec m) → M → C)
      (G : BitVec n → BitVec m)
      (t t_enc : ℕ) (ε : NNReal)
      (h_ind_ps : ind_perfect_secrecy Enc (U m))
      (h_prg : IsPRG G (t + t_enc) (ε / 2)) :
    ∀ (St : Type) [Fintype St] [Inhabited St],
        Indistinguishable Enc (PMF.map G (U n)) t ε (St := St) := by

  rw [← indistinguishability_equivalence]
  exact security_transfer n m Enc G t t_enc ε h_ind_ps h_prg


/- BitVec n is used to represent the sets of plain text, cipher text, and keys.-/
variable {n : ℕ} [Fintype (BitVec n)]

/-- One-time pad encryption function -/
def OTP_Enc (n : ℕ) (k : BitVec n) (m : BitVec n) : BitVec n :=
  k ^^^ m

/-- One-time pad decryption function -/
def OTP_Dec (n : ℕ) (k : BitVec n) (c : BitVec n) : BitVec n :=
  k ^^^ c

/-- Uniform distribution over the set of keys -/
noncomputable
def OTP_Gen : PMF (BitVec n) :=
  PMF.uniformOfFintype (BitVec n)

omit [Fintype (BitVec n)] in
/-- Lemma: For any m, k, c ∈ BitVec n, c = Enc(k, m) ↔ k = Dec(c, m) -/
lemma mkc_symm (m k c : (BitVec n)) : c=k^^^m ↔ k=c^^^m := by
  constructor
  · intro hc
    rw [hc, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · intro hk
    rw [hk, BitVec.xor_assoc,BitVec.xor_self, BitVec.xor_zero]

/-- Theorem: One-time pad encryption achieves indistinguishability-based perfect secrecy -/
theorem OTP_is_ind_perfectly_secret :
  ind_perfect_secrecy (OTP_Enc n: BitVec n → BitVec n → BitVec n)
                      (OTP_Gen : PMF (BitVec n)) := by
    intro m₁ m₂ c

    unfold Enc_dist OTP_Gen OTP_Enc
    simp [Bind.bind, PMF.bind_apply, mkc_symm, tsum_ite_eq]

theorem OTP_PRG_implies_Computational_Indistinguishability
    (m m' : ℕ) [Fintype (BitVec m)] [Fintype (BitVec m')]
    (t t_enc : ℕ) (ε : NNReal)
    (G : BitVec m → BitVec m')
    (h_prg : IsPRG G (t + t_enc) (ε / 2)) :
    ∀ (St : Type) [Fintype St] [Inhabited St],
        Indistinguishable (OTP_Enc m') (PMF.map G (U m)) t ε (St := St) := by
  apply IndPS_PRG_implies_Computational_Indistinguishability
  · exact OTP_is_ind_perfectly_secret
  · exact h_prg

end ComputationalSecurity
