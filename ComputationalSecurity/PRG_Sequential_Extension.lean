import ComputationalSecurity.DistInd
import ComputationalSecurity.BVCryptGameLib
import ComputationalSecurity.PRGDefs
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise

namespace ComputationalSecurity

open PMF
open BVCryptGame

/-!
# Theorem 4.1: PRG Sequential Extension

Formalizes the construction of an L-bit PRG from a 1-bit PRG
via the sequential construction (Figure 4.2 in the textbook).
Security is proven via a hybrid argument over L steps.
-/

section Construction

variable {n : ℕ}

/-- Splits an `(n+1)`-bit vector into the high 1 bit (output) and the low n bits (next seed). -/
def split_next (v : BitVec (n + 1)) : BitVec 1 × BitVec n :=
  let v_aligned : BitVec (1 + n) := v.cast (by omega)
  let p := bv_split 1 n v_aligned
  (p.1, p.2)

/-- Recursively extends a 1-bit PRG `G` to L bits by collecting one output bit per step. -/
def G_ext (G : BitVec n → BitVec (n + 1)) : (L : ℕ) → BitVec n → BitVec L
  | 0, _ => BitVec.zero 0
  | l + 1, s =>
    let res := G s
    let (bit, s_next) := split_next res
    bit ++ G_ext G l s_next |>.cast (by omega)

/-- The extended PRG `G' : {0,1}^n → {0,1}^L`, defined as `G_ext G L`. -/
def G' (G : BitVec n → BitVec (n + 1)) (L : ℕ) (s : BitVec n) : BitVec L :=
  G_ext G L s

/-- The output distribution of the extended PRG G'. -/
noncomputable def G'_dist
    (G : BitVec n → BitVec (n + 1)) (L : ℕ) : PMF (BitVec L) :=
  (U n).map (G' G L)

end Construction

section Lemmas

variable {n : ℕ}

/-- Splitting a concatenation recovers its parts: `split_next (b ++ s) = (b, s)`. -/
private lemma split_next_append (b : BitVec 1) (s : BitVec n) :
    split_next ((b ++ s).cast (by omega)) = (b, s) := by
  unfold split_next
  simp only [BitVec.cast_cast]
  exact (bv_split 1 n).right_inv (b, s)

end Lemmas


section SecurityProof

variable {n : ℕ} (G : BitVec n → BitVec (n + 1)) (L : ℕ)

/-- The i-th hybrid distribution for the proof of Theorem 4.1.
    `Hybrid i` consists of `(L-i)` uniform random bits followed by `i` PRG bits.
    Boundary cases: `Hybrid 0 = U L` and `Hybrid L = G'_dist`. -/
noncomputable def Hybrid (i : ℕ) : PMF (BitVec L) :=
  if h : i <= L then
    do
      let u_pre ← U (L - i)     -- (L-i) uniform random bits
      let seed ← U n
      let suffix := G' G i seed  -- i PRG output bits
      return (u_pre ++ suffix).cast (by omega)
  else
    G'_dist G L

/-- Applies one step of G to an `(n+1)`-bit input: extracts 1 output bit
    and generates the remaining `k-1` bits via `G_ext`. -/
def F_step (G : BitVec n → BitVec (n + 1)) (k : ℕ) (v : BitVec (n + 1)) : BitVec k :=
  match k with
  | 0 => BitVec.zero 0
  | k' + 1 =>
    let (b, s_next) := split_next v
    (b ++ G_ext G k' s_next).cast (by omega)

/-- One step of `G_ext` matches `F_step`: `G' G (k+1) s = F_step G (k+1) (G s)`. -/
lemma G_prime_step_eq_F_step (s : BitVec n) (k : ℕ) :
    G' G (k + 1) s = F_step G (k + 1) (G s) := by
  unfold G' G_ext F_step
  simp only [split_next]


/-- Splits a uniform random bitvector of length `n + 1` into a uniform
    1-bit prefix and a uniform `n`-bit suffix, then recombines them. -/
private lemma U_1_n_split {n : ℕ} :
    U (n + 1) = (do
      let b ← U 1
      let seed ← U n
      PMF.pure ((b ++ seed).cast (by omega))) := by
  calc
    U (n + 1)
      = (fun x => x.cast (by omega)) <$> U (1 + n) := by
        change U (n + 1) = PMF.map (bitvec_add_comm_equiv n) (U (1 + n))
        exact (uniformOfFintype_map_equiv (bitvec_add_comm_equiv n)).symm
    _ = (fun x => x.cast (by omega)) <$> (do
          let b ← U 1
          let seed ← U n
          PMF.pure (b ++ seed)) := by
        rw [U_add_dist 1 n]
        rfl
    _ = (do
          let b ← U 1
          let seed ← U n
          PMF.pure ((b ++ seed).cast (by omega))) := by
        simp only [Functor.map, Function.comp_def, Bind.bind]
        simp only [bind_bind, PMF.pure_bind]

/-- `Hybrid i` equals the distribution obtained by sampling a uniform prefix
    and then applying `F_step` to a fresh uniform `(n+1)`-bit value. -/
lemma step_equiv_random (hi : i < L) :
    Hybrid G L i = (do
        let pre ← U (L - (i + 1))
        let v   ← U (n + 1)
        return (pre ++ F_step G (i + 1) v).cast (by omega)) := by
  calc
    Hybrid G L i
      = (do
          let u_pre ← U (L - i)
          let seed ← U n
          PMF.pure ((u_pre ++ G' G i seed).cast (by omega))) := by
        unfold Hybrid
        simp only [show i ≤ L from by omega, ↓reduceDIte]; rfl
    -- Step 1: use h_split_U to split u_pre into pre and b
    _ = (do
          let u_pre ← (do
            let pre ← U (L - (i + 1))
            let b ← U 1
            PMF.pure (((pre ++ b).cast (by omega) : BitVec (L - i))))
          let seed ← U n
          PMF.pure ((u_pre ++ G' G i seed).cast (by omega))) := by
        congr 1
        exact h_split_U i L hi
    -- Step 2: Flatten the nest
    _ = (do
          let pre ← U (L - (i + 1))
          let b ← U 1
          let seed ← U n
          PMF.pure ((((pre ++ b).cast (by omega) : BitVec (L - i)) ++ G' G i seed).cast (by omega))) := by
        simp only [bind_assoc]; simp only [Bind.bind]; simp only [PMF.pure_bind]
    -- Step 3: Rearrange the contents inside pure (bit string concatenation order) (apply separated lemma)
    _ = (do
          let pre ← U (L - (i + 1))
          let b ← U 1
          let seed ← U n
          PMF.pure ((pre ++ F_step G (i + 1) ((b ++ seed).cast (by omega))).cast (by omega)))
        := by
          simp [F_step, split_next_append]
          unfold G';
          congr; funext pre; congr; funext b; congr; funext seed; congr 1;
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_cast, BitVec.toNat_append]
          simp only [Nat.shiftLeft_or_distrib]
          simp only [Nat.shiftLeft_add, Nat.or_assoc]
          simp only [Nat.shiftLeft_eq_mul_pow]
          ring_nf
    -- Step 4: Refold the sampling of b and seed into a single do block (Refold)
    _ = (do
          let pre ← U (L - (i + 1))
          let v ← (do
            let b ← U 1
            let seed ← U n
            PMF.pure ((b ++ seed).cast (by omega)))
          PMF.pure ((pre ++ F_step G (i + 1) v).cast (by omega))) := by
          congr ; funext pre;
          simp only [bind_assoc]
          congr ; funext b; congr ; funext seed;
          simp only [Bind.bind, PMF.pure_bind]
    -- Step 5: Replace the factored-out part with U (n+1)
    _ = (do
            let pre ← U (L - (i + 1))
            let v ← U (n + 1)
            PMF.pure ((pre ++ F_step G (i + 1) v).cast (by omega))) := by
          congr; funext pre
          congr 1
          exact U_1_n_split.symm

/-- `Hybrid (i+1)` equals the distribution obtained by sampling a uniform prefix
    and then applying `F_step` to the output of the PRG `G`. -/
lemma step_equiv_prg (hi : i < L) :
    Hybrid G L (i + 1) =
      do
        let pre ← U (L - (i + 1))
        let v   ← (U n).map G
        return (pre ++ F_step G (i + 1) v).cast (by omega) := by
  unfold Hybrid
  simp only [show i + 1 ≤ L from hi, ↓reduceDIte]
  -- Rewrite G' G (i+1) s as F_step G (i+1) (G s).
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

/-- A single hybrid step: `Hybrid i ≈(t, ε/L) Hybrid (i+1)`,
    reducing to the security of the base PRG `G`. -/
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

/-- **Theorem 4.1**: If `G : {0,1}^n → {0,1}^(n+1)` is a `(t + L·cost_G, ε/L)`-secure PRG,
    then the sequentially extended PRG `G' : {0,1}^n → {0,1}^L` is `(t, ε)`-secure. -/
theorem PRG_Sequential_Extension
    (n L : ℕ) (hL : L > 0)
    (G : BitVec n → BitVec (n + 1))
    (t : ℕ) (ε : NNReal) (cost_G : ℕ)
    (h_G_secure : DistIndistinguishable ((U n).map G) (U (n + 1)) (t + L * cost_G) (ε / L)) :
    DistIndistinguishable ((U n).map (G' G L)) (U L) t ε := by
  -- Hybrid 0 equals U L (all random bits).
  have h_end : U L = Hybrid G L 0 := by
    unfold Hybrid; simp [zero_le, Nat.sub_zero]
    have (c : BitVec L) :  (fun a ↦ c) <$> U n = PMF.pure c := by
      change PMF.map (Function.const _ c) (U n) = PMF.pure c
      exact PMF.map_const (U n) c
    simp only [Bind.bind, this]
    simp only [PMF.bind_pure]

  -- Hybrid L equals the G' distribution (all PRG bits, zero random bits).
  have h_start : (U n).map (G' G L) = Hybrid G L L := by
    unfold Hybrid
    simp only [Nat.le_refl, ↓reduceDIte, LawfulMonad.bind_pure_comp]
    apply PMF.ext; intro x
    -- We use the fact that BitVec(L-L) is a singleton, meaning an empty bit string.
    have huniq : ∀ b : BitVec (L - L), b = BitVec.zero (L - L) := by
      intro b; apply BitVec.eq_of_toNat_eq; simp
      have h : b.toNat < 2 ^ (L - L) := b.isLt
      have h1 : 2 ^ (L - L) = 1 := by simp
      omega
    simp_rw [huniq]
    conv_rhs =>
      arg 1; arg 2; ext u_pre; arg 1; ext a;
      rw [show BitVec.cast _ (BitVec.zero (L - L) ++ G' G L a) = G' G L a from by
        apply BitVec.eq_of_toNat_eq; simp]
    simp only [Bind.bind, PMF.bind_const]
    exact DFunLike.congr rfl rfl

  rw [h_start, h_end]
  -- Flip direction: DistIndistinguishable is symmetric.
  rw [DistIndistinguishable_comm]
  apply transitivity (Hybrid G L) L t ε hL
  intro i hi
  exact Sequential_Extension_Step n L G i hi t ε cost_G h_G_secure

end SecurityProof

end ComputationalSecurity
