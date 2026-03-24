/-
  Formalization of Theorem 3.2 (textbook Chapter 3, pp.36-37):
  (t + tM + th + tR, ε)-Indistinguishability implies
  (t, tGen + tEnc, ε)-Semantic Security.

  ----------------------------------------------------------------
  Proof structure (following textbook pp.36-37):
  ----------------------------------------------------------------
  Step 1: Construct indistinguishability adversary (B1_ind, B2_ind) from (A1, A2):
            B1_ind: sample (mDist, h, R, st) ← A1, m ← mDist,
                    output (m0 = m, m1 = default, stB = (m, h(m), R, st))
            B2_ind: receive ciphertext c and state stB = (m, hval, R, st),
                    run a ← A2(c, hval, st), output R(m, a)
  Step 2: Construct simulator S_sim from (Enc, Gen, A2):
            S_sim receives (hval, st) exactly like A2 (it simulates A2).
            Generates k' ← Gen, encrypts default : M,
            runs A2(Enc k' default, hval, st), returns the output directly.
            This matches the textbook simulator on p.37.
  Step 3: Show p0(B1_ind A1, B2_ind A2) = pa(A1, A2)  [textbook eq on p.37]
  Step 4: Show p1(B1_ind A1, B2_ind A2) = ps(A1, S_sim)  [textbook eq on p.37]
  Step 5: Apply Indistinguishable_without_hne to (B1_ind A1, B2_ind A2):
            |p0 - p1| ≤ ε, hence |pa - ps| ≤ ε. Done.

  ----------------------------------------------------------------
  Key type design:
  ----------------------------------------------------------------
  - A1, A2, S operate on state type St  (semantic security world)
  - B1_ind, B2_ind operate on St_B M St (indistinguishability world)
  - St_B M St = M × Bit × (M → Bit → Bit) × St packages
    (m, h(m), R, st) so that B2_ind can recover the ss experiment
  - S_sim has type Bit → St → PMF Bit (same as any simulator for A2)
  - m' = default throughout (B1_ind and S_sim share the same fixed plaintext),
    which requires [Inhabited M]
  - Indistinguishable_without_hne is used instead of Indistinguishable
    so that B1_ind (which may output m = default) can be applied directly.
    The two definitions are equivalent: any adversary achieving |p0-p1| > ε > 0
    must have m0 ≠ m1 on its support anyway.

  ----------------------------------------------------------------
  File organization:
  ----------------------------------------------------------------
    Section 1 (def B1_ind, B2_ind): Construction of indistinguishability adversaries
    Section 2 (def S_sim):          Construction of simulator
    Section 3 (lemmas):             p0_eq_pa, p1_eq_ps
    Section 4 (theorem):            Main theorem assembling Steps 1–5

  Authors: Yasuaki Honda
-/

import ComputationalSecurity.Defs

namespace ComputationalSecurity

open PMF

variable {M C K St : Type} [Inhabited M]

-- ============================================================
-- Section 1: Construction of (B1_ind, B2_ind)
-- ============================================================

/-- The state type passed from B1_ind to B2_ind in the indistinguishability game.
    Packages (m, h(m), R, st) where st : St is the inner semantic security state,
    so that B2_ind can reconstruct the semantic security experiment from the ciphertext. -/
abbrev St_B (M St : Type) := M × Bit × (M → Bit → Bit) × St

/-- Indistinguishability adversary B1_ind constructed from
    semantic security adversary A1.
    Samples (mDist, h, R, st) ← A1, m ← mDist,
    outputs (m0 = m, m1 = default, stB = (m, h(m), R, st)).
    The fixed plaintext m1 = default is shared with S_sim. -/
noncomputable def B1_ind
    (A1 : PMF (PMF M × (M → Bit) × (M → Bit → Bit) × St)) :
    PMF (M × M × St_B M St) :=
  do
    let (mDist, h, R, st) ← A1
    let m ← mDist
    PMF.pure (m, default, m, h m, R, st)

/-- Indistinguishability adversary B2_ind wrapping semantic security adversary A2.
    Receives ciphertext c and state stB = (m, hval, R, st),
    unpacks stB to recover (m, hval, R, st), runs a ← A2(c, hval, st),
    outputs R(m, a). -/
noncomputable def B2_ind
    (A2 : C → Bit → St → PMF Bit) :
    C → St_B M St → PMF Bit :=
  fun c (m, hval, R, st) => do
    let a ← A2 c hval st
    PMF.pure (R m a)

-- ============================================================
-- Section 2: Construction of simulator S_sim
-- ============================================================

/-- Simulator S_sim constructed from (Enc, Gen, A2).
    Has type Bit → St → PMF Bit, matching exactly the type of any simulator for A2.
    Receives (hval, st) just like A2 (S simulates A2, not B2_ind).
    Generates k' ← Gen, encrypts the fixed plaintext default : M,
    runs A2(Enc k' default, hval, st), and returns A2's output directly.
    Uses the same fixed plaintext m' = default as B1_ind, ensuring p1 = ps.
    S has no access to the ciphertext; it only sees h(m) and st.
    This matches the textbook simulator on p.37. -/
noncomputable def S_sim
    (Enc : K → M → C) (Gen : PMF K)
    (A2 : C → Bit → St → PMF Bit) :
    Bit → St → PMF Bit :=
  fun hval st => do
    let k' ← Gen
    let a ← A2 (Enc k' default) hval st
    PMF.pure a

-- ============================================================
-- Section 3: Key equalities
-- ============================================================

/-- p0(Enc, Gen, B1_ind A1, B2_ind A2) = pa(Enc, Gen, A1, A2).
    The indistinguishability game encrypting m0 = m equals
    the semantic security game: both compute Enc_k(m) and feed it to A2,
    then check R(m, a). Reference: textbook p.37. -/
lemma p0_eq_pa
    (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (PMF M × (M → Bit) × (M → Bit → Bit) × St))
    (A2 : C → Bit → St → PMF Bit) :
    p0 Enc Gen (B1_ind A1) (B2_ind A2) = pa Enc Gen A1 A2 := by
  simp only [p0, pa, B1_ind, B2_ind, bind_assoc]
  simp only [Bind.bind, PMF.pure_bind]

/-- p1(Enc, Gen, B1_ind A1, B2_ind A2) = ps(A1, S_sim Enc Gen A2).
    The indistinguishability game encrypting m1 = default equals
    the simulator's game: both compute Enc_{k'}(default) and feed it to A2,
    then check R(m, a). The key distributions are identical (both use Gen).
    Reference: textbook p.37. -/
lemma p1_eq_ps
    (Enc : K → M → C) (Gen : PMF K)
    (A1 : PMF (PMF M × (M → Bit) × (M → Bit → Bit) × St))
    (A2 : C → Bit → St → PMF Bit) :
    p1 Enc Gen (B1_ind A1) (B2_ind A2) =
    ps (St := St) A1 (S_sim Enc Gen A2) := by
  simp only [p1, ps, B1_ind, B2_ind, S_sim, bind_assoc]
  simp only [Bind.bind, PMF.pure_bind]

-- ============================================================
-- Section 4: Main theorem
-- ============================================================

/-- Theorem 3.2: (t + tM + th + tR, ε)-Indistinguishability implies
    (t, tGen + tEnc, ε)-Semantic Security.

    Uses Indistinguishable_without_hne (no distinctness condition on plaintexts)
    so that B1_ind (which outputs m1 = default regardless of m) can be applied
    directly. The [Inhabited M] hypothesis provides the fixed plaintext default
    shared between B1_ind and S_sim.

    Parameters:
    - t    : complexity budget for the semantic security adversary (A1, A2)
    - tM   : complexity for sampling a plaintext from mDist (output of A1)
    - th   : complexity for evaluating the partial information function h
    - tR   : complexity for evaluating the relation R
    - tGen : complexity for key generation (Gen)
    - tEnc : complexity for encryption (Enc)
    - ε    : distinguishing advantage bound

    Reference: Theorem 3.2, textbook p.36. -/
theorem indistinguishable_implies_semantically_secure
    (Enc : K → M → C) (Gen : PMF K)
    (t tM th tR tGen tEnc : ℕ) (ε : NNReal)
    (hind : Indistinguishable (St := St_B M St)
              Enc Gen (t + tM + th + tR) ε) :
    SemanticallySecure (St := St) Enc Gen t (tGen + tEnc) ε := by
  -- Introduce A1, A2, complexity bounds from SemanticallySecure
  intro A1 A2 tA1 tA2 htA
  -- Witness: S_sim Enc Gen A2, with type Bit → St → PMF Bit
  refine ⟨S_sim Enc Gen A2, tA1 + tA2 + (tGen + tEnc), le_refl _, ?_⟩
  -- Apply Indistinguishable_without_hne to (B1_ind A1, B2_ind A2)
  have hind_ineq :
      |(p0 Enc Gen (B1_ind A1) (B2_ind A2)).toReal -
       (p1 Enc Gen (B1_ind A1) (B2_ind A2)).toReal| ≤ (ε : ℝ) := by
    apply hind (B1_ind A1) (B2_ind A2) tA1 tA2
    omega
  -- Rewrite p0 = pa, p1 = ps via key lemmas, conclude
  rw [p0_eq_pa, p1_eq_ps] at hind_ineq
  exact hind_ineq

end ComputationalSecurity
