/-
  Definitions for computational security of symmetric encryption.
  Formalizes Definition 3.4 (Semantic Security) and
  Definition 3.5 (Indistinguishability) from the textbook.

  Reference: Chapter 3, "Computational Security"
  Authors: Yasuaki Honda
-/

import ComputationalSecurity.ProbabilityUtils
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace ComputationalSecurity

open PMF

variable {M C K St : Type}

-- ============================================================
-- Correctness
-- ============================================================

/-- Correctness property of a symmetric encryption scheme.
    Decrypting an encrypted plaintext with the same key recovers the original plaintext:
    Dec(k, Enc(k, m)) = m for all keys k and plaintexts m. -/
def correctness (Enc : K → M → C) (Dec : K → C → M) : Prop :=
  ∀ (k : K) (m : M), Dec k (Enc k m) = m

-- ============================================================
-- Definition 3.4: Semantic Security
-- ============================================================

/-- Success probability of adversary A2 when given the actual ciphertext (pa in Def 3.4).
    A1 outputs a plaintext distribution mDist, partial information function h : M → Bit,
    relation R : M → Bit → Bit, and state st.
    A key k is sampled from Gen, a plaintext m from mDist, and A2 receives
    the ciphertext Enc(k, m), the partial info h(m), and the state st,
    then outputs a guess a : Bit. The returned value is the probability that R(m, a) = 1,
    i.e., that A2 successfully computes the target function of m. -/
noncomputable def pa
    (Enc : K → M → C)
    (Gen : PMF K)
    (A1 : PMF (PMF M × (M → Bit) × (M → Bit → Bit) × St))
    (A2 : C → Bit → St → PMF Bit) : ENNReal :=
  (do
    let (mDist, h, R, st) ← A1
    let m ← mDist
    let k ← Gen
    let a ← A2 (Enc k m) (h m) st
    PMF.pure (R m a)) 1

/-- Success probability of simulator S without the ciphertext (ps in Def 3.4).
    S receives only the partial information h(m) : Bit and the state st,
    with no access to the ciphertext or the key.
    The returned value is the probability that R(m, s) = 1,
    where s : Bit is the simulator's output. -/
noncomputable def ps
    (A1 : PMF (PMF M × (M → Bit) × (M → Bit → Bit) × St))
    (S : Bit → St → PMF Bit) : ENNReal :=
  (do
    let (mDist, h, R, st) ← A1
    let m ← mDist
    let s ← S (h m) st
    PMF.pure (R m s)) 1

/-- Definition 3.4: (t, α, ε)-Semantic Security.
    An encryption scheme (Enc, Gen) is (t, α, ε)-semantically secure if
    for every adversary (A1, A2) with combined complexity tA1 + tA2 ≤ t,
    there exists a simulator S with complexity tS ≤ tA1 + tA2 + α such that
    the advantage |pa - ps| is at most ε.

    Here t bounds the adversary's total complexity, α is the additional complexity
    budget allowed for the simulator, and ε : NNReal is the maximum advantage,
    consistent with the textbook where ε is a nonneg real number. -/
def SemanticallySecure
    (Enc : K → M → C)
    (Gen : PMF K)
    (t α : ℕ) (ε : NNReal) : Prop :=
  ∀ (A1 : PMF (PMF M × (M → Bit) × (M → Bit → Bit) × St))
    (A2 : C → Bit → St → PMF Bit)
    (tA1 tA2 : ℕ),
    tA1 + tA2 ≤ t →
    ∃ (S : Bit → St → PMF Bit) (tS : ℕ),
      tS ≤ tA1 + tA2 + α ∧
      |(pa Enc Gen A1 A2).toReal - (ps A1 S).toReal| ≤ (ε : ℝ)

-- ============================================================
-- Definition 3.5: Indistinguishability
-- ============================================================

/-- Probability that adversary A2 outputs 1 when m0 is encrypted (p0 in Def 3.5).
    A1 outputs a pair of plaintexts (m0, m1) and state st.
    A key k is sampled from Gen, and A2 receives the ciphertext Enc(k, m0)
    and state st, then outputs a Bit. -/
noncomputable def p0
    (Enc : K → M → C)
    (Gen : PMF K)
    (A1 : PMF (M × M × St))
    (A2 : C → St → PMF Bit) : ENNReal :=
  (do
    let (m0, _, st) ← A1
    let k ← Gen
    A2 (Enc k m0) st) 1

/-- Probability that adversary A2 outputs 1 when m1 is encrypted (p1 in Def 3.5).
    A1 outputs a pair of plaintexts (m0, m1) and state st.
    A key k is sampled from Gen, and A2 receives the ciphertext Enc(k, m1)
    and state st, then outputs a Bit. -/
noncomputable def p1
    (Enc : K → M → C)
    (Gen : PMF K)
    (A1 : PMF (M × M × St))
    (A2 : C → St → PMF Bit) : ENNReal :=
  (do
    let (_, m1, st) ← A1
    let k ← Gen
    A2 (Enc k m1) st) 1

/-- Definition 3.5: (t, ε)-Indistinguishability.
    An encryption scheme (Enc, Gen) is (t, ε)-indistinguishable if
    for every adversary (A1, A2) with combined complexity at most t
    that only outputs distinct plaintext pairs (m0 ≠ m1),
    the advantage |p0 - p1| in distinguishing encryptions of m0 and m1 is at most ε.

    The condition A1 (m0, m1, st) > 0 → m0 ≠ m1 formalizes that the
    distinguishing game is only meaningful for distinct plaintexts, consistent
    with the textbook where the adversary is required to output two distinct messages.
    ε : NNReal is consistent with the textbook where ε is a nonneg real number. -/
def Indistinguishable
    (Enc : K → M → C)
    (Gen : PMF K)
    (t : ℕ) (ε : NNReal) : Prop :=
  ∀ (A1 : PMF (M × M × St))
    (_ : ∀ m0 m1 st, A1 (m0, m1, st) > 0 → m0 ≠ m1)
    (A2 : C → St → PMF Bit)
    (tA1 tA2 : ℕ),
    tA1 + tA2 ≤ t →
    |(p0 Enc Gen A1 A2).toReal - (p1 Enc Gen A1 A2).toReal| ≤ (ε : ℝ)

end ComputationalSecurity
