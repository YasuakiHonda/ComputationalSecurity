/-
  Definitions for Pseudorandom Generators (PRGs).
  Formalizes Definitions 4.3 and 4.4 from the textbook.

  Reference: Chapter 4, "Pseudorandomness"
  Authors: Yasuaki Honda
-/

import ComputationalSecurity.DistInd

namespace ComputationalSecurity

open PMF
open BVCryptGame

/-- Definition 4.3: Pseudorandom Distribution.
    A distribution X over {0,1}^n is (t, ε)-pseudorandom if
    it is (t, ε)-indistinguishable from the uniform distribution U n. -/
def IsPseudorandom {n : ℕ} (X : PMF (BitVec n)) (t : ℕ) (ε : NNReal) : Prop :=
  DistIndistinguishable X (U n) t ε

/-- Definition 4.4: (t, ε)-Pseudorandom Generator (PRG).
    A function G : {0,1}^n → {0,1}^m is a (t, ε)-PRG if
    1. The output length m is greater than the input length n (expansion).
    2. The distribution G(s) where s ← U n is (t, ε)-pseudorandom. -/
def IsPRG {n m : ℕ} (G : BitVec n → BitVec m) (t : ℕ) (ε : NNReal)
      [Fintype (BitVec n)] [Fintype (BitVec m)] : Prop :=
  (n < m) ∧ IsPseudorandom (PMF.map G (U n)) t ε

end ComputationalSecurity
