# ComputationalSecurity

A Lean 4 + Mathlib 4 formalization of computational security for symmetric encryption,
covering the equivalence between **Semantic Security** and **Indistinguishability** (Chapter 3),
and **Pseudorandomness** including computational indistinguishability of distributions,
the Hybrid Argument, and security under PRG-based key generation (Chapter 4).

Based on: Yasunaga, *Computational Security* (textbook), Chapters 3 and 4.

## What This Project Proves

### Chapter 3: Semantic Security and Indistinguishability

The project formalizes two definitions of security for symmetric encryption and
proves their equivalence:

- **Definition 3.4 — Semantic Security**: No efficient adversary can compute any partial
  function of a plaintext significantly better with the ciphertext than without it.
- **Definition 3.5 — Indistinguishability**: No efficient adversary can distinguish the
  encryption of two chosen plaintexts.

- **Theorem 3.1** (`SemSec_Implies_Ind.lean`): (t, α, ε/2)-Semantic Security ⟹ (t, ε)-Indistinguishability
- **Theorem 3.2** (`Ind_Implies_SemSec.lean`): (t, ε)-Indistinguishability ⟹ (t, α, ε)-Semantic Security

Both theorems are fully proved with no `sorry`.

### Chapter 4: Pseudorandomness

- **Definition 4.1 — Computational Indistinguishability of Distributions** (`DistInd.lean`):
  Two distributions X and Y are (t, ε)-indistinguishable if no efficient distinguisher
  can tell them apart with advantage greater than ε.
- **Proposition 4.1 — Closure** (`DistInd.lean`): Computational indistinguishability is
  preserved under efficient computation (if X ≈ Y then f(X) ≈ f(Y)).
- **Hybrid Argument** (`DistInd.lean`): Formalization of the hybrid lemma and transitivity
  of indistinguishability.
- **Definitions 4.3, 4.4 — Pseudorandom Distribution and PRG** (`DistInd.lean`).
- **Security Transfer Theorem** (`ShortKey_CompSec.lean`): If an encryption scheme is
  perfectly secret under a uniform key, replacing the key with the output of a PRG
  yields a computationally secure scheme.
- **OTP + PRG Security** (`ShortKey_CompSec.lean`): The one-time pad with a PRG key is
  computationally secure (`OTP_PRG_fixed_security`).
- **Equivalence of Fixed-Message and Adversarial Indistinguishability**
  (`ShortKey_CompSec.lean`): `FixedMessageIndistinguishable ↔ Indistinguishable`
  for all state types `St`.

All results are fully proved with no `sorry`.

## Build

Requires [elan](https://github.com/leanprover/elan) and an internet connection to download Mathlib.

```
lake clean; lake update; lake exe cache get; lake build
```

Toolchain: `leanprover/lean4:v4.29.0-rc4`, Mathlib `v4.29.0-rc4`.

## Repository Structure

```
ComputationalSecurity/
├── ComputationalSecurity.lean        # Top-level import aggregator
└── ComputationalSecurity/
    ├── ProbabilityUtils.lean         # Shared probability utilities
    ├── Defs.lean                     # Core definitions (Def 3.4, 3.5)
    ├── GuessingLemma.lean            # Lemma 3.1 (Guessing Lemma)
    ├── SemSec_Implies_Ind.lean       # Theorem 3.1
    ├── Ind_Implies_SemSec.lean       # Theorem 3.2
    ├── DistInd.lean                  # Chapter 4: Def 4.1, Prop 4.1, Hybrid Argument, PRG
    └── ShortKey_CompSec.lean         # OTP, Security Transfer, FixedMessageIndistinguishable
```

## File Descriptions

### `ProbabilityUtils.lean`
Shared utilities used throughout the project. Defines `Bit` (`Fin 2`), `randomBit` (uniform PMF over `Bit`), and `Pr` (probability of a `PMF Bool` outputting `true`). Also provides helper lemmas for ENNReal arithmetic and PMF bounds used in the main proofs.

### `Defs.lean`
Core definitions of the two security notions, following the textbook.

- `pa` / `ps`: success probabilities for the real and ideal experiments in the semantic security game.
- `p0` / `p1`: probabilities of outputting 1 when encrypting `m0` or `m1` in the indistinguishability game.
- `SemanticallySecure`: Definition 3.4.
- `Indistinguishable`: Definition 3.5.

Adversary state is parameterized by a type variable `St`, allowing stateful adversaries. Probabilities are represented as `ENNReal` with `.toReal` at the inequality boundary, consistent with Mathlib's PMF library.

### `GuessingLemma.lean`
Formalization of Lemma 3.1. Given a distinguisher `A` that tells apart two distributions `X 0` and `X 1`, the lemma constructs a guesser that correctly identifies which distribution a sample came from with probability greater than 1/2.

- `guessing_lemma_case1`: When `Pr[A=1|X 1] - Pr[A=1|X 0] > ε`, the original `A` is used as the guesser.
- `guessing_lemma_case2`: When `Pr[A=1|X 0] - Pr[A=1|X 1] > ε`, the flipped adversary `flipA A` is used instead. 
- `guessing_lemma_abs`: The combined absolute-value version used in practice.

### `SemSec_Implies_Ind.lean`
Proof of Theorem 3.1. The key technique is a direct **Advantage Equality**:

```
pa - ps  =  1/2 * (p1 - p0)
```

This is established by decomposing global probabilities into per-sample local probabilities, then summing over the support of the adversary's message distribution. The approach naturally handles the degenerate case `m0 = m1` (both sides are zero), eliminating the need for a distinctness hypothesis on adversary outputs.

### `Ind_Implies_SemSec.lean`
Proof of Theorem 3.2. Constructs an indistinguishability adversary `(B1_ind, B2_ind)` from a semantic security adversary `(A1, A2)`, and a simulator `S_sim` that encrypts a fixed default plaintext. The state type `St_B M St = M × Bit × (M → Bit → Bit) × St` packages the semantic security state for use inside the indistinguishability game. Uses `Indistinguishable` directly (no distinctness condition on plaintexts), since `B1_ind` may output `m = default`.

### `DistInd.lean`
Formalizes the core concepts of Chapter 4.

- `PrDX_one`: the probability that a distinguisher outputs 1 on a sample from distribution X.
- `DistIndistinguishable`: Definition 4.1, (t, ε)-computational indistinguishability of distributions.
- `closure` (Prop. 4.1): indistinguishability is preserved under efficient computation;
  if X ≈ Y then `(X >>= A) ≈ (Y >>= A)`.
- `hybrid_sum_inequality`, `hybrid_lemma`: the Hybrid Argument — if the total distance
  between X₀ and Xₗ exceeds ε, some adjacent pair Xᵢ and Xᵢ₊₁ has distance > ε/l.
- `transitivity`: indistinguishability is transitive via the hybrid argument.
- `U`: the uniform distribution over `BitVec n`.
- `IsPseudorandom`, `IsPRG`: Definitions 4.3 and 4.4.

### `ShortKey_CompSec.lean`
Definitions and theorems connecting perfect secrecy, PRGs, and computational security.

- `Enc_dist`: the ciphertext distribution induced by encrypting a fixed message under a random key.
- `ind_perfect_secrecy`: indistinguishability-based definition of perfect secrecy.
- `OTP_Enc`, `OTP_Dec`, `OTP_Gen`, `OTP_is_ind_perfectly_secret`: the one-time pad and its perfect secrecy proof.
- `security_transfer`: if `Enc` is perfectly secret under `U m`, replacing the key with
  a PRG `G` yields `DistIndistinguishable` ciphertext distributions (generalization of Prop. 4.4).
- `FixedMessageIndistinguishable`: the per-message-pair version of `Indistinguishable`.
- `OTP_PRG_fixed_security`: the OTP with a PRG key satisfies `FixedMessageIndistinguishable`.
- `indistinguishability_equivalence`: `FixedMessageIndistinguishable ↔ Indistinguishable`
  for all state types `St`. Proved via an expectation argument (forward) and a point-mass
  reduction with `St = Unit` (reverse).

## Design Choices

| Choice | Rationale |
|---|---|
| `Bit = Fin 2` | Consistent with textbook notation; avoids `Bool` coercions |
| `ENNReal` for probabilities | Native type for Mathlib's `PMF`; `.toReal` used at inequality boundaries |
| `St` type parameter for adversary state | Enables stateful adversaries without fixing a concrete state type |
| `NNReal` for advantage bound `ε` | Matches textbook (ε ≥ 0); simplifies inequality reasoning |


## Authors

Yasuaki Honda, with AI assistance (Claude / Google AI Studio).
