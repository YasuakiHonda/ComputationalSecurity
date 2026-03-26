# ComputationalSecurity

A Lean 4 + Mathlib 4 formalization of the equivalence between **Semantic Security** and **Indistinguishability** for symmetric encryption schemes.

Based on: Yasunaga, *Computational Security* (textbook), Chapter 3.

## What This Project Proves

The central result is the equivalence of two definitions of security for symmetric encryption:

- **Definition 3.4 — Semantic Security**: No efficient adversary can compute any partial function of a plaintext significantly better with the ciphertext than without it.
- **Definition 3.5 — Indistinguishability**: No efficient adversary can distinguish the encryption of two chosen plaintexts.

The project formalizes both directions of the equivalence:

- **Theorem 3.1** (`SemSec_Implies_Ind.lean`): (t, α, ε/2)-Semantic Security ⟹ (t, ε)-Indistinguishability
- **Theorem 3.2** (`Ind_Implies_SemSec.lean`): (t, ε)-Indistinguishability ⟹ (t, α, ε)-Semantic Security

Both theorems are fully proved with no `sorry`.

## Build

Requires [elan](https://github.com/leanprover/elan) and an internet connection to download Mathlib.

```
lake update
lake build
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
    └── Ind_Implies_SemSec.lean       # Theorem 3.2
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
- `guessing_lemma_case2`: When `Pr[A=1|X 0] - Pr[A=1|X 1] > ε`, the flipped adversary `flipA A` is used instead. This resolves an ambiguity in the textbook, which uses the same algorithm `A` for both cases.
- `guessing_lemma_abs`: The combined absolute-value version used in practice.

### `SemSec_Implies_Ind.lean`
Proof of Theorem 3.1. The key technique is a direct **Advantage Equality**:

```
pa - ps  =  1/2 * (p1 - p0)
```

This is established by decomposing global probabilities into per-sample local probabilities, then summing over the support of the adversary's message distribution. The approach naturally handles the degenerate case `m0 = m1` (both sides are zero), eliminating the need for a distinctness hypothesis on adversary outputs.

### `Ind_Implies_SemSec.lean`
Proof of Theorem 3.2. Constructs an indistinguishability adversary `(B1_ind, B2_ind)` from a semantic security adversary `(A1, A2)`, and a simulator `S_sim` that encrypts a fixed default plaintext. The state type `St_B M St = M × Bit × (M → Bit → Bit) × St` packages the semantic security state for use inside the indistinguishability game. Uses `Indistinguishable` directly (no distinctness condition on plaintexts), since `B1_ind` may output `m = default`.

## Design Choices

| Choice | Rationale |
|---|---|
| `Bit = Fin 2` | Consistent with textbook notation; avoids `Bool` coercions |
| `ENNReal` for probabilities | Native type for Mathlib's `PMF`; `.toReal` used at inequality boundaries |
| `St` type parameter for adversary state | Enables stateful adversaries without fixing a concrete state type |
| `NNReal` for advantage bound `ε` | Matches textbook (ε ≥ 0); simplifies inequality reasoning |
| No `hne` (m0 ≠ m1) in `Indistinguishable` | Eliminated by the Advantage Equality approach in Thm 3.1, and by using a default plaintext in Thm 3.2 |

## Authors

Yasuaki Honda, with AI assistance (Claude / Google AI Studio).
