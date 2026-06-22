# ComputationalSecurity

A Lean 4 + Mathlib 4 formalization of computational security for symmetric encryption,
covering the equivalence between **Semantic Security** and **Indistinguishability** (Chapter 3),
and **Pseudorandomness** including computational indistinguishability of distributions,
the Hybrid Argument, security under PRG-based key generation,
the **PRG Sequential Extension** (Theorem 4.1) — constructing an L-bit PRG from a 1-bit PRG,
and **Next-Bit Unpredictability** (Theorem 4.2, direction: pseudorandomness implies
next-bit unpredictability).

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
- **Definitions 4.3, 4.4 — Pseudorandom Distribution and PRG** (`PRGDefs.lean`).
  (Previously in `DistInd.lean`; extracted to a dedicated file in refactoring.)
- **Security Transfer Theorem** (`ShortKey_CompSec.lean`): If an encryption scheme is
  perfectly secret under a uniform key, replacing the key with the output of a PRG yields
  computationally indistinguishable ciphertext distributions. Proved via the Hybrid Argument
  with a 2-step hybrid sequence.
- **Indistinguishability from Perfect Secrecy + PRG** (`ShortKey_CompSec.lean`):
  `IndPS_PRG_implies_Computational_Indistinguishability` — perfect secrecy under `U m`
  plus a PRG implies `Indistinguishable` (Definition 3.5) for any state type.
- **OTP + PRG Security** (`ShortKey_CompSec.lean`): `OTP_PRG_implies_Computational_Indistinguishability`
  — the one-time pad with a PRG key satisfies `Indistinguishable` (Definition 3.5).
- **Equivalence of Fixed-Message and Adversarial Indistinguishability**
  (`ShortKey_CompSec.lean`): `FixedMessageIndistinguishable ↔ Indistinguishable`
  for all state types `St`.
- **Theorem 4.1 — PRG Sequential Extension** (`PRG_Sequential_Extension.lean`):
  If `G : {0,1}^n → {0,1}^(n+1)` is a secure PRG, then the sequential construction
  `G' : {0,1}^n → {0,1}^L` (Figure 4.2) is also a secure PRG for any L.
  Proved via an L-step hybrid argument (`Hybrid 0 = U L` through `Hybrid L = G'_dist`).
  Fully proved with no `sorry`.

- **Definition 4.5 — Next-Bit Unpredictability** (`NextBit_Unpredictable.lean`):
  No efficient algorithm can predict the next bit of a pseudorandom sequence given
  all preceding bits with probability greater than 1/2 + ε/2.
- **Theorem 4.2 (direction: PRG → NB unpredictable)** (`NextBit_Unpredictable.lean`):
  If `G'` is `(t + t_extract, ε/2)`-pseudorandom, then `G'` is `(t, ε)`-next-bit
  unpredictable. Proved via a reduction `predictor_to_distinguisher` and the key lemma
  `PrDX_one_U_predictor_eq_half` (for the true uniform distribution, every predictor
  succeeds with probability exactly 1/2).
  Fully proved with no `sorry`.

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
    ├── ProbabilityUtils.lean         # Shared probability and BitVec utilities
    ├── Defs.lean                     # Core definitions (Def 3.4, 3.5)
    ├── GuessingLemma.lean            # Lemma 3.1 (Guessing Lemma)
    ├── SemSec_Implies_Ind.lean       # Theorem 3.1
    ├── Ind_Implies_SemSec.lean       # Theorem 3.2
    ├── DistInd.lean                  # Chapter 4: Def 4.1, Prop 4.1, Hybrid Argument
    ├── PRGDefs.lean                  # Def 4.3, 4.4: IsPseudorandom, IsPRG
    ├── PRG_Sequential_Extension.lean # Theorem 4.1: PRG Sequential Extension
    ├── NextBit_Unpredictable.lean    # Theorem 4.2: PRG implies Next-Bit Unpredictability
    └── ShortKey_CompSec.lean         # OTP, Security Transfer, FixedMessageIndistinguishable
```

## File Descriptions

### `ProbabilityUtils.lean`
Shared utilities used throughout the project. Defines `Bit` (`Fin 2`), `randomBit` (uniform PMF over `Bit`), `Pr` (probability of a `PMF Bool` outputting `true`), and `U` (the uniform distribution over `BitVec n`). Also provides `bitvec_equiv`, `card_bitvec`, `U_add_dist`, `h_split_U`, and related BitVec combinatorial lemmas used in the PRG Sequential Extension proof. Helper lemmas for ENNReal arithmetic and PMF bounds are also included.

Recent additions include `uniformOfFintype_map_equiv` (uniform distribution preserved under
equivalences), `boolEquiv` (`Bool ≃ BitVec 1`), `U1_eq_map_boolEquiv`,
`uniformOfFintype_prod_eq_bind`, and `uniformOfFintype_eq_bind3_of_equiv` — infrastructure
lemmas enabling `tsum`-free proofs at the `map`/`bind`/`Equiv` abstraction level.

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
- `DistIndistinguishable_comm`: symmetry — X ≈ Y implies Y ≈ X.
- `DistIndistinguishable_mono`: monotonicity in t — a bound for larger t implies one for smaller t.
- `closure` (Prop. 4.1): indistinguishability is preserved under efficient computation;
  if X ≈ Y then `(X >>= A) ≈ (Y >>= A)`.
- `hybrid_sum_inequality`, `hybrid_lemma`: the Hybrid Argument — if the total distance
  between X₀ and Xₗ exceeds ε, some adjacent pair Xᵢ and Xᵢ₊₁ has distance > ε/l.
- `transitivity`: indistinguishability is transitive via the hybrid argument.
- `DistIndistinguishable_bind`: indistinguishability is preserved under monadic bind pointwise.

### `PRGDefs.lean`
Defines the core PRG notions extracted from `DistInd.lean` during refactoring.

- `IsPseudorandom`: Definition 4.3 — a distribution is pseudorandom if it is computationally indistinguishable from the uniform distribution.
- `IsPRG`: Definition 4.4 — a function `G` is a PRG if its output distribution is pseudorandom.

### `PRG_Sequential_Extension.lean`
Formalizes Theorem 4.1 and its supporting construction (Figure 4.2).

- `G_ext`, `G'`: the sequential extension of a 1-bit PRG to L bits, collecting one output bit per step.
- `Hybrid`: the i-th hybrid distribution — `(L-i)` uniform random bits followed by `i` PRG bits.
  Boundary cases: `Hybrid 0 = U L` (fully random) and `Hybrid L = G'_dist` (fully PRG).
- `Sequential_Extension_Step`: each adjacent hybrid pair is indistinguishable, reducing to
  the security of the base PRG `G` via `closure`.
- `PRG_Sequential_Extension`: the main theorem — if `G` is `(t + L·cost_G, ε/L)`-secure,
  then `G'` is `(t, ε)`-secure.

### `NextBit_Unpredictable.lean`
Formalizes the direction "pseudorandomness implies next-bit unpredictability" of Theorem 4.2.

- `Pr_predict_success`: probability that algorithm `A` correctly predicts the `(i+1)`-th bit
  of a sample from `X`, given the first `i` bits.
- `NextBitUnpredictable`: Definition 4.5.
- `predictor_to_distinguisher`: reduction turning a next-bit predictor into a distinguisher.
- `tripleEquiv`: equivalence `BitVec L ≃ BitVec i × BitVec 1 × BitVec (L-i-1)`,
  the key structural decomposition for the proof.
- `U_map_pre_bit`: mapping a uniform `L`-bit sample to `(prefix, bit)` equals independent
  sampling — proved at the `map`/`bind`/`Equiv` level without descending to `tsum`.
- `PrDX_one_U_predictor_eq_half`: for the true uniform distribution `U L`, every predictor
  succeeds with probability exactly 1/2.
- `pseudorandom_implies_unpredictable`: the main theorem.

### `ShortKey_CompSec.lean`
Definitions and theorems connecting perfect secrecy, PRGs, and computational security.

- `Enc_dist`: the ciphertext distribution induced by encrypting a fixed message under a random key.
- `ind_perfect_secrecy`: indistinguishability-based definition of perfect secrecy.
- `security_transfer`: if `Enc` is perfectly secret under `U m`, replacing the key with a PRG `G`
  yields `DistIndistinguishable` ciphertext distributions. Proved via the Hybrid Argument
  (`transitivity` with a 2-step hybrid sequence P0 ≈ Q0 = Q1 ≈ P1).
- `FixedMessageIndistinguishable`: the per-message-pair version of `Indistinguishable`.
- `indistinguishability_equivalence`: `FixedMessageIndistinguishable ↔ Indistinguishable`
  for all state types `St`. Proved via an expectation argument (forward) and a point-mass
  reduction with `St = Unit` (reverse).
- `IndPS_PRG_implies_Computational_Indistinguishability`: if `Enc` achieves `ind_perfect_secrecy`
  under `U m` and `G` is a PRG, then the scheme with key `G(s)` satisfies `Indistinguishable`
  (Definition 3.5). Derived from `security_transfer` and `indistinguishability_equivalence`.
- `OTP_Enc`, `OTP_Dec`, `OTP_Gen`, `OTP_is_ind_perfectly_secret`: the one-time pad and its
  perfect secrecy proof.
- `OTP_PRG_implies_Computational_Indistinguishability`: the OTP with a PRG key satisfies
  `Indistinguishable` (Definition 3.5). Derived from `IndPS_PRG_implies_Computational_Indistinguishability`.

## Design Choices

| Choice | Rationale |
|---|---|
| `Bit = Fin 2` | Consistent with textbook notation; avoids `Bool` coercions |
| `ENNReal` for probabilities | Native type for Mathlib's `PMF`; `.toReal` used at inequality boundaries |
| `St` type parameter for adversary state | Enables stateful adversaries without fixing a concrete state type |
| `NNReal` for advantage bound `ε` | Matches textbook (ε ≥ 0); simplifies inequality reasoning |
| `do`-notation for PMF | Consistent with the `Hybrid` definition style; avoids `bind`/`map` syntax mismatch |
| `map`/`bind`/`Equiv` abstraction for proofs | Proofs of distribution equalities are kept at the `PMF.map`/`bind`/`Equiv` level; descent to `tsum`/`Finset.sum` is limited to a small set of infrastructure lemmas (`uniformOfFintype_map_equiv`, `uniformOfFintype_prod_eq_bind`) |

## Authors

Yasuaki Honda, with AI assistance (Claude / Google AI Studio).
