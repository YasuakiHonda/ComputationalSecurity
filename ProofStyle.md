# Proof Style Guide for ComputationalSecurity

This document summarizes the proof style conventions and infrastructure
established in the ComputationalSecurity project.
Read this at the start of a new session before writing or modifying any proof.

---

## 1. Core Philosophy

### Theorem statements
- State theorems at the **`PMF`/`do`-notation level**.
- Use `(U L).map ...` or `do let x ← ...; pure ...` forms.
- Never state theorems in terms of `tsum`, `Finset.sum`, or pointwise probability values.

### Proof structure
- Prove distribution equalities using a **`calc` chain of `do`-expression rewrites**.
- Each `calc` step should be **human-readable**: one meaningful transformation per step,
  with a comment explaining what is happening.
- Each step's justification should use `simp`, `rw`, or `congr`/`funext` at the
  `PMF.map`/`PMF.bind`/`Equiv` level.

### Forbidden descent
- **Never use `PMF.ext` + `tsum`/`Finset.sum` inside a theorem proof.**
- `tsum` and `Finset.sum` are allowed only inside designated **infrastructure lemmas**
  in `ProbabilityUtils.lean` (see Section 3).
- **Never use `getLsbD` index arithmetic or `BitVec.extractLsb'` composition** inside
  a distribution-equality proof. Isolate all such reasoning in a single `have` or
  a dedicated `BitVec` lemma.

---

## 2. BitVec Design Principles

### Avoid `cast`
- **Never put `BitVec.cast (by omega)` inside a recursive definition.**
  Once `cast` enters a recursive definition, it multiplies at every unfolding,
  and each occurrence carries a distinct proof term (e.g., `Decidable.byContradiction ...`),
  making `simp`/`rw` unable to match across occurrences.
- If a `cast` is unavoidable, introduce it with a **named proof**:
  ```lean4
  have h : n + m = L := by omega
  BitVec.cast h x   -- reuse h everywhere instead of (by omega)
  ```

### Use products instead of `++`
- Prefer **`BitVec i × BitVec j`** over `BitVec (i + j)` as the intermediate
  representation in definitions and lemma statements.
- The `++` (append) operator forces a `cast` whenever the length equation is not
  definitionally true, causing the problems above.
- Convert to `BitVec L` only at the **boundary** (the final theorem statement),
  using `bitvec_equiv` or `Equiv`-based infrastructure.

### Abstraction levels for BitVec reasoning
| Level | Tools | When to use |
|---|---|---|
| **Equiv** | `bitvec_equiv`, `tripleEquiv`, `Equiv.prodCongr` | Structural decomposition |
| **Concat/Extract algebra** | `extractLsb'_append_eq_left/right`, `append_assoc` | Relating `++` and `extractLsb'` |
| **Bit arithmetic** | `getLsbD`, `toNat`, `<<<`, `\|\|\|` | Last resort; isolate in one `have` |

When you find yourself writing `BitVec.eq_of_toNat_eq` + `simp [toNat_append]` + `omega`,
that is a signal that the definition above should be redesigned to use products.

### Useful escape hatch (when bit arithmetic is unavoidable)
```lean4
apply BitVec.eq_of_toNat_eq
simp only [BitVec.toNat_cast, BitVec.toNat_append]
simp only [Nat.shiftLeft_eq_mul_pow]
ring
```
`Nat.shiftLeft_comm` does not exist in Mathlib; use `Nat.shiftLeft_eq_mul_pow` + `ring` instead.

---

## 3. Infrastructure Lemmas (`ProbabilityUtils.lean`)

These are the **only** lemmas allowed to use `tsum`/`Finset.sum` directly.
All other proofs must be built on top of these. You can propose new infrasture lemma if needed.

| Lemma | Statement | Note |
|---|---|---|
| `uniformOfFintype_map_equiv` | `(uniformOfFintype α).map e = uniformOfFintype β` | 1 use of `tsum` |
| `uniformOfFintype_prod_eq_bind` | `uniformOfFintype (α × β) = (uniformOfFintype α).bind (fun a => (uniformOfFintype β).map (Prod.mk a))` | 1 use of `tsum` |
| `uniformOfFintype_eq_bind3_of_equiv` | Given `e : α ≃ β × γ × δ`, decomposes `uniformOfFintype α` into 3 nested binds | No `tsum`; uses above two |
| `U_add_dist` | `U (n+m) = do let b1 ← U n; let b2 ← U m; return b1 ++ b2` | Uses `tsum` |
| `boolEquiv` | `Bool ≃ BitVec 1` | Definitional |
| `U1_eq_map_boolEquiv` | `U 1 = (uniformOfFintype Bool).map boolEquiv` | No `tsum` |
| `bitvec_equiv` | `BitVec (n+m) ≃ BitVec n × BitVec m` | Definitional |
| `card_bitvec` | `Fintype.card (BitVec n) = 2^n` | Uses `tsum` |
| `h_split_U` | `U (L-i) = do let pre ← U (L-(i+1)); let b ← U 1; return (pre ++ b).cast (by omega)` | Uses `tsum` |

---

## 4. Useful PMF Rewriting Rules

### Monad laws (use as `simp` lemmas)
```lean4
PMF.bind_assoc     -- (p >>= f) >>= g = p >>= (fun x => f x >>= g)
PMF.pure_bind      -- (pure a) >>= f = f a
PMF.bind_pure      -- p >>= pure = p
PMF.bind_const     -- (p >>= fun _ => q) = q   (when q does not depend on the bound variable)
PMF.map_bind       -- (p >>= f).map g = p >>= (fun x => (f x).map g)
PMF.bind_map       -- (p.map f) >>= g = p >>= (g ∘ f)
```

### Common patterns
```lean4
-- Dropping an unused sample
-- Goal: (do let _ ← U k; pure x) = pure x
exact PMF.bind_const (U k) (PMF.pure x)

-- U 1 ↔ Bool
rw [U1_eq_map_boolEquiv]   -- replaces U 1 with (uniformOfFintype Bool).map boolEquiv
-- or the reverse
rw [← U1_eq_map_boolEquiv]

-- Decomposing U L into 3 independent samples via an Equiv
rw [show U L = ... from uniformOfFintype_eq_bind3_of_equiv (tripleEquiv i)]
```

### `do`-notation pitfalls
- `let b ← p` inside `do` desugars to `Bind.bind`, not `PMF.bind` directly.
  If `rw [PMF.bind_const]` fails, try `exact PMF.bind_const p q` instead.
- Type inference in `do` blocks can fail when the types of bound variables are
  not immediately determined. Fix with explicit type annotations:
  ```lean4
  let b : β ← PMF.uniformOfFintype β
  -- or use explicit bind/pure instead of do notation
  (PMF.uniformOfFintype β).bind (fun b : β => ...)
  ```

---

## 5. Proof Skeleton for Distribution Equality

```lean4
lemma my_lemma ... :
    (U L).map f = (do let x ← D1; let y ← D2; PMF.pure (g x y)) := by
  calc
    (U L).map f
    -- Step 1: rewrite map as do (always rfl or PMF.map_eq)
    _ = (do let x ← U L; PMF.pure (f x)) := by rfl
    -- Step 2: decompose U L via Equiv
    _ = (do let a ← D1; let b ← D2; let c ← D3; PMF.pure (h a b c)) := by
        unfold U
        rw [uniformOfFintype_eq_bind3_of_equiv myEquiv]
        simp only [Equiv.invFun_as_coe, Bind.bind, bind_bind, PMF.pure_bind,
                   Equiv.apply_symm_apply]
    -- Step 3: drop unused sample c
    _ = (do let a ← D1; let b ← D2; PMF.pure (h' a b)) := by
        congr 1; funext a; congr 1; funext b
        exact PMF.bind_const D3 (PMF.pure (h' a b))
    -- Step 4: convert types (e.g., U 1 → Bool)
    _ = (do let x ← D1; let y ← D2; PMF.pure (g x y)) := by
        congr 1; funext x
        rw [U1_eq_map_boolEquiv]
        simp only [PMF.bind_map, Function.comp_def]
        congr 1; funext b; cases b <;> rfl
```

---

## 6. Known Pitfalls and Solutions

| Symptom | Cause | Solution |
|---|---|---|
| `rw [PMF.bind_const]` fails with pattern mismatch | `do` desugars to `Bind.bind`, not `PMF.bind` | Use `exact PMF.bind_const p q` |
| `simp [Functor.map_map]` does nothing | `PMF.map` ≠ `<$>` syntactically | Use `PMF.map` definition or `congr`/`funext` |
| `simp [BitVec.cast_cast]` does nothing | Proof terms in `cast` differ (`Decidable.byContradiction` vs `omega`) | Use `BitVec.eq_of_toNat_eq` + `simp [toNat_cast, toNat_append]` + `ring` |
| `Nat.shiftLeft_comm` not found | Does not exist in Mathlib | `simp [Nat.shiftLeft_eq_mul_pow]; ring` |
| Type error in `do` block: `d` has type `?m.56 b c` | Lean treats bound variables as dependent | Add explicit type annotations `let b : β ←` or use explicit `bind` |
| `uniformOfFintype_eq_bind3_of_equiv` type error on last variable | Same dependency issue | Write as explicit nested `.bind (fun b => .bind (fun c => .bind (fun d => ...)))` |
