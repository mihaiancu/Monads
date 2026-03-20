# Monad ⟺ Bind

This repository provides a Lean 4 proof that one can get the Category Theory **Monad** laws from the Functional Programming **Bind** laws, and vice versa. We consider the [Category `Type`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Types/Basic.html), where _objects_ are _types_ and _morphisms_ are _functions_.

See the ![Monads diagram](./MonadBind.pdf) for a handwritten schematic view.

---

## 1. Monads in C.T. vs F.P. 

### Category Theory (C.T.)

A **monad** on a category consists of:

- An endofunctor $M$
- **pure** (unit): $\text{pure}_\alpha : \alpha \to M\alpha$
- **map**: $m : (\alpha \to \beta) \to (M\alpha \to M\beta)$
- **join** (multiplication): $\text{join}_\alpha : MM\alpha \to M\alpha$

> In Mathlib 4: `Mathlib.CategoryTheory.Monad.Basic`

### Functional Programming (F.P.)

A **monad** in FP is defined via:

- **pure** (return): $\text{pure}_\alpha : \alpha \to M\alpha$
- **bind**: $\mathtt{>>=} : M\alpha \to (\alpha \to M\beta) \to M\beta$

> In Lean 4: `Init.Prelude` / `Control`; class hierarchy: `Functor` → `Applicative` → `Monad`

Example: $M = \text{Option}$; $\text{Option}\ \alpha = \\{\text{none}\\} \cup \\{\text{some}\ x \mid x : \alpha\\}$

---

## 2. Bind Laws (F.P.)

|  | Law | Name |
|---|-----|------|
| 1 | $x' \mathtt{>>=} \text{pure} = x'$ | Right identity |
| 2 | $(\text{pure}\ x) \mathtt{>>=} f' = f'\ x$ | Left identity |
| 3 | $x' \mathtt{>>=} f' \mathtt{>>=} g' = x' \mathtt{>>=} (\text{fun}\ x => f'\ x \mathtt{>>=} g')$ | Associativity |

---

## 3. Monad Laws (C.T.)

### m is an (endo)functor

```
         f              m f
  α ─────────→ β    Mα ─────────→ Mβ
```

- $(m\ \text{id})\ x' = x'$
- $m\ (g \circ f)\ x' = (m\ g \circ m\ f)\ x'$

### pure is a natural transformation

- $(m\ f)(\text{pure}\ x) = \text{pure}\ (f\ x)$

```
          f
  α ─────────────→ β
  │                 │
  │ pure_α          │ pure_β
  ↓                 ↓
 Mα ────────────→ Mβ
        m f
```

### join is a natural transformation

- $\text{join}\ (m\ (m\ f)\ x'') = m\ f\ (\text{join}\ x'')$

```
        m(m f)
 MMα ──────────→ MMβ
  │                │
  │ join_α         │ join_β
  ↓                ↓
 Mα ────────────→ Mβ
        m f
```

### join is associative

- $\text{join}\ (\text{join}\ x''') = \text{join}\ (m\ \text{join}\ x''')$
  
```
         join_{Mα}
MMMα ──────────→ MMα
 │                │
 │ m(join_α)      │ join_α
 ↓                ↓
MMα  ───────────→ Mα
         join_α
```

### pure is unit

- $\text{join}\ (\text{pure}\ x') = x'$
- $\text{join}\ (m\ \text{pure}\ x') = x'$

```
        pure_{Mα}                  m(pure_α)
  Mα ───────────→ MMα        Mα ───────────→ MMα
   │               │          │               │
   │ id_{Mα}       │ join_α   │ id_{Mα}       │ join_α
   │               │          │               │
   ↓               ↓          ↓               ↓
  Mα ════════════ Mα         Mα ════════════ Mα

```

---

## 4. The Bridge: Translating Between Bind and Monad

### From Bind to Monad (Bind ⟹ Monad)

Given `>>=` and `pure`, define:

$$m\ f\ x' := x' \mathtt{>>=}  (\text{pure} \circ f)$$

$$\text{join}\ x'' := x'' \mathtt{>>=}  \text{id}_{M\alpha}$$

Then the Bind laws imply all the Monad laws.

### From Monad to Bind (Monad ⟹ Bind)

Given `m`, `join`, and `pure`, define:

$$x' \mathtt{>>=} f' := \text{join}\ (m\ f'\ x')$$

Then the Monad laws imply all the Bind laws.

---

## 5. Lean-Mathlib Formalization

The equivalence is fully formalized in `MonadBind_default.lean`:

- **Namespace `BindMonad`** — starts from `[LawfulMonad M]` (Bind laws) and proves all Monad properties:
  - `m_id`, `m_comp` (functor laws)
  - `pure_natural` (naturality of pure)
  - `join_natural` (naturality of join)
  - `join_assoc` (associativity of join)
  - `pure_unity` (left and right unit)

- **Namespace `MonadBind`** — starts from `CategoryTheory.Monad` and proves all Bind laws:
  - `bind_pure` (right identity)
  - `pure_bind` (left identity)
  - `bind_assoc` (associativity)

---

## 7. Self-Contained Formalization with Custom Classes

The file `MonadBind_classes.lean` provides a fully self-contained formalization that does not depend on Mathlib. It defines its own `Bind` and `Monad` type classes and proves the equivalence by constructing instances in both directions.

## References

- [Monad (category theory)](https://en.wikipedia.org/wiki/Monad_(category_theory))
- [Monad (functional programming)](https://en.wikipedia.org/wiki/Monad_(functional_programming))
