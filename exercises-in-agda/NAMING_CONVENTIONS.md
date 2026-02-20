# Naming Conventions

This document describes the naming conventions followed throughout the
formalization, intended both as a reference and as a guide for future work.

---

## 1. General Rules

### The camelCase / hyphen-case Split

There are two distinct naming styles for definitions, selected by the *nature*
of the definition:

- **camelCase** — for *computational functions*: definitions whose focus is on
  value-level computation, i.e. the kind of function that could be defined in
  weaker systems such as STLC, System T, or System F.
  - Examples: `predOrZero`, `posOrZeroOfNat`, `asNatDiff`, `divBy2`, `leftMap`, `mapRightOf`
  - This also includes **unconditional verb-initial names** — names that read
    as imperative commands to manipulate or transform terms, even when the
    result is a proof. Examples: `expandCrossTerm`, `rearrangeFirst`, `swapMiddle`.
  - **Decision procedures** (`decide-{X}`) are conceptually computational
    (they *compute* a decision) and should ideally be camelCase, e.g. `decideEqNat`, `decideUnit`.
- **hyphen-case** — for *propositions, theorems, and proof-relevant
  definitions*: anything whose focus is on proving a property or constructing
  evidence of a mathematical statement.
  - Examples: `add-comm`, `mul-ldistr`, `is-equiv-then-is-emb`, `identity-type-of-a-k-type-is-a-k-type`

The line between "computational" and "propositional" is inevitably blurred in
HoTT (every definition computes), but the intent is clear: a map
`Nat → Nat → Nat` performing arithmetic is computational; a proof
`(m n : Nat) → m + n ≡ n + m` is propositional.

Single-word names (e.g. `add`, `mul`, `pred`, `abs`, `triangular`) and
type-qualified single-operation names (e.g. `Nat-minus`, `Int-succ`) are
not affected by this split — the convention applies when a multi-word
descriptive name is needed.

### Symbols Force Hyphens
When a name embeds a **symbolic operator** (e.g. `+₀`, `ΣΣ`, `↔`), hyphens
are used regardless of whether the definition is computational, because
symbols are not readable in camelCase and underscores are reserved for Agda
mixfix operators. Examples: `swap-+₀`, `swap-ΣΣ-fn`, `swap-ΣΣ-families`.

### CamelCase for Module Names
- **CamelCase is also used for Agda module names** (e.g. `NatBasic`,
  `IntBasic`, `BoolBasic`, `EmptyBasic`).
- This is a separate convention from the camelCase-for-computational rule.

---

## 2. Type / Data Definitions

### Concrete Types
- Named with a short capitalised word: `Nat`, `Bool`, `Int`, `Unit`, `Empty`, `List`.
- Inductive type constructors are lowercase: `zero`, `succ`, `true`, `false`,
  `nil`, `cons`, `unit`, `pair`, `left`, `right`.

### Type Formers & Operators
- Symbolic operators use underscores for mixfix slots:
  `_≡_`, `_+₀_`, `_×_`, `_↔_`, `_≃_`, `_↪_`.
- Named type families use capital initial: `Σ`, `Σ-poly`, `Fin`.

---

## 3. Named Predicates and Properties

### `Is-{property}` (Capital `I`)
Used for **named HoTT predicates** — type-valued propositions about types or functions:

| Pattern | Examples |
|---------|----------|
| `Is-{property}` | `Is-contr`, `Is-prop`, `Is-set`, `Is-equiv`, `Is-emb`, `Is-inj`, `Is-decidable`, `Is-trunc` |
| `Is-{compound}` | `Is-contr-fn`, `Is-coh-invertible`, `Is-decidable-family`, `Is-retract-of`, `Is-trunc-map` |

### `Has-{property}` (Capital `H`)
Used for asserting that a type **possesses** a particular structure:
- `Has-decidable-eq`, `Has-inverse`

### `is-{...}` (Lowercase)
Used for **lemmas/theorems** that *prove* or *relate* such predicates:
- `is-equiv-then-is-emb`, `is-emb-iff-fibs-are-props`,
  `is-emb-preserved-by-homotopy`

---

## 4. Observational Equality Types

Named `Eq-{Type}` with capital `E`:
- `Eq-Nat`, `Eq-Bool`, `Eq-Fin`, `Eq-Σ`, `Eq-Copr`, `Eq-fib`

Reflexivity proofs: `Eq-{Type}-refl` (e.g. `Eq-Nat-refl`, `Eq-Σ-refl`).

---

## 5. Induction Principles

Named `ind-{Type}` or `{Type}-ind`:
- `ind-≡`, `ind-Σ`, `ind-×`, `ind-+₀`, `ind-Bool`, `ind-List`, `ind-Fk`
- `Nat-ind`, `Unit-ind`

Both patterns appear; the `ind-{symbol}` form is preferred for symbolic types
(`ind-Σ`, `ind-+₀`), while `{Type}-ind` is used for named types
(`Nat-ind`, `Unit-ind`).

---

## 6. Theorems About Operations: `{op}-{property-key}`

Arithmetic and algebraic laws follow the pattern
**`{operation}-{property-keyword}`**, optionally qualified by side:

### Property Keywords

| Keyword | Meaning | Example |
|---------|---------|---------|
| `comm`  | commutativity | `add-comm`, `mul-comm` |
| `assoc` / `unassoc` | (un)associativity | `add-assoc`, `mul-unassoc` |
| `lunit` / `runit` | left/right unit | `add-lunit`, `mul-runit` |
| `lzero` / `rzero` | left/right zero (annihilator) | `mul-lzero`, `mul-rzero` |
| `ldistr` / `rdistr` | left/right distributivity | `mul-ldistr`, `mul-rdistr` |
| `inj` | injectivity | `add-inj`, `mul-inj`, `succ-inj` |
| `symm` | symmetry | `min-symm`, `max-symm` |

### Modifiers for Side
- `-left` / `-right`: `add-succ-left`, `add-succ-right`, `add-pred-left`, `add-pred-right`

---

## 7. Implications and Biimplications

### `{A}-then-{B}` for implications (A → B)
- `Is-contr-then-is-prop`, `is-equiv-then-is-emb`, `contr-fn-then-equiv`, `has-decidable-equality-then-is-set`
- Long chains are fine: `is-emb-then-homotope-ap-is-equiv`

### `{A}-iff-{B}` for proposition-level biimplications (A ↔ B)
- Use `-iff-` only when both sides are proposition-valued statements.
- In this codebase, a practical default is:
  - proposition-valued if both sides are named predicates such as `Is-...` / `Has-...`;
  - or if propositionhood is explicit from context (e.g. both sides live in `Props`).
- Examples: `is-emb-iff-fibs-are-props`, `fst-is-emb-iff-is-subtype`, `Set-iff-axiom-K`.

### `{A}-biimpl-{B}` for general biimplications (A ↔ B)
- Use `-biimpl-` as the default when propositionhood of both sides is not built
  into the statement naming/context.
- Examples: `Nat-≡-biimpl-Eq-Nat`, `Bool-≡-biimpl-Eq-Bool`,
  `Fin-≡-biimpl-Eq-Fin`, `leq-biimpl-exists-diff`, `lt-biimpl-succ-leq`.

### `{A}-preserved-by-{B}` for preservation under some operation
- `Is-prop-preserved-by-equiv`, `is-emb-preserved-by-homotopy`

### `{A}-pulled-back-by-{B}`
- `Is-prop-pulled-back-by-equiv`, `is-k-type-pulled-back-by-equiv`

---

## 8. Equivalences, Sections, Retractions

### Naming the maps
- `forward` / `backward` for the two directions of a biimplication or
  equivalence proof (used as local `where`-clause names).

### `{Type}-≃-{Type}` for equivalences between concrete types
- `pair-eq-≃-Eq-Σ`

### `{description}-is-equiv`
- `pair-eq-Eq-Σ-is-equiv`, `fiber-decomposition-is-equiv`, `tr-is-equiv`, `prepend-path-is-equiv`

---

## 9. Concrete-Type Qualified Names: `{Type}-{property}`

When a result is about a specific type, prefix with the type name:

| Type prefix | Examples |
|-------------|----------|
| `Nat-`   | `Nat-ind`, `Nat-is-set`, `Nat-has-decidable-eq`, `Nat-minus` |
| `Int-`   | `Int-succ`, `Int-pred-succ`, `Int-has-decidable-eq` |
| `Bool-`  | `Bool-is-set` |
| `Unit-`  | `Unit-Is-contr`, `Unit-Is-prop`, `Unit-has-decidable-eq` |
| `Empty-` | `Empty-Is-prop` |
| `Leq-Nat-` | `Leq-Nat-refl`, `Leq-Nat-is-prop` |
| `Lt-Nat-`  | (inside `Lt-Nat` module) `lt-succ`, `zero-lt-succ`, `trichotomy` |
| `Fin-`   | `Fin-has-decidable-eq`, `Fin-de-Morgan` |

---

## 10. Abbreviation Glossary

Standard shortened forms used in names:

| Abbreviation | Meaning |
|--------------|---------|
| `ap` | action on paths (functorial action of a map) |
| `apd` | dependent ap |
| `biimpl` | biimplication (general/default connective for `↔`) |
| `cod` | codomain |
| `coh` | coherent |
| `con` | concatenation (of paths) |
| `contr` | contractible |
| `copr` | coproduct |
| `deceq` | decidable equality |
| `dep` | dependent |
| `depfn` | dependent function |
| `distr` | distributivity |
| `dom` | domain |
| `emb` | embedding |
| `eq` | equality |
| `equiv` | equivalence |
| `eqv` | equivalence (variant) |
| `fib` | fiber |
| `fn` | function |
| `fst` | first projection |
| `hcomp` | horizontal composition |
| `htpe` | homotopy (in suffixes: `-lhtpe`, `-rhtpe`) |
| `htpy` | homotopy |
| `inv` | inverse |
| `iff` | biimplication reserved for proposition-level statements |
| `leq` | less-than-or-equal |
| `lt` | less-than |
| `neq` | not equal |
| `obseq` | observational equality |
| `pr₁` / `pr₂` | first/second projection |
| `retr` | retraction |
| `sect` | section |
| `sk` | successor-k (truncation level) |
| `snd` | second projection |
| `succk` | successor-k (truncation level, in type names) |
| `tot` | totalization |
| `tr` | transport |
| `trunc` | truncation |
| `unassoc` | un-associate |

---

## 11. Symbolic Operator Modules

Symbolic aliases for operations are grouped in nested `Symbolic` or
`SymbolicQualified` modules:

- **`Symbolic`**: unqualified operators (`_+_`, `_*_`, `_**_`)
- **`SymbolicQualified`**: type-subscripted operators (`_+ℕ_`, `_*ℕ_`, `_+ℤ_`)

---

## 12. Module Organisation Patterns

- **`{Type}Basic`** module: basic operations on a type (`NatBasic`, `IntBasic`, `BoolBasic`, `EmptyBasic`)
- **`{Symbol}-Basic`** module: operations on a symbolic type (`Σ-Basic`, `+₀-Basic`, `↔-Basic`)
- **`{concept}`** module scoping related definitions (`Is-decidable`, `Has-decidable-eq`, `Leq-Nat`, `Lt-Nat`)
- **`{concept}-Reasoning`** module: equational reasoning combinators (`≡-Reasoning`, `↔-Reasoning`, `≃-Reasoning`, `~-Reasoning`)
- **`exercise-{n}-{m}`** modules for multi-part exercises

---

## Known Exceptions and Legacy Inconsistencies

| Name | Issue | Expected |
|------|-------|----------|
| `neg-bool` | Hyphen-case but computational (`Bool → Bool`) | `negBool` |
| `swap-middle` | Hyphen-case but unconditional verb (local `where` in section-05) | `swapMiddle` |
| `flip-dependent-fn` | Hyphen-case but computational (swaps argument order) | `flipDependentFn` |
| `flip-dependent-biimpl` | Hyphen-case but computational (biimplication of the above) | `flipDependentBiimpl` |
| `flip-biimpl` | Hyphen-case but computational (flips a biimplication) | `flipBiimpl` |
| `decide-Unit` | Hyphen-case but decision procedure | `decideUnit` |
| `decide-Empty` | Same | `decideEmpty` |
| `decide-Eq-Nat` | Same (takes plain `Nat` data) | `decideEqNat` |
| `decide-Fin-depfn` | Same | `decideFinDepfn` |
| `decide-Σ-P` | Decision procedure naming is mixed with symbol-forced hyphenation | keep as-is (symbolic exception) |
| `biimpl` vs `iff` | Mixed usage remains across sections | Use `iff` only when both sides are proposition-valued; otherwise use `biimpl` |

### Style Notes

- Articles (`-a-`) should be elided from names when we can naturally recover them in our mind.
  Current exceptions like `k-type-is-a-succ-k-type` and `identity-type-of-a-k-type-is-a-k-type`
  should drop the `-a-`.

---

## Summary: Constructing Long Descriptive Names

First, determine whether the definition is **computational** (camelCase) or
**propositional** (hyphen-case) per §1.

For **propositional** names, long names are built compositionally from a small
vocabulary, using hyphens:

```
[subject-type]-[operation/concept]-[relationship]-[target/qualifier]
```

For **computational** names, compose descriptively in camelCase
(e.g. `posOrZeroOfNat`, `mapRightOf`, `asNatDiff`).

### Building blocks

1. **Subject** (optional type prefix): `Nat-`, `Bool-`, `Σ-`, `Leq-Nat-`, ...
2. **Core concept**: `add`, `mul`, `equiv`, `emb`, `contr`, `prop`, `trunc`, ...
3. **Relationship connective**:
   - `-then-` (implication)
   - `-iff-` (biimplication when both sides are proposition-valued)
   - `-biimpl-` (general biimplication; default if unsure)
   - `-is-` (asserting a property)
   - `-preserved-by-` / `-pulled-back-by-`
   - `-from-` / `-to-` (conversion direction)
4. **Qualifiers** (appended):
   - `-left` / `-right` (side)
   - `-at` (pointed version, e.g. `singleton-induction-at`)
   - `{-Type}` suffix for target type

### Examples of compositional construction

| Name | Decomposition |
|------|---------------|
| `add-comm` | `add` + `comm` |
| `mul-ldistr` | `mul` + `l` + `distr` |
| `Is-contr-then-is-prop` | `Is-contr` + `then` + `is-prop` |
| `is-emb-iff-fibs-are-props` | `is-emb` + `iff` + `fibs-are-props` |
| `dom-of-equiv-is-prop-iff-cod-is-prop` | `dom-of-equiv` + `is-prop` + `iff` + `cod-is-prop` |
| `is-family-of-equivs-iff-tot-is-equiv` | `is-family-of-equivs` + `iff` + `tot-is-equiv` |
| `map-is-sk-trunc-iff-ap-is-k-trunc` | `map-is-sk-trunc` + `iff` + `ap-is-k-trunc` |
| `has-decidable-equality-then-is-set` | `has-decidable-equality` + `then` + `is-set` |
| `retract-of-contr-is-contr` | `retract-of-contr` + `is-contr` |
| `Σ-≃-sections-at-base-center` | `Σ` + `≃` + `sections-at-base-center` |
