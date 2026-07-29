# TsinghuaCFSG — mathematical overview

**Draft.** Companion to `REVIEW.md`: that file is an audit, this one is an exposition of what
the repository contains mathematically, which formalisation choices were forced, and which
were not. Facts about Mathlib quoted below were checked against the pinned copy in
`.lake/packages/mathlib` (v4.32.0).

---

## 1. What is proved

Two theorems, both `sorry`-free and depending only on `propext`, `Classical.choice`,
`Quot.sound`.

**The Feit–Thompson odd order theorem** — `FeitThompson/FinalTheorem.lean`:

```lean
theorem odd_order_theorem :
    ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G
```

Stated entirely in Mathlib vocabulary, so nothing defined in this repository can weaken it.

**Suzuki's theorem on doubly transitive groups** — `BenderSuzuki/Suzuki.lean`:

```lean
theorem suzuki {G Ω} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA : HypothesisA G Ω H D Q t) :
    ∃ (L : Subgroup G) (_ : L.Normal) (q : ℕ),
      Odd (Nat.card (G ⧸ L)) ∧ (∃ n, q = 2 ^ n) ∧ 2 < q ∧ ( … three cases … )
```

with the three cases identifying `L` as `PSL₂(2ᵏ)`, `Sz(2^(2k+1))` or `PSU₃(q)` **together with
its permutation action on `Ω`** — each case carries an explicit equivariance clause
`eΩ (l • ω) = ρ (eL l) (eΩ ω)`, so the conclusion is an isomorphism of permutation groups, not
merely of abstract groups.

---

## 2. The mathematical route

### 2.1 Sources

The odd order theorem is not formalised from Feit–Thompson's 1963 paper but from the modern
two-volume rewriting:

* **Bender–Glauberman**, *Local Analysis for the Odd Order Theorem*, LMS 188 (1994)
  → `FeitThompson/BGsection1…16`, `BGappendixC`
* **Peterfalvi**, *Character Theory for the Odd Order Theorem*, LMS 272 (2000), Part I
  → `FeitThompson/PFsection1…14`

and the module decomposition is the one used by the Coq math-comp/odd-order development
(`BGsection*.v`, `PFsection*.v`, `stripped_odd_order_theorem.v` ↦ `FinalTheorem.lean`).

`BenderSuzuki/` formalises Peterfalvi Part II (Suzuki's classification of the 2-transitive
groups of this shape — Zassenhaus groups of even degree / split BN-pairs of rank 1 in
characteristic 2), with `BenderSuzuki/External/` supplying the classical prerequisites.

### 2.2 The skeleton of the odd order proof

Everything hangs off one typeclass, `FeitThompson/MinCE.lean`:

```lean
class IsMinCE (G : Type*) [Group G] [Finite G] : Prop where
  odd_order : Odd (Nat.card G)
  simple : IsSimpleGroup G
  not_solvable : ¬ IsSolvable G
  proper_subgroups_solvable : ∀ H : Subgroup G, H < ⊤ → IsSolvable H
```

`minimalCounterexampleReduction_theorem` produces such a `G` from a failure of the theorem
(minimal counterexample of least order; simplicity comes from solvability being closed under
extensions), and the rest of the development derives `False`.

**Local analysis (BG).** Working inside a minimal counterexample, every proper subgroup is
solvable, so `E(H) = 1` and `F*(H) = F(H)` for all proper `H` — which is why components and the
generalized Fitting subgroup never appear (see `REVIEW.md §4`). The chain is:

| block | mathematics | key Lean names |
|---|---|---|
| BG §1–6 | `p`-solvability, Hall subgroups, Fitting theory, chief factors, `Op_{p',p,p'}` | `fittingSubgroup`, `IsHallSubgroup`, `HasPLengthOne`, `StronglyPSolvable` |
| BG §7 | families `𝓗_H(A;π)` of `A`-invariant `π`-subgroups; Hypothesis 7.1 | `section7HFamily`, `Hypothesis7_1` |
| BG §8–9 | the uniqueness theorem; the family 𝓜 of maximal subgroups | `section8HasUniqueMaximalOver`, `section9MaximalSubgroups = {M | IsCoatom M}` |
| BG §10–12 | `M_σ`, `M_α`, the prime sets `σ(M)`, `τ₁/τ₂/τ₃(M)`, `β(M)` | `section10Msigma`, `section12Tau1Primes`, … |
| BG §13–15 | the families 𝓜_F, 𝓜_P; the `K`,`U` data; prime and regular action | `section14MFamilyF/P1/P2`, `section14ActsRegularlyOn`, `section15KUData` |
| BG §16 | Theorems I–III: the type I–V classification of maximal subgroups | `section16MFSubgroup` (`M_F`), `section16TypeI/II`, `section16ASet` |
| BG App. C | the arithmetic theorem: conditions (A) and (B) force `p ≤ q` | `appendixCConditionA/B`, `appendixC_theorem_C` |

**Character theory (PF).**

| block | mathematics | key Lean names |
|---|---|---|
| PF §1 | characters, induction, restriction, Brauer, the Frobenius–Schur-type count `(1.1)` | `inducedClassFunction`, `scalarProduct`, `IsIrreducibleCharacterOnGroup` |
| PF §2 | the **Dade isometry** for a TI-set `A` with normaliser `L` (Hypothesis 2.2) | `Hypothesis2`, `dadeTransform`, `IsTISubsetWithNormalizer` |
| PF §3 | cyclic TI-sets `W ∖ (W₁ ∪ W₂)`, the `ω_{ij}` character table | `cyclicTISet`, `OmegaSystem` |
| PF §4–7 | **coherence**: extending isometries from `ℤ[S, L#]` to `ℤ[S]` | `hypothesis_5_2_b_statement`, `isCoherentExtension`, `subgroupSupportEnergy` |
| PF §8 | the five types of maximal subgroup, `A(M)`, `A₀(M)`, `A₁(M)`, `M_s` | `typeIDefinitionData`…`typeVDefinitionData`, `a1Set`, `msChoiceSource` |
| PF §9–12 | the main coherence theorems for each type (the bulk: 210k lines) | `theorem_9_11_*`, `dadeIsometryRelativeToTypeIASet` |
| PF §13 | Hypothesis (13.1): two non-conjugate maximal subgroups `S`, `T` with cyclic `W₁`, `W₂`, `p = |W₂|`, `q = |W₁|` | `hypothesis_13_1_data`, `hypothesis_13_1_sourceData` |
| PF §14 | (14.2): `P ⋊ U ≅ 𝔽_{p^q} ⋊ U*`, and the final contradiction | `theorem_14_2_a_data`, `theorem_14_conclusion` |

**The endgame** is visible in `FinalTheorem.lean`: BG §16 gives a dichotomy — either every
maximal subgroup is of type I (`bg16AllMaximalTypeI`, refuted by
`not_bg16AllMaximalTypeI_of_isMinCE`), or the PF (8.8)(b) configuration holds. The latter feeds
PF §13, then PF (14.2) produces the field model `P ≅ 𝔽_{p^q}` with `|U| = (p^q−1)/(p−1)`
coprime to `p−1` — Appendix C condition (A) — plus an embedding giving condition (B). Theorem C
then forces `p ≤ q`, contradicting `q < p` from Hypothesis (14.1).

### 2.3 The Suzuki side

`HypothesisA` (= (A1)+(A2)+(A3), `PFchapter1section1/Basic.lean`) says: `G` acts 2-transitively
and faithfully on `Ω`, `H` is a point stabiliser, `t` is an involution outside `H`,
`D = H ∩ Hᵗ`, `H = Q ⋊ D` with `|Q|` even and `|D|` odd, and `G` has 2-rank ≥ 2. It is
satisfiable — `A₅` on 5 points — so the theorem is not vacuous.

The proof is by induction on `|G|` and runs through Peterfalvi's chapters 1–4 with
`K = {x ∈ D | xᵗ = x⁻¹}`, `V = C_D(t)`, `W = C_V(K)`, and a distinguished involution `s`.
The classical inputs are **formalised rather than assumed** (165k lines): Huppert I–V, XI
(110k), Higman on Suzuki 2-groups (37k), Suzuki V–VI (9k), Isaacs (4k), Hall on near-fields
(4k). The target groups are concrete: `SuzukiMatrixSubgroup m` is generated by the standard
root, torus and Weyl matrices over `GF(2^(2m+1))`, and the Suzuki–Tits ovoid appears as
`(xy + x^σx² + y^σ, y, x, 1)` with `σ = 2^(k+1)`.

---

## 3. Definitional changes that were forced, and why

These are the places where the Lean text *has* to differ from the books. They are the main
reason the development is large, and they are, on the whole, handled correctly.

### 3.1 Subgroups of subgroups (the dominant cost)

The books treat `F(M)`, `M'`, `O_p(M)`, `Z(M)`, `C_M(x)` as subgroups of the ambient `G`
without comment. In Lean, `Subgroup ↥M` and `Subgroup G` are different types, so every such
object needs an explicit transport, and every statement needs to choose a side. Hence a whole
parallel vocabulary:

```lean
ambientDerivedSubgroup H := (derivedSubgroup ↥H).map H.subtype
piCoreIn π H            := (piCore π ↥H).map H.subtype
section16PCoreIn p H    := (pCore p.val H).map H.subtype
elementCentralizerIn L a := L ⊓ Subgroup.centralizer {a}
subgroupCentralizerIn, centerIn, fittingSubgroupOf, section10NormalIn, section16HallSubgroupOf, …
```

plus `H.subgroupOf M` in the other direction, and bridging lemmas such as
`natCard_subgroupOf_eq`. This is unavoidable, and it accounts for a large share of both the
vocabulary and the line count. `section16HallSubgroupOf H K := ∃ _ : H ≤ K, IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf K)`
is a typical, correct instance of the pattern.

### 3.2 There is no class-function API in Mathlib

Checked: Mathlib has `Representation.character` and `FDRep.character`, but **no class-function
space, no induction or restriction of class functions, and no Frobenius reciprocity in that
form**. All of PF is about class functions supported on subsets, isometries between spaces of
virtual characters, and induction between subgroups — so this had to be built from nothing:

```lean
abbrev ClassFunction (G : Type*) := G → ℂ
def IsClassFunction (f : ClassFunction G) := ∀ x g, f (x * g * x⁻¹) = f g
def inducedClassFunction (H : Subgroup G) (θ) : ClassFunction G :=
  fun g => (Nat.card H : ℂ)⁻¹ * ∑ x : G, if h : x*g*x⁻¹ ∈ H then θ ⟨_, h⟩ else 0
```

The induction formula, restriction, `scalarProduct`, `IsVirtualCharacter` and
`IsIrreducibleCharacterOnGroup` are all correct. The *choice* to leave the type unbundled is
defensible — Dade isometries move class functions between `↥M` and `G` across coercions, and a
bundled subtype would add friction at every step — but the price is that invariance is not
enforced by the type and is frequently not asserted (`REVIEW.md §2.2`). A bundled
`ClassFunction` with a `FunLike` instance would have cost less than it looks.

Note that the repository *does* contain a bundled version,
`Representation/Foundations.lean:19: abbrev ClassFunction (G) := ConjClasses G → ℂ`, which is
then not the one used in the PF sections — two answers to the same question, coexisting.

### 3.3 Notions absent from Mathlib

| notion | why it had to be defined | verdict |
|---|---|---|
| Frobenius groups | Mathlib has none (checked) | `IsFrobeniusGroupWithKernelComplement` is correct: `K ⊴ G`, `K.IsComplement' R`, `R ∩ Rᵍ = 1` for `g ∉ R`, both nontrivial |
| `generatorRank` | Mathlib's `Group.rank` requires `[Group.FG G]` (`Mathlib/GroupTheory/Rank.lean:33`) | a total `sInf` version, proved equal to `Group.rank`; legitimate, though both are then used |
| elementary abelian, extraspecial, `𝒪_{p',p,p'}`, `p`-length, chief factors, `SCN_n(P)`, near-fields, Hermitian forms, `Sz(q)`, `PSU₃(q)` | not in Mathlib | correct as defined (see `REVIEW.md §11`) |

### 3.4 Totality: junk values

Lean functions are total, so partial mathematical constructions must be given a value
everywhere. This is standard Mathlib practice (`Nat.div` by zero, `Classical.choice`-based
inverses), and the repository follows it: `dadeTransform` returns `0` off `dadeSupport` and
`Classical.choose`s a representative on it, with well-definedness supplied separately by
`Hypothesis2` and used only through `agreesWithDadeTransform`.

The pattern is right; the particular execution is not. Because `Classical.choose` is applied to
a proposition that mentions `g`, the chosen representative need not be stable along a
conjugacy class, so `dadeTransform … α` is not even guaranteed to be a class function. A
`Quotient.lift` over `ConjClasses G`, or a choice made once per class, would have fixed this
(`REVIEW.md §2.3`).

### 3.5 `Fact p.Prime` rather than primality in the definition

`IsElementaryAbelian p G` and `IsExtraspecial p G` do not require `p` prime; primality arrives
at use sites via `[Fact p.Prime]`. **This mirrors Mathlib's own convention** — checked:
`IsPGroup p G := ∀ g, ∃ k, g ^ p ^ k = 1` carries no primality either
(`Mathlib/GroupTheory/PGroup.lean:26`). So this is standard practice, not a deviation.

The price is real nonetheless: `IsElementaryAbelian 0 G` is equivalent to `IsMulCommutative G`,
because `Monoid.exponent G ∣ 0` always holds. A statement mentioning `IsElementaryAbelian q Q`
is therefore much weaker than it looks unless `q.Prime` is in scope — in the places checked it
is, but the type does not say so.

### 3.6 Arithmetic in ℕ

Orders and indices are `Nat.card` (modern Mathlib practice, avoids `Fintype` instance
juggling), so subtraction truncates and division is integer division:
`Nat.card U = (p ^ q − 1) / (p − 1)`, `((v − 1 : ℕ) : ℝ)`. There are 476 such casts. All the
ones inspected sit next to primality hypotheses that make them exact, but the invariant is
carried by convention rather than by the types.

### 3.7 Set-level normalisers and TI-sets

The books normalise *subsets* (`A₀(M)`, `W ∖ (W₁ ∪ W₂)`), not just subgroups. Mathlib's
`Subgroup.normalizer` already takes a `Set G` (`Mathlib/Algebra/Group/Subgroup/Defs.lean:668`),
so `Subgroup.normalizer (U : Set G)` throughout is standard usage, and the local `setNormalizer`
is a re-definition of it rather than a new notion.

### 3.8 The minimal counterexample as a typeclass

Making `IsMinCE` a class lets several hundred lemmas be stated with `[IsMinCE G]` and resolved
by instance search instead of threading an explicit hypothesis. This is a genuinely good
adaptation and it works well. Its misuse — putting `IsMinCE G` *inside* `hypothesis_13_1_sourceData`
as a conjunct — is a separate matter (§4).

### 3.9 Statements as `Prop`-valued definitions

`oddOrderTheorem : Prop`, `minimalCounterexampleReduction : Prop` exist so that the statement
itself can be quantified over and manipulated universe-polymorphically
(`¬ oddOrderTheorem.{u} → ∃ G, IsMinCE G`). Unusual, but it has a purpose here.

---

## 4. Deviations from standard practice that were *not* forced

Summarised from `REVIEW.md`; details there.

1. **Hypothesis packages as nested `∧` rather than structures.** `hypothesis_13_1_sourceData`
   is a 24-fold conjunction destructured positionally at every use. This is what produced the
   22 accessor theorems declared in Lean's core `And` namespace (`REVIEW.md §21.4`), including
   fully generic ones like `And.B1 {a b c : Prop} (h : a ∧ b ∧ c) : b`. A `structure` costs
   nothing and gives named fields.
2. **A two-tier statement system.** 638 declarations distinguish `…Data` (what is being
   carried) from `…DefinitionData` / `source…` (what the book says), with bridge lemmas
   between the tiers. The intent — tracking faithfulness — is comprehensible; the effect is
   that the reader must know which tier a name belongs to.
3. **203 `*_statement` `Prop`s, 35 of them dead**, 16 with a same-named theorem that retypes
   the body inline instead of referring to the definition.
4. **`IsMinCE G` as a conjunct of `hypothesis_13_1_sourceData`**, which makes PF §13/§14
   statements vacuous and non-reusable.
5. **Three inequivalent TI notions and four conjugation conventions** in simultaneous use.
6. **Global unscoped notation** `ρ →ₗ σ`, `ρ ≃ₗ σ` reusing Mathlib's linear-map arrows.
7. **Injection into upstream namespaces**: 460 declarations into `Representation`, 46 into
   `Subgroup`, 22 into `And`.
8. **A module-private duplicate of the Section 1 vocabulary** (`PFsection1_1.lean`) shadowing
   the public definitions in `PFsection1_3.lean`.

---

## 5. Definitional errors

| definition | problem |
|---|---|
| `Section1.IsTISubset` | provably `↔ A = ∅` (dead code, but present) |
| `Section13.dadeIsometryRelativeToAZero` | is literally `hypothesis_5_2_b_statement`; ignores `K` and never mentions `A₀(M)`, yet is a field of `hypothesis_13_1_sourceData` |
| `agreesWithInductionOnAZero` | first conjunct replaced by `True` |
| `IsMinimalNormal` | admits `⊥`; consumers work around it with `by_cases M = ⊥` |
| `IsIrreducibleCharacterFamily` | means "pairwise distinct" |
| `supportsSubgroup`, `supportConclusionData` | ignore the subgroup they are named for / documented as placeholders |
| `pfAppendixCModelData` | mixes `y⁻¹Ay` and `yAy⁻¹` in one conjunct; barely satisfiable (dead) |
| `Section1.exponentCondition` | guard inverts the meaning at `n = 1` |

None of these can affect `odd_order_theorem`, whose statement uses no local definition. They do
affect what the intermediate results mean.

---

## 6. How to read this repository

* **Start at** `FeitThompson/FinalTheorem.lean` (bottom) and `BenderSuzuki/Suzuki.lean:446`.
  Those two statements are the contract; everything else is machinery.
* **The name taxonomy**: `…_statement` = a book item as a `Prop`; `…_data` = a hypothesis or
  conclusion package; `source…` / `…DefinitionData` = the book-faithful tier; `…_core`,
  `…_bridge` = glue between tiers; `section⟨n⟩…` = BG section `n` vocabulary;
  `theorem_⟨n⟩_⟨m⟩` = PF item (n.m).
* **Before citing any interior result**, unfold its statement. Roughly 10% of the `Prop`
  definitions were read for this review and several were found not to mean what they are
  named; the sample does not support assuming the rest do.
* **Do not expect the interior to be falsifiable.** Everything downstream of `IsMinCE G` lives
  under a false hypothesis, so no interior statement's meaning is enforced by the kernel.
