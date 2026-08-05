# The converse direction: sources, and how to certify it

This document accompanies `BenderSuzuki/Converse/`, `BenderSuzuki/Classification.lean`
and `comparator/`.

Part I is a certification account, written for a reader who wants to believe the results
without reading the proofs. Part II is a source-critical account: what the formalisation
takes from the literature, and where it departs.

---

# Part I. Certifying the result without reading the proofs

## 1. The trust question

Everything below is machine-checked. On each of the main theorems, `#print axioms` returns
exactly `[propext, Classical.choice, Quot.sound]`, the three axioms of ordinary mathematics
in Lean. There is no `sorry`, no `axiom`, and no `native_decide`.

Machine-checking a proof does not certify a *statement*. A statement can be vacuous, or can
quantify over the wrong objects, and still be proved. The question we address is therefore
not whether the proofs are correct, since the kernel answers that. It is how much a human
must read before believing that the statements say what they should.

## 2. The comparator files

The `comparator/` directory is a challenge/solution pair in the sense of
[leanprover/comparator](https://github.com/leanprover/comparator).

| file | lines | role |
|---|---|---|
| `comparator/Defs.lean` | 253 | the definitions, Mathlib-only. Audit this. |
| `comparator/Challenge.lean` | 56 | four statements, all `sorry`. Audit this too. |
| `comparator/Solution.lean` | 89 | the same four statements, proved. Nobody need read this. |
| `comparator/config.json` | | theorem names and permitted axioms |

The challenge does not import this repository. Its subject matter, namely strong embedding,
Hypothesis (A), and the three groups, is defined in `Defs.lean` from Mathlib primitives
alone. Walking the constants that occur in the four statement types, and closing under
types, definition values, and inductive constructors, we obtain the following.

| statement cone | count |
|---|---|
| total constants | 3786 |
| from `BenderSuzuki` or `FeitThompson` | 0 |
| from `Defs.lean` | 33, or 27 after dropping `_proof_*` |

An earlier version of these files named the repository's own `HypothesisA` and
`suzukiConclusion`. It carried 37 opaque imported definitions that a reader had to accept on
trust. That version is preserved in the git history.

### Why `Defs.lean` is shared rather than copied

The usual shape has the solution restate the challenge's definitions verbatim, and
`Compare.loop` forces the copies to agree. This arrangement does not work at the present scale.
The two files have different import sets, since the solution pulls in the whole repository, and
instance resolution is sensitive to that. On the copy-in-each version we observed three
divergences.

- In `Disjoint`, the element `⊥` elaborated through `BoundedOrder.toOrderBot` in the challenge
  and `CompletePartialOrder.toOrderBot` in the solution.
- `GaloisField 2 m` picked up `Nat.fact_prime_two` in one file and the repository's own `Fact`
  instance in the other.
- The instance `Finite (PSL2Model k)`, left as `_` in the statement, resolved through
  `Subgroup.finiteIndex_of_finite` in the challenge and `Subgroup.finiteIndex_center` in the
  solution.

Comparator compares syntactically, so each of these would be rejected. Byte-identical source
does not give byte-identical elaboration. Sharing the module makes the definitions the same
constants, rather than two copies that have to agree by accident. The third case we fix
instead by binding the instance explicitly in the statement.

The sharing is not a weakening. `Defs.lean` lies in the challenge's import closure, hence in
the trusted base, and the solution cannot vary it.

### Why the solution may import the repository

`Solution.lean` imports `BenderSuzuki.Converse.StronglyEmbedded`, and hence the whole
development. The arrangement is safe by construction, and not by convention.

- `safeExport` runs `lean4export <module> -- <names>`, which exports the transitive closure
  of the named declarations.
- `runKernel` creates a fresh `Lean.mkEmptyEnvironment` and replays that entire closure
  through the kernel. Nothing is trusted from the pre-built `.olean` files: every constant
  in the proof cone is re-typechecked from the exported term.
- `checkAxioms` enforces the whitelist across the same closure, so a `sorry` anywhere in the
  imported development would surface as `sorryAx` and be rejected.
- For the four targets, only the `ConstantVal`, that is the name, the universe parameters,
  and the type, is compared. The proof term is not compared, so it may come from anywhere.

Nothing requires the solution to use the repository. The omission is deliberate, and it is not
a gap: the solution is this repository, so whatever it discharges, this repository proves.

### The full trusted base

By comparator's first assumption, the trusted set is the import closure of `Challenge.lean`
together with `lakefile.toml`. The complete human audit surface is therefore the following.

| | lines |
|---|---|
| `comparator/Defs.lean` | 253 |
| `comparator/Challenge.lean` | 56 |
| the `lakefile.toml` diff | 12 |

Nothing else. Mathlib is assumed; no part of this repository is.

We give no `definition_names` in `config.json`, and this is deliberate. A definition hole is
gameable: comparator's own README warns of it, and a solution could define
`IsStronglyEmbedded := fun _ => True` and discharge everything by `trivial`. Left out of the
holes list, every definition is reached by `Compare.loop` as part of the statement cone.

### The four challenge items

| | question | answer |
|---|---|---|
| 1 | Does Hypothesis (A) imply strong embedding? | `hypothesisA_stronglyEmbedded`: the point stabiliser is strongly embedded. |
| 2 | Is Hypothesis (A) satisfiable at all? Before this work nothing in the repository ever constructed one; every occurrence consumed one, so `suzuki` might have been vacuously true. | `psl2_hypothesisA`: `PSL₂(2ᵏ)` satisfies it for `k ≥ 2`. |
| 3 | Is the Suzuki branch attained? | `suzuki_hypothesisA`: `Sz(2^(2m+1))` satisfies it for `m ≥ 1`. |
| 4 | Is the unitary branch attained? | `psu3_hypothesisA`: for `k ≥ 2` there is a field of order `(2ᵏ)²` with fixed field of order `2ᵏ`, and a Hermitian form of the standard shape, whose `PSU₃` satisfies it. |

Composing 1 with each of 2, 3 and 4 gives that each of the three groups has a strongly
embedded subgroup. Everything the solution supplies is existentially quantified: the set
acted on, the action, `H`, `D`, `Q`, and `t`. The solution cannot substitute a convenient
group of its own.

### What the reader has to recognise, and what they do not

The definition of `PSL2Model` is one line, namely
`Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 k)`. `PSUModel` is the isometry
group of a Hermitian form, cut down to determinant one and pushed into `PGL`. Both are
recognisable on sight.

`SzModel` is not. It is an explicit generator set of 4×4 matrices with a Tits exponent
`2^(m+1)`, and no reader should be asked to recognise `Sz(q)` in it. They are not asked to.
The four statements say that it satisfies Hypothesis (A), and therefore has a strongly
embedded subgroup. Bender's classification then places it in one of the three families, and
the orders separate it from the other two. The awkward definition certifies itself.

Proof terms inside definitions, such as the subgroup closure obligations in
`unitarySubgroup` and the determinant computations in `SzRootGL`, carry no meaning: a
subgroup is determined by its carrier. The audit cost of a 60-line definition with a 4-line
carrier is 4 lines.

### What was verified locally

- `Defs.lean` compiles against Mathlib alone.
- `Challenge.lean` compiles with exactly four `sorry`s and no errors.
- `Solution.lean` compiles with no `sorry`.
- Printing all four statement types with `pp.all` from each module and diffing gives 9305
  identical lines, which is the property comparator itself enforces.
- The command `#print axioms` on all four solution theorems gives
  `[propext, Classical.choice, Quot.sound]`.
- We enumerated the statement cone by a `run_cmd` traversal over types, definition values
  and inductive constructors: it contains no constant of this repository.

Comparator itself was run, and reports `Your solution is okay!`. It builds and exports each
of the two modules inside the sandbox, compares the four statements, checks the axioms, and
replays the solution through a fresh kernel.

A passing run establishes nothing unless the check can fail, so we ran two negative
controls. Replacing one solution proof by `sorry` gives
`Illegal axiom detected: 'sorryAx'`. Weakening one statement, from `0 < m` to `2 <= m`,
gives `Challenge and solution theorem statement do not match`. Both are rejections of the
kind the artifact relies on.

Four adaptations were needed, and we record them because each is a deviation from the
intended setup.

- The shipped `lean4export` targets Lean 4.33.0-rc1 and cannot read our 4.32.0 build,
  failing with `incompatible header`. We rebuilt it from the same source against 4.32.0.
- Release v0.1.17 of `landrun` requires Landlock ABI v9, and this kernel provides v8. We
  used v0.1.14, which runs.
- Comparator grants read access to the system directories but not execute. Since `-ldd` in
  v0.1.14 does not add the ELF interpreter, no dynamically linked binary could start. A
  wrapper adds execute rights on `/usr`, `/lib` and `/lib64`. Writes remain confined to the
  paths comparator specifies, which we verified: reads and writes outside them are refused.
- Lake's artifact cache lies outside the writable set, so the build inside the sandbox
  failed with `failed to cache artifact`. We pointed `HOME` at a directory inside `.lake`.

Comparator's README also asks that the solution not have been compiled beforehand, since a
challenge compiled alongside an adversarial solution could otherwise go unnoticed. This is a
condition on the checking environment rather than on the artifact, and anyone who obtains the
artifact and runs the comparison in a fresh checkout discharges it by construction. We also
discharged it here: we deleted the compiled artifacts of `Defs`, `Challenge` and `Solution`
and ran the comparison again, so that comparator rebuilt all three from source inside the
sandbox. Its own order builds and exports the challenge before the solution is compiled at
all. The result was unchanged.

### Two further questions, outside these files

| | question | answer |
|---|---|---|
| 5 | Were the pre-existing statements weakened to make this work? | `git diff main --stat`: the only pre-existing Lean file touched is `BenderSuzuki.lean`, and only to add import lines. `Suzuki.lean`, `PFchapter1section1/Basic.lean`, and `PFchapter1section3/Basic.lean` are byte-for-byte unchanged. |
| 6 | Are the three matrix groups the groups they claim to be? A file named `SuzukiMatrixGroup` proves nothing about its contents. | See §3 and §4. Strong embedding is exactly this check, and it only goes so far. |

## 3. Why strong embedding is the right certificate

`IsStronglyEmbedded` is not in Mathlib, so it must be read. It is, however, not new code
either: it is the definition `BenderSuzuki/FinalTheorem.lean:15` already states, the one
`bender_suzuki` takes as its hypothesis. The converse lane introduces no notion of its own,
so a reader has a single definition to check and not two.

```lean
def IsInvolution {G : Type*} [Group G] (x : G) : Prop := x ≠ 1 ∧ x ^ 2 = 1

def IsStronglyEmbedded {X : Type*} [Group X] (M : Subgroup X) : Prop :=
  M ≠ ⊤ ∧ (∃ x ∈ M, IsInvolution x) ∧
    ∀ g ∉ M, ∀ x ∈ M ⊓ M.map (MulAut.conj g).toMonoidHom, ¬ IsInvolution x
```

Every symbol (`Subgroup`, `MulAut.conj`, `Subgroup.map`, and the lattice `⊓`) is Mathlib's.
The expression `M.map (MulAut.conj g).toMonoidHom` is `g M g⁻¹`, and we verify this in two
ways: as `rfl` against the pointwise action `MulAut.conj g • M`, and as
`x ∈ M.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ M`.

The proof under Hypothesis (A) naturally produces the parity form -- `|M|` even and
`|M ⊓ M^g|` odd -- and a private lemma converts it by Cauchy's theorem at the prime two.
That form is nowhere stated.

We now give the certification argument. We prove that the three families have strongly
embedded subgroups (`BenderSuzuki/Converse/StronglyEmbedded.lean:139,145,151`), and package
that with `bender_suzuki` as an equivalence
(`BenderSuzuki/Classification.lean:122`).

A group with a strongly embedded subgroup and 2-rank at least two is severely constrained.
By Bender's theorem, which is external to this repository, `G` then has a normal subgroup
`L` of odd index with `L/O(L)` isomorphic to `PSL₂(2ⁿ)`, `Sz(2^(2n+1))`, or `PSU₃(2ⁿ)`. The
2-rank condition is not decoration. Without it the conclusion is false, since in any group
whose Sylow 2-subgroups are cyclic or generalised quaternion the normaliser of a Sylow
2-subgroup is strongly embedded. Both halves are available here: the 2-rank hypothesis is
`A3` of `HypothesisA`, so it is proved for each of the three families alongside the strong
embedding.

A reader who trusts that classical fact, and who has read the three lines of
`IsStronglyEmbedded`, therefore obtains the following.

> Whatever the definitions `PSL2BinaryMatrixGroup`, `SuzukiMatrixGroup`, and
> `ProjectiveSpecialUnitaryMatrixGroup` actually denote, they denote groups in Bender's
> list.

They cannot be trivial, cannot be soluble, and cannot be a matrix group of the wrong shape. The
argument is a cheap check on several thousand lines of matrix-group construction in `External/`
and `MatrixGroups/`, bought for the price of reading a four-line structure.

## 4. The limit of that argument, stated plainly

Strong embedding certifies membership in the list, and not which member. A sceptic should
know exactly where the argument stops.

If `SuzukiMatrixGroup m` had been mis-defined as `PSL₂(2^(2m+1))`, it would still have a
strongly embedded subgroup and would still satisfy Hypothesis (A). Nothing in §3 would
notice. The coincidence is not hypothetical.

| group | degree | order |
|---|---|---|
| `Sz(8)` | 65 | 29 120 |
| `PSL₂(64)` | 65 | 262 080 |
| `PSU₃(4)` | 65 | 62 400 |

All three are 2-transitive of degree 65, and all three satisfy Hypothesis (A). Degree alone,
and therefore `HypothesisA` alone, cannot tell them apart. What separates them is the group
order.

Here the coverage is uneven, and we state the residual gap.

- For `Sz`, the order `|Sz(q)| = (q²+1)q²(q−1)` is a stated theorem, carried through
  `sz_data` (`Sz.lean:86`). The Suzuki family is fully pinned down.
- For `PSU₃`, we state `|Ω| = q³+1` and `|U| = q³(q²−1)/gcd(q+1,3)`. The group order follows
  by orbit-stabiliser, but it is not a named theorem.
- For `PSL₂`, we state `|Q| = q`, `|D| = q−1` and `|Ω| = q+1`. Again the order follows, but
  it is not named.

Adding the two missing order statements would close this. They are corollaries of facts
already proved, and not new mathematics.

## 5. The reading list

A reader who wants to believe the main claims, and who is willing to trust the Lean kernel
for everything else, must read the following statements, and no proofs.

| what | where | size |
|---|---|---|
| the definitions: `IsStronglyEmbedded`, `HypothesisA`, the three groups | `comparator/Defs.lean` | 248 lines |
| the four statements | `comparator/Challenge.lean` | 56 lines |

That is 304 lines, whose import closure is Mathlib and nothing else. No file of this
repository appears on the list, which is the point of stating the challenge over Mathlib. Of
the 248 lines in `Defs.lean`, roughly 60 are proof terms discharging subgroup-closure and
determinant obligations inside definitions, and these carry no meaning. The meaningful
reading is nearer 190 lines.

The remaining 2500 lines or so of new material (2440 under `Converse/`, together with 130 in
`Classification.lean`) are proof. They are the kernel's problem, and not the reader's.

## 6. Claims not supported by the argument above

For completeness, we list the claims that this document does not support.

- That Bender's theorem itself holds. We use it in §3 as external knowledge, and it is not
  formalised anywhere in this repository.
- That `HypothesisA` is equivalent to having a strongly embedded subgroup. We prove only
  `HypothesisA → IsStronglyEmbedded`. The reverse is the hard direction of Bender's paper.
- That the three families are pairwise non-isomorphic, or that the definitions pick out the
  intended member of the list. See §4.
- That an arbitrary group satisfying the conclusion of the classification has a strongly
  embedded subgroup. We prove this for the three families themselves, which is what the
  equivalence needs; the general statement is probably true, since for `G = L × C` with `C`
  odd one may take `H × C`, but we do not prove it.
- Anything at all about `BenderSuzuki.suzuki` as a named declaration. The challenge no longer
  mentions it. What these files certify is that this repository proves the four statements of
  §2. The classification's conclusion is proved in `Converse/`, but it lies outside the
  audited surface. An earlier version did anchor to
  `BenderSuzuki.suzuki` directly, at the cost of 37 opaque imported definitions, and it is
  preserved in the git history.

---

# Part II. Relation to the sources

## 7. What is formalised, and from where

The pre-existing theorem of the repository is `BenderSuzuki.suzuki`
(`BenderSuzuki/Suzuki.lean:446`). It is Peterfalvi, *Character Theory for the Odd Order
Theorem*, Part II, Theorem A: the Bender-Suzuki classification in its Zassenhaus form, a
classification of the doubly transitive groups of even degree whose point stabiliser splits
as a normal even-order subgroup by an odd-order complement. Mathematically this is Suzuki's
1962 determination of that class, with Bender's later simplification. Its classical inputs
are themselves formalised, not assumed, in `BenderSuzuki/External/`: Huppert *Endliche
Gruppen I* II.10.12 for `PSU₃`, Huppert-Blackburn XI.3.1, and XI.3.3 for the Suzuki groups.
The `PSL₂` case rests on Mathlib.

We add three things, none of which is a transcription of a numbered statement in any source.

1. Witnesses. Each of the three families in the conclusion is shown to satisfy the
   hypothesis (`BenderSuzuki/Converse/PSL2.lean:641`, `Sz.lean:501`, `PSU3.lean:622`).
2. The point stabiliser under Hypothesis (A) shown to be strongly embedded, in the sense
   of `BenderSuzuki/FinalTheorem.lean:15`
   (`BenderSuzuki/Converse/StronglyEmbedded.lean:90`).
3. The two directions packaged as an equivalence
   (`BenderSuzuki/Classification.lean:122`).

## 8. Where the formalisation follows the sources closely

We transcribe Hypothesis (A) field for field. The structure `HypothesisA1`
(`BenderSuzuki/PFchapter1section1/Basic.lean:146`) has twelve fields, in the order and shape
of Peterfalvi's Part II hypothesis: double transitivity, `H` a point stabiliser, `t` an
involution outside `H`, `D = H ∩ Hᵗ`, then `H = Q ⋊ D` expressed as five separate conditions
(`Q ≤ H`, `D ≤ H`, `Q ⊴ H`, `Disjoint Q D`, `Q ⊔ D = H`), then `|Q|` even, and `|D|` odd.
The last two fields are `A2`, faithfulness, and `A3`, 2-rank at least two.

We preserve Peterfalvi's conjugation convention, defining `rightConjugate H g = g⁻¹ H g`
(`Basic.lean:35`), following the exponent convention `H^g` of the text rather than Mathlib's
`g H g⁻¹`. The docstring records the discrepancy. The convention appears in the statement of
the theorem, at `HypothesisA1.D_eq`.

The conclusion names the standard permutation representations, with explicit equivariance. The
definition `suzukiConclusion` (`BenderSuzuki/PFchapter1section3/Basic.lean:95`) asserts more
than an abstract isomorphism `L ≅ PSL₂(q)`. Each of the three action models carries a group
isomorphism `eL`, a permutation representation `ρ` pinned to the linear action, and a bijection
`eΩ` intertwining them. The three sets are the textbook ones: the projective line, the Tits
ovoid `{p∞} ∪ {p(x,y)}` in `PG(3,q)` in Huppert-Blackburn's coordinates, and the isotropic
points of a Hermitian form with antidiagonal Gram matrix, as in Huppert II.10.12.

The Suzuki group is Huppert's generator presentation rather than an abstract characterisation:
the generators `SuzukiRootGL`, `SuzukiTorusGL`, and `SuzukiWeylGL`, with the Tits endomorphism
`π` whose square is the Frobenius endomorphism.

## 9. Where the formalisation departs from the sources

### 9.1 Strong embedding is not the form that is formalised

The Bender-Suzuki theorem is often quoted in the form *"if `G` has a strongly embedded
subgroup then ..."*. That is not what `BenderSuzuki.suzuki` assumes. Hypothesis (A) assumes
the full Zassenhaus configuration, which is strictly stronger than strong embedding.
Recovering the configuration from a strongly embedded subgroup alone is the hard content of
Bender's 1971 paper, and we do not formalise it. What we prove is the one-way implication
`HypothesisA → IsStronglyEmbedded H`.

The repository did already define strong embedding, in `FinalTheorem.lean:15` and again as
an internal variant in `SE/Basic.lean:32`, and `bender_suzuki` is stated with the first of
these. What was missing was any route from Hypothesis (A) to it, which is what the converse
lane supplies.

### 9.2 The converse has no source statement

Peterfalvi states Theorem A in one direction only. That the three families do satisfy
Hypothesis (A) is classical and universally assumed, but it is not a numbered result to
transcribe: we assemble it from the classical facts in `External/`. Likewise
`hypothesisA_lift` (`Lift.lean:229`), the passage from a normal subgroup of odd index to the
whole group, is standard but is not a lemma anywhere in the sources with a number attached.
We prove it from scratch.

### 9.3 A convention that deliberately does not follow Peterfalvi

`IsStronglyEmbedded` (`BenderSuzuki/FinalTheorem.lean:15`) uses Mathlib's conjugation
`g M g⁻¹`, written `M.map (MulAut.conj g).toMonoidHom`, and not the repository's
`rightConjugate`. Our justification is that this is a general-purpose definition rather than
a transcription of a numbered statement, so the argument from faithfulness to the source
does not apply, and being readable against Mathlib is worth more. The two are
interchangeable here, because `g` ranges over all of `G ∖ M` and `g ∉ M ↔ g⁻¹ ∉ M`.

### 9.4 Proof strategies that depart from the sources

In the Suzuki case, Huppert-Blackburn establish `Q ∩ D = 1` and `QD = H` by computing how
root elements act on the ovoid. We instead derive `|Q| = q²` from the root-closure
description and `|D| = q − 1` from orbit-stabiliser together with double transitivity. Then
`Q ∩ D = 1` follows from coprimality of `q²` and `q − 1`, and `Q ⊔ D = H` from a cardinality
count. The ovoid computation is avoided entirely. The mathematics is the same, but the route
is not the source's.

In the lifting argument, we obtain normality of `Q` in the larger stabiliser by showing that
`Q` absorbs every 2-element of `H ∩ L`, via the quotient by `Q`, whose order `|D₀|` is odd.
The usual route invokes Sylow uniqueness.

### 9.5 Shape departures forced by formalisation

- `Ω` is an independent type with a `MulAction`, and not a coset space.
- The unitary branch of the conclusion quantifies existentially over the field `E` and the form
  `J`, rather than naming `GF(q²)`. The existential form is weaker than the textbook statement,
  and it materially complicated the converse: a witness for one particular form does not
  suffice, so we generalised the `PSU₃` development to arbitrary `(K, J, q)` of the stated
  shape (`PSU3.lean:368`).
- The conclusion supplies data (`eL`, `ρ`, `eΩ`) where the sources say "is isomorphic to,
  acting naturally". The supplied data are a strengthening, and they are what make the converse
  provable at all.

### 9.6 A second transcription, in Mathlib vocabulary

For the certification described in Part I we transcribe Hypothesis (A) and the three groups a
second time, in `comparator/Defs.lean`, using Mathlib primitives alone. The copy is field for
field, and the solution must discharge the repository's version from it, so a weakened copy
would fail rather than pass silently. The transcription forces two small departures. First,
`rightConjugate` is written directly as `H.map (MulAut.conj g⁻¹).toMonoidHom`, because the
repository's `Subgroup.conjBy` is not a Mathlib declaration. Second, the three groups are
transcribed as `PSL2Model`, `SzModel`, and `PSUModel`; each is definitionally equal to the
repository's version, and we check this by `rfl`.
