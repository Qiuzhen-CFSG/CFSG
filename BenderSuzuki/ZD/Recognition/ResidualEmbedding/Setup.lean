module

public import BenderSuzuki.ZD.Recognition.Interfaces

/-!
# Boundaries of the residual ZD argument

These definitions separate the permutation argument of Sections 5–7, the
generation theorem of Sections 12–15, and the residual analysis of Sections
16–17 in GLS, Volume 4, Chapter 2. They are explicit proof obligations,
not assertions that these source theorems have already been proved.

The two-point stabilizer is `D = M ∩ Mᵗ`. The commutator uses the odd core
of `D`, mapped into the ambient group; it does not use the two-residual.
All actions are the canonical actions on actual cosets of `M`.
-/

noncomputable section

namespace BenderSuzuki.ZD

open PFAppendixIII PFchapter1section1

variable {G : Type*} [Group G]

/-- The two-point stabilizer from source (12A), for an involution `t`
interchanging the base point and its translate. -/
@[expose] public def residualPairStabilizer (M : Subgroup G) (t : G) : Subgroup G :=
  M ⊓ rightConjugate M t

/-- The ambient copy of `[O_{2'}(D), t]` from source (12A). -/
@[expose] public def residualCommutator (M : Subgroup G) (t : G) : Subgroup G :=
  let D := residualPairStabilizer M t
  ⁅(pPrimeCore 2 D).map D.subtype, Subgroup.zpowers t⁆

/-- The group `L = ⟨z, t, [O_{2'}(D), t]⟩` of Section 12. -/
@[expose] public def residualGenerated (M : Subgroup G) (z t : G) : Subgroup G :=
  Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔ residualCommutator M t

/-- The source Theorem 4 action conclusions needed in the residual case.
Only distinguished involutions are quantified over in the odd-subgroup
clause; they are not replaced by arbitrary involutions of `G`. -/
public structure ResidualAction (Z : Set G) (M : Subgroup G) : Prop where
  two_transitive : MulAction.IsMultiplyPretransitive G (G ⧸ M) 2
  odd_normalizer : ∀ z ∈ Z, z ∈ M → ∀ W : Subgroup G,
    Odd (Nat.card W) → W ≤ M → z ∈ Subgroup.normalizer (W : Set G) →
      W ≤ Subgroup.centralizer ({z} : Set G) ∨
        ∀ beta : G ⧸ M, W ≤ MulAction.stabilizer G beta →
          beta = QuotientGroup.mk 1

/-- The generation conclusion of Theorem 12.1, to be established in the
case where `M` is not strongly embedded. Double transitivity makes all
the relevant two-point stabilizers even in that case. -/
@[expose] public def ResidualGeneration (Z : Set G) (M : Subgroup G) : Prop :=
  ∀ z ∈ Z, z ∈ M → ∀ t ∈ Z, t ∉ M → residualGenerated M z t = ⊤

end BenderSuzuki.ZD
