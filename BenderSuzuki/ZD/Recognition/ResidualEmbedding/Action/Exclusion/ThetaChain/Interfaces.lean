module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Interfaces

/-!
# Distinguished Gamma construction: the remaining geometric obligation

This is the conclusion of GLS, Volume 4, Chapter 2, Proposition 7.4, on
the actual cosets of `M`. In particular the swapping involution belongs to
the distinguished set `Z`. The base-point pair centralizer in (d)(3) is
written as `D ∩ C_G(K₁)`, using that the base stabilizer is `M`.

This definition is a proof obligation. Its construction from the minimal
counterexample requires Lemma 7.3 and the two branches of Proposition 7.4;
no theta comparison is part of the definition.
-/

noncomputable section

namespace BenderSuzuki.ZD

open PFAppendixIII PFchapter1section1

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- All clauses of Proposition 7.4, retaining distinguished membership. -/
@[expose] public def ActionGamma (d : ActionCounterexample Z M) : Prop :=
  ∃ Gamma : Set (G ⧸ M),
    Gamma ⊆ d.toTheorem4bSixA.kFixedPoints ∧
    (QuotientGroup.mk 1 : G ⧸ M) ∈ Gamma ∧
    1 < Nat.card Gamma ∧
    (∀ beta : G ⧸ M, beta ∈ Gamma ↔ d.z • beta ∈ Gamma) ∧
    (∀ beta gamma : G ⧸ M, beta ∈ Gamma → gamma ∈ Gamma → beta ≠ gamma →
      (MulAction.stabilizer G beta ⊓ MulAction.stabilizer G gamma) ⊓
        Subgroup.centralizer d.toTheorem4bSixA.invertedSet ≤ M) ∧
    (∀ beta : G ⧸ M, beta ∈ Gamma → beta ≠ QuotientGroup.mk 1 →
      ∃ t ∈ Z,
        t • (QuotientGroup.mk 1 : G ⧸ M) = beta ∧
        rightConjugateSet d.toTheorem4bSixA.invertedSet
            (rightConjugateElem t d.z) ⊆ theorem4bSection7E M d.z beta ∧
        theorem4bSection7D M beta ⊓
            Subgroup.centralizer (rightConjugateSet d.toTheorem4bSixA.invertedSet
              (rightConjugateElem t d.z)) ≤ theorem4bSection7E M d.z beta ∧
        ∃ g : G, g • (d.z • beta) = (QuotientGroup.mk 1 : G ⧸ M) ∧
          g • beta ∈ Gamma)

end BenderSuzuki.ZD
