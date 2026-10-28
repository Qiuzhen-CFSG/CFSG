module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.DerivedEightConjugacy.LocalCriterion
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coordinates

/-!
# Three local centralizers in the fixed Rudvalis coordinates

The remaining local calculation separates into a conjugacy sieve and the
derived-subgroup calculation for three representatives. All elements and
centralizers here belong to the original model; the subgroup intersection is
the literal one used by `LocalCentralizerDerivedNormal`.

The two certificate propositions are independent obligations, not asserted
facts. `LocalCentralizers` proves their application to the requested criterion.
The representative indices were discovered by the adjacent `source/Explore.g`;
GAP output is not proof evidence. The local criterion is a sufficient route
motivated by GLS3 Table 5.3r and pp.291–292, and Aschbacher–Smith I.2.2(7),
pp.412–413; it is not itself a quoted source theorem.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry.LocalCentralizers
open Subgroup SylowOvergroups.RadicalCoverage.LocalCover

/-- Centralizer inside the unchanged fixed local subgroup, viewed in `Model`. -/
@[expose] public def centralizerAt (i : Model) : Subgroup Model :=
  localP ⊓ centralizer ({i} : Set Model)

/-- Three indices in `CatalogueCertificate.normalForm`, in ascending order. -/
@[expose] public def representativeIndex : Fin 3 → Fin 16384 := ![13, 37, 158]

/-- The representatives are actual words, not abstract conjugacy-class tags. -/
@[expose] public def representative (r : Fin 3) : Model :=
  CatalogueCertificate.normalForm (representativeIndex r)

public theorem representative_mem (r : Fin 3) : representative r ∈ localP :=
  CatalogueCertificate.normalForm_mem _

/-- The finite local sieve must produce a conjugator in `localP` itself. -/
@[expose] public def RepresentativeCover : Prop :=
  ∀ i ∈ localP, i ^ 2 = 1 →
    Nat.card (centralizerAt i) = 256 →
    (∀ x ∈ centralizerAt i, x ^ 2 = 1 →
      x ∈ centralizer (centralizerAt i : Set Model)) →
    ∃ (r : Fin 3) (g : Model), g ∈ localP ∧
      i = MulAut.conj g (representative r)

/-- The representative calculation may use the order already supplied by
the actual consumer. It need not independently compute centralizer orders. -/
@[expose] public def RepresentativeDerived : Prop :=
  ∀ r : Fin 3, Nat.card (centralizerAt (representative r)) = 256 →
    ⁅centralizerAt (representative r), centralizerAt (representative r)⁆ = elementary 2

end Rudvalis.CoveringIncidence.NormalizerGeometry.LocalCentralizers
