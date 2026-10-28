module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Inputs
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.Reduction

/-!
# Assembly of the root J₂ marking branches

The subgroup-placement premise selects a conjugator in the literal tetrahedral
centralizer. The independent inverter-coset premise identifies the resulting
reflection action up to the long cubic. Correcting the conjugator by that
cubic element preserves both subgroup marks and removes the action discrepancy.
This supplies precisely the `RootJ2Marks` consumed by `Geometry.Extension`.

The source placement and inverter-coset premises remain explicit; this module
does not yet assert `exists_rootJ2Marks`. Their discharge remains with this
assembly, independently of the supplied permutation-to-icosian equivalence.
Source: Aschbacher, *Sporadic Groups* (1994), proof of Lemma 49.5, pp.283–284,
with the root J₂ choice from 49.1 (p.280) and placement from 48.8 (p.273).
-/

open Matrix Atlas.Conway
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open OctonionLocals

/-- Conditional assembly of the independent subgroup-placement and reflection branches.
Neither remaining source premise is asserted by this theorem. -/
theorem exists_rootJ2Marks_of_subgroup_placement_and_inverter_coset (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (hplace : ∃ g ∈ centralizerI, RootJ2SubgroupMarks L (conjugatedRootJ2 e g))
    (hcoset : ∀ g ∈ centralizerI,
      RootJ2SubgroupMarks L (conjugatedRootJ2 e g) →
        ∃ t : Fˣ, ∀ v : Fin 6 → F,
          quotientModTwoRepresentation
              (conjugatedRootJ2 e g Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.inverter)
              (L.coordinates v) =
            quotientModTwoRepresentation (longCubic L t) (L.coordinates (action graph v))) :
    ∃ g ∈ centralizerI, Nonempty (RootJ2Marks L (conjugatedRootJ2 e g)) := by
  obtain ⟨g, hg, M⟩ := hplace
  obtain ⟨t, ht⟩ := hcoset g hg M
  refine ⟨longCubic L t * g, centralizerI.mul_mem (L.long_mem _) hg, ?_⟩
  exact ⟨rootJ2MarksOfCubicCoset L e g M t ht⟩

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
