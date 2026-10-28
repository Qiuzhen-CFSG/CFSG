module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Definitions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights

/-!
# Identifying the normal-eight catalogue with the literal normalizer rows

The checked presentation isomorphism sends each marked generator to its
specified matrix word. It therefore sends the three catalogue subgroups to
the exact subgroups `MatrixNormalizerBounds.F`, including the product of
generators in the third row. Transporting the exhaustive catalogue through
this isomorphism proves the coverage premise of the ambient-normalizer
adapter. Normality and the upper-central bound refer to the actual Sylow
subgroup throughout; no uniqueness of its normal eights is assumed.

This supplies the concrete catalogue input for the normal-eight branch of
the Sylow-overgroup analysis cited in Aschbacher–Smith A.3.12, printed
pp.47–48, and Kleidman–Wilson (1988), pp.484–510. Literal matrix-word and
presentation provenance is retained in `SylowNormalEights` and its imports.
-/

public section

open Subgroup Janko4.LocalStructure.SylowNormalEights
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The marked presentation catalogue maps to the exact matrix generating triples. -/
theorem family_map_matrixEquiv (i : Fin 3) :
    (Presentation.family i).map matrixEquiv.toMonoidHom = F i := by
  fin_cases i <;>
    simp [Presentation.family, Presentation.familyGenerator, Matrix.range_cons,
      Matrix.range_empty, MonoidHom.map_closure, Set.image_insert_eq, F] <;>
    congr 1 <;> ext x <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto

/-- Every normal elementary eight in the third center is one of the literal rows. -/
theorem literal_family_coverage : Coverage := by
  intro A hn he hc hu
  let : A.Normal := hn
  let : IsElementaryAbelian 2 A := he
  have hnormal : (A.map matrixEquiv.symm.toMonoidHom).Normal :=
    Subgroup.Normal.map hn matrixEquiv.symm.toMonoidHom matrixEquiv.symm.surjective
  have helementary : IsElementaryAbelian 2 (A.map matrixEquiv.symm.toMonoidHom) :=
    IsElementaryAbelian.map _
  have hcard : Nat.card (A.map matrixEquiv.symm.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective matrixEquiv.symm.injective, hc]
  have hupper : A.map matrixEquiv.symm.toMonoidHom ≤
      Subgroup.upperCentralSeries Presentation.Carrier 3 := by
    rw [← Subgroup.comap_upperCentralSeries matrixEquiv 3]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_comap]
    simpa using hu hx
  obtain ⟨i, hi⟩ := Presentation.Profiles.catalogueCoverage_of_card presentation_card
    _ hnormal helementary hcard hupper
  refine ⟨i, ?_⟩
  rw [← family_map_matrixEquiv i]
  exact ((Subgroup.map_symm_eq_iff_map_eq (e := matrixEquiv) (Presentation.family i)).mp hi).symm

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
