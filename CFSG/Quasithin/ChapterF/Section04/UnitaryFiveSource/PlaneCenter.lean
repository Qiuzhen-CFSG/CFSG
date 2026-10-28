module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.PlaneCenter
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Source

/-!
# The plane-core center in the actual PSU₅(4) model

Restrict the original residual inclusion and use the faithful projective
unipotent parametrization. The resulting equivalence identifies the canonical
plane two-core with the native parameter group, including its square-one locus,
center, commutator and Frattini subgroup. Only the unipotent restriction of
projectivization is injective; the scalar kernel of the full SU₅ map is retained.

Source: Aschbacher--Smith F.4.29(6) and F.4.35, printed pp.289--292.
The Chapter6 companion applies this to the original prepared plane residual.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive
variable (U : Model 4)

/-- The canonical core is parametrized through the actual residual inclusion
and the injective unipotent restriction of projectivization. -/
def rightLocalImageCoreParameters :
    pCore 2 U.rightLocalImage ≃* PlaneCore.Parameters U.form :=
  (LocalCoreTransport.coreEquiv 2 U.rightLocalImageEquiv.symm).trans
    U.rightLocalTwoCoreEquiv

/-- The plane core is special, with an elementary center of order `4^4`;
its involutions are exactly the nonidentity elements of that center. -/
theorem rightLocalImage_core_center_structure :
    Nat.card (center (pCore 2 U.rightLocalImage)) = 4 ^ 4 ∧
      IsElementaryAbelian 2 (center (pCore 2 U.rightLocalImage)) ∧
      center (pCore 2 U.rightLocalImage) = commutator (pCore 2 U.rightLocalImage) ∧
      center (pCore 2 U.rightLocalImage) = frattini (pCore 2 U.rightLocalImage) ∧
      ∀ x : pCore 2 U.rightLocalImage,
        x ^ 2 = 1 ↔ x ∈ center (pCore 2 U.rightLocalImage) := by
  obtain ⟨c,hc⟩ := U.exists_lineTraceOne
  exact PlaneCore.Parameters.structure_of_equiv U.form U.local_field_card U.conjugation
    c hc U.rightLocalImageCoreParameters

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
