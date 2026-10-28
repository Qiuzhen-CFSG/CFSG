module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry

/-!
# Application of intrinsic cubic geometry to simultaneous subgroup placement

The three explicit Leech model premises discharge the cubic-orbit and
centralizer premises of the existing placement theorem. The independent
SL₃(4) dihedral conjugacy premise is retained. This application uses the
literal root J₂ embedding, long frame, cubic and dihedral maps.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 49.5, pp.283–284.
-/

open Matrix Atlas.Conway
open scoped MatrixGroups
public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open OctonionLocals

/-- Conditional consumer application; the three intrinsic model inputs and
matrix-dihedral conjugacy are not asserted by this theorem. -/
theorem exists_rootJ2SubgroupMarks_of_fixedFree_local_data (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (hfusion : FixedFreeCubicFusion) (hroot : CubicFixedFree (rootJ2Cubic e))
    (hbound : Nat.card ↥(centralizerI ⊓ Subgroup.centralizer
      (Subgroup.zpowers (rootJ2Cubic e) : Set LeechCentralQuotient)) ≤ Nat.card SL(3,F))
    (hD : ∀ j : DihedralGroup 5 →* SL(3,F), Function.Injective j →
      ∃ A : SL(3,F), j.range.map (MulAut.conj A).toMonoidHom = rootJ2LongDihedralModel.range) :
    ∃ g ∈ centralizerI, RootJ2SubgroupMarks L (conjugatedRootJ2 e g) := by
  obtain ⟨hX, hC⟩ := rootJ2_cubicGeometry_of_fixedFree_local_data L e hfusion hroot hbound
  exact exists_rootJ2SubgroupMarks_of_cubic_local_data L e hX hC hD

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
