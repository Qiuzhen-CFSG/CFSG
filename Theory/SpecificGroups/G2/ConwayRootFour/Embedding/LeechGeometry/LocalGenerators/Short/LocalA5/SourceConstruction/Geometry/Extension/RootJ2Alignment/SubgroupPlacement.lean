module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.Transport

/-!
# Simultaneous root J₂ subgroup placement from cubic local geometry

First align the root J₂ cubic with the long cubic. Its marked dihedral group
then centralizes that cubic. The ambient centralizer bound places the dihedral
group in the faithful long SL₃(4); pull it back and conjugate it to the precise
block-dihedral model there. This second conjugation fixes the long cubic,
so the product of the two conjugators supplies both subgroup marks.

The ambient cubic orbit and centralizer bound, and the matrix conjugacy theorem,
remain explicit premises. This is a conditional assembly for
`exists_rootJ2SubgroupMarks`, whose final discharge belongs to this module.
It does not assert that source theorem or the independent inverter action.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 49.5, pp.283–284,
using the root J₂ from 49.1 and local placement from 48.3, 49.2 and 48.8.
-/

open Matrix Atlas.Conway
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open OctonionLocals PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight

/-- Assemble cubic placement, its ambient centralizer, and finite matrix conjugacy.
All three geometric inputs remain explicit until their separate proofs are supplied. -/
theorem exists_rootJ2SubgroupMarks_of_cubic_local_data (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (hX : ∃ g ∈ centralizerI, (longCubic L).range ≤
      Sporadic.LeechRelated.J2.RecognitionGeometry.X.map (conjugatedRootJ2 e g))
    (hC : centralizerI ⊓
      Subgroup.centralizer ((longCubic L).range : Set LeechCentralQuotient) ≤ L.long.range)
    (hD : ∀ j : DihedralGroup 5 →* SL(3,F), Function.Injective j →
      ∃ A : SL(3,F), j.range.map (MulAut.conj A).toMonoidHom = rootJ2LongDihedralModel.range) :
    ∃ g ∈ centralizerI, RootJ2SubgroupMarks L (conjugatedRootJ2 e g) := by
  obtain ⟨g, hg, hXg⟩ := hX
  have hB : Sporadic.LeechRelated.J2.RecognitionGeometry.B.map
      (conjugatedRootJ2 e g) ≤ L.long.range :=
    (rootJ2_dihedral_le_cubicCentralizer L e hg hXg).trans hC
  let j := rootJ2DihedralPullback L (conjugatedRootJ2 e g) hB
  obtain ⟨A, hA⟩ := hD j
    (rootJ2DihedralPullback_injective L _ (conjugatedRootJ2_injective e g) hB)
  refine ⟨L.long A * g, centralizerI.mul_mem (L.long_mem A) hg, ?_⟩
  refine ⟨rootJ2_cubic_mark_long_conjugate L e g hXg A, ?_⟩
  rintro c ⟨d, rfl⟩
  have hd : rootJ2LongDihedralModel d ∈ j.range.map (MulAut.conj A).toMonoidHom := by
    rw [hA]
    exact ⟨d, rfl⟩
  obtain ⟨a, ⟨b, rfl⟩, hab⟩ := hd
  refine ⟨Sporadic.LeechRelated.J2.RecognitionGeometry.dihedralHom b, ?_, ?_⟩
  · rw [← Sporadic.LeechRelated.J2.RecognitionGeometry.dihedralHom_range]
    exact ⟨b, rfl⟩
  · rw [conjugatedRootJ2_mul]
    have hh := congrArg L.long hab
    change L.long (A * j b * A⁻¹) = L.long (rootJ2LongDihedralModel d) at hh
    simpa only [map_mul, map_inv, j, rootJ2DihedralPullback_spec,
      rootJ2LongDihedralModel_apply] using hh

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
