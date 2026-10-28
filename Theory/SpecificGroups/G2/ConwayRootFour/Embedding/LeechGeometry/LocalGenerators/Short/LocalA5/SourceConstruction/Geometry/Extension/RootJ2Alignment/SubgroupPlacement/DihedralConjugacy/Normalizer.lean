module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.DihedralConjugacy.Normalizer.Golden

/-!
# The marked five-normalizer in SL₃(4)

The normalizer has order thirty. The calculation over `GoldenFour` reduces
normalizing matrices to their lower two-by-two block. Here the same field
comparison used by `Placement` identifies its rotation with the literal
`rootJ2LongDihedralModel (.r 1)`. Transport of normalizers then excludes a
factor of four in its order, the input to the two-stage Sylow conjugacy argument.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 49.5, pp.283–284,
local placement using 48.3, 49.2 and 48.8. This is independent finite matrix
group mathematics; no ambient Leech placement is an input.
-/

open Matrix Atlas.Conway Atlas.Algebra
open scoped MatrixGroups
set_option backward.isDefEq.respectTransparency false
public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction

private def fiveSLFieldEquiv : SL(3,GoldenFour) ≃* SL(3,F) where
  toFun := Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom
  invFun := Matrix.SpecialLinearGroup.map fieldEquiv.symm.toRingHom
  left_inv a := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change fieldEquiv.symm (fieldEquiv (a.val i j)) = a.val i j
    exact fieldEquiv.symm_apply_apply _
  right_inv a := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change fieldEquiv (fieldEquiv.symm (a.val i j)) = a.val i j
    exact fieldEquiv.apply_symm_apply _
  map_mul' := map_mul _

private theorem fiveSLFieldEquiv_rotation :
    fiveSLFieldEquiv FiveNormalizer.bigR = rootJ2LongDihedralModel (.r 1) := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fiveSLFieldEquiv, FiveNormalizer.bigR, FiveNormalizer.diag, FiveNormalizer.rot,
      rootJ2LongDihedralModel, block, blockMatrix, slEquiv, dihedralModel, dihedralValue,
      rotation, Matrix.SpecialLinearGroup.map, show (1 : ZMod 5).val = 1 from rfl]

/-- The exact normalizer order for the marked block rotation, with the original
field comparison and coordinates of `Placement`. -/
theorem rootJ2LongFiveNormalizer_card :
    Nat.card (Subgroup.normalizer
      (Subgroup.zpowers (rootJ2LongDihedralModel (.r 1)) : Set SL(3,F))) = 30 := by
  have he : FiveNormalizer.N.map fiveSLFieldEquiv.toMonoidHom =
      Subgroup.normalizer
        (Subgroup.zpowers (rootJ2LongDihedralModel (.r 1)) : Set SL(3,F)) := by
    rw [FiveNormalizer.N, Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers]
    change Subgroup.normalizer
      (Subgroup.zpowers (fiveSLFieldEquiv FiveNormalizer.bigR) : Set SL(3,F)) = _
    rw [fiveSLFieldEquiv_rotation]
  rw [← he, ← Nat.card_congr
    (FiveNormalizer.N.equivMapOfInjective fiveSLFieldEquiv.toMonoidHom
      fiveSLFieldEquiv.injective).toEquiv, FiveNormalizer.normalizer_card]

/-- The numerical input required by marked dihedral subgroup conjugacy. -/
theorem rootJ2LongFiveNormalizer_four_not_dvd : ¬ 4 ∣ Nat.card (Subgroup.normalizer
    (Subgroup.zpowers (rootJ2LongDihedralModel (DihedralGroup.r 1)) : Set SL(3,F))) := by
  rw [rootJ2LongFiveNormalizer_card]
  norm_num

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
