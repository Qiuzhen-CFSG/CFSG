module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCoordinates
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.LinearThree.Blocks

/-!
# The nonbinary local-block assertions for the L₃ amalgam

The concrete point and line factors are natural L₂(2ⁿ)-blocks for n > 1,
are perfect, and equal their solvable residuals. The imported `Blocks`
constructors discharge every C.1.7 short-group clause and C.1.12 module
identification from the affine structure. This entry point additionally
identifies their quotient and core coordinates on the original matrices.
For the point radical the coordinate swap `(x,y) ↦ (y,x)` turns its dual
action into the natural action of the same lower-right SL₂ block.

All residuals are the terminal derived subgroup. Their ambient images use
the actual inclusions into PSL₃, while block shortness is intrinsic to each
local factor, as stipulated by C.1.7 when no overgroup is specified.

Source: Aschbacher–Smith, C.1.7 and C.1.12, printed pp.123–124;
F.1.12(I)(1) and the equality Lᵢ = Lᵢ∞ on printed p.264 (PDF pp.273–275).
The Sylow containment and outer-extension conclusions belong to the parent
source assembly.
-/

public section

open Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree

open Matrix.PSL3.LinearThree ChapterC

section Coordinates
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The point block's actor is the original lower-right SL₂ block. -/
theorem pointLocalBlockModuleModel_quotient_matrix (g : pointLocalSL F) :
    ((pointLocalBlockModuleModel F).quotientIso
      (QuotientGroup.mk' (pCore 2 (pointLocal F)) (pointLocalProjectEquiv F g))).val =
      !![g.val.val 1 1, g.val.val 1 2; g.val.val 2 1, g.val.val 2 2] := by
  rw [pointLocalBlockModuleModel_quotientIso]
  exact pointLocalCoreQuotientEquiv_project_val F g

/-- The line block's actor is the original upper-left SL₂ block. -/
theorem lineLocalBlockModuleModel_quotient_matrix (g : lineLocalSL F) :
    ((lineLocalBlockModuleModel F).quotientIso
      (QuotientGroup.mk' (pCore 2 (lineLocal F)) (lineLocalProjectEquiv F g))).val =
      !![g.val.val 0 0, g.val.val 0 1; g.val.val 1 0, g.val.val 1 1] := by
  rw [lineLocalBlockModuleModel_quotientIso]
  exact lineLocalCoreQuotientEquiv_project_val F g

/-- The natural point-core coordinates project the original root row with its coordinates swapped.
The conjugation identity is `SL2Affine.coreEquiv_action` for this same equivalence. -/
theorem pointLocal_root_coordinates (g : pointLocalSL F) (hg : g ∈ pointRadicalSL F) :
    (SL2Affine.coreEquiv (pointLocalEquivAffine F)
      (Multiplicative.ofAdd ![g.val.val 0 2, g.val.val 0 1]) : pointLocal F) =
      pointLocalProjectEquiv F g := by
  apply (pointLocalEquivAffine F).injective
  rw [SL2Affine.coreEquiv_apply, pointLocalEquivAffine_project]
  apply SemidirectProduct.ext
  · exact Multiplicative.toAdd.injective
      (pointLocalAffineEquiv_left_of_mem_radical F g hg).symm
  · exact (show (pointLocalAffineEquiv F g).right = 1 from hg).symm

/-- The natural line-core coordinates project the original root column. -/
theorem lineLocal_root_coordinates (g : lineLocalSL F) (hg : g ∈ lineRadicalSL F) :
    (SL2Affine.coreEquiv (lineLocalEquivAffine F)
      (Multiplicative.ofAdd ![g.val.val 0 2, g.val.val 1 2]) : lineLocal F) =
      lineLocalProjectEquiv F g := by
  apply (lineLocalEquivAffine F).injective
  rw [SL2Affine.coreEquiv_apply, lineLocalEquivAffine_project]
  apply SemidirectProduct.ext
  · exact Multiplicative.toAdd.injective (lineLocalAffineEquiv_left F g).symm
  · exact (show (lineLocalAffineEquiv F g).right = 1 from hg).symm

end Coordinates

variable (F : Type) [Field F] [Finite F]

omit [Field F] [Finite F] in
private theorem card_ge_four {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    4 ≤ Nat.card F := by
  rw [hF]
  exact (show 2 ^ 2 ≤ 2 ^ n from Nat.pow_le_pow_right (by decide) hn)

/-- The nonbinary point-local block and residual clauses, with no structural premises left. -/
theorem pointLocal_block_structure {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    IsL2EvenBlock (pointLocal F) n ∧ Group.IsPerfect (pointLocal F) ∧
      Subgroup.solvableResidual (pointLocal F) = ⊤ ∧
      (Subgroup.solvableResidual (pointLocal F)).map (pointLocal F).subtype =
        pointLocal F :=
  ⟨pointLocal_isL2EvenBlock F hF hn,
    pointLocal_isPerfect F (card_ge_four F hF hn),
    pointLocal_solvableResidual_eq_top F (card_ge_four F hF hn),
    pointLocal_map_solvableResidual F (card_ge_four F hF hn)⟩

/-- The nonbinary line-local block and residual clauses, with no structural premises left. -/
theorem lineLocal_block_structure {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    IsL2EvenBlock (lineLocal F) n ∧ Group.IsPerfect (lineLocal F) ∧
      Subgroup.solvableResidual (lineLocal F) = ⊤ ∧
      (Subgroup.solvableResidual (lineLocal F)).map (lineLocal F).subtype =
        lineLocal F :=
  ⟨lineLocal_isL2EvenBlock F hF hn,
    lineLocal_isPerfect F (card_ge_four F hF hn),
    lineLocal_solvableResidual_eq_top F (card_ge_four F hF hn),
    lineLocal_map_solvableResidual F (card_ge_four F hF hn)⟩

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree
