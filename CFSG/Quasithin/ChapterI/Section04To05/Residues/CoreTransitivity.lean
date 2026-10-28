module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.KernelSeparation
public import Theory.GroupAction.ThreePointTransitivity

/-!
# The actual point core exchanges the two other points of each incident line

The original point core fixes the base point and preserves every incident
line. Its nontrivial line action follows from the proved core-join index.
The elementary three-point argument makes this action transitive on the
other two points, and conjugation transports it to every line through the
base point. This is I.5.7(2), used by I.5.9's point-neighbor orbit count.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem point_core_baseLine_transitive {y z : S.Point}
    (hy : S.Inc y S.baseLine) (hz : S.Inc z S.baseLine)
    (hxy : S.basePoint ≠ y) (hxz : S.basePoint ≠ z) :
    ∃ g ∈ S.Q 0, g • y = z := by
  apply MulAction.transitive_other_two_of_nontrivial
    {y : S.Point | S.Inc y S.baseLine} (S.line_points_card S.baseLine) (S.Q 0)
    (show S.Inc S.basePoint S.baseLine from ⟨1, rfl, rfl⟩)
    (fun _ hg => S.point_core_fixes_basePoint hg) ?_ ?_ hy hz hxy hxz
  · intro g hg w
    change S.Inc w S.baseLine ↔ S.Inc (g • w) S.baseLine
    have hf : g • S.baseLine = S.baseLine :=
      S.core_fixes_incident_coset 0 1 (by decide) hg ⟨1, rfl, rfl⟩
    constructor
    · intro h
      simpa only [hf] using h.smul S g
    · intro h
      have hf' : g⁻¹ • S.baseLine = S.baseLine :=
        S.core_fixes_incident_coset 0 1 (by decide) ((S.Q 0).inv_mem hg) ⟨1, rfl, rfl⟩
      simpa only [hf', inv_smul_smul] using h.smul S g⁻¹
  · intro h
    apply S.point_core_not_le_lineCore
    have hh : S.Q 0 = S.Q 0 ⊓ S.Q 1 := by
      rw [← S.point_core_line_kernel, inf_eq_left.mpr h]
    exact hh.le.trans inf_le_right

theorem point_core_incidentLine_transitive {l : S.Line} (hl : S.Inc S.basePoint l)
    {y z : S.Point} (hy : S.Inc y l) (hz : S.Inc z l)
    (hxy : S.basePoint ≠ y) (hxz : S.basePoint ≠ z) :
    ∃ g ∈ S.Q 0, g • y = z := by
  obtain ⟨a, ha, hal⟩ := (CosetGeometry.incident_base_iff S.family 0 ⟨1, l⟩).mp hl
  have hline : a • S.baseLine = l := by
    change ((a * 1 : G) : G ⧸ S.family 1) = l
    simpa only [mul_one] using hal
  have hp : a • S.basePoint = S.basePoint := by
    apply MulAction.mem_stabilizer_iff.mp
    rwa [S.stabilizer_basePoint]
  have hy' : S.Inc (a⁻¹ • y) S.baseLine := by
    simpa only [← hline, inv_smul_smul] using hy.smul S a⁻¹
  have hz' : S.Inc (a⁻¹ • z) S.baseLine := by
    simpa only [← hline, inv_smul_smul] using hz.smul S a⁻¹
  obtain ⟨q, hq, he⟩ := S.point_core_baseLine_transitive hy' hz'
    (fun h => hxy (by simpa only [hp, smul_inv_smul] using congrArg (a • ·) h))
    (fun h => hxz (by simpa only [hp, smul_inv_smul] using congrArg (a • ·) h))
  refine ⟨a * q * a⁻¹, (mem_normalizer_iff.mp (S.family_le_normalizer_Q 0 ha) q).mp hq, ?_⟩
  simpa only [mul_smul, smul_inv_smul] using congrArg (a • ·) he

end Quasithin.I5.DSystem
