module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.CoreLineAction

/-!
# Point-pair adjustments in the original geometry

The point core fixes all lines at its point and exchanges the other two
points of each line. Thus an element fixing a point and one incident line
can be adjusted to fix a chosen second point without changing its action
on any incident line. Likewise, a line kernel fixes that line pointwise
and exchanges the other points on every different incident line.

Translation gives these statements at arbitrary original points, keeping
the ambient elements and actions. These are the two local adjustments in
the I.5.9 four-step geodesic argument, printed pp.421–422.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem base_pair_fixer_same_lines {l : S.Line} (hl : S.Inc S.basePoint l)
    {y : S.Point} (hy : S.Inc y l) (hxy : S.basePoint ≠ y)
    {a : G} (ha : a ∈ S.family 0) (hal : a • l = l) :
    ∃ g : G, g • S.basePoint = S.basePoint ∧ g • y = y ∧
      ∀ m : S.Line, S.Inc S.basePoint m → g • m = a • m := by
  have hax : a • S.basePoint = S.basePoint := by
    apply MulAction.mem_stabilizer_iff.mp
    rwa [S.stabilizer_basePoint]
  have hay : S.Inc (a • y) l := by simpa only [hal] using hy.smul S a
  have hne : S.basePoint ≠ a • y := fun h => hxy ((MulAction.injective a) (hax.trans h))
  obtain ⟨q, hq, he⟩ := S.point_core_incidentLine_transitive hl hay hy hne hxy
  refine ⟨q * a, ?_, ?_, ?_⟩
  · rw [mul_smul, hax, S.point_core_fixes_basePoint hq]
  · simpa only [mul_smul] using he
  · intro m hm
    rw [mul_smul]
    apply S.core_fixes_incident_coset 0 1 (by decide) hq
    change S.Inc S.basePoint (a • m)
    simpa only [hax] using hm.smul S a

/-- A literal element fixing two points, with unchanged action on their incident lines. -/
theorem exists_point_pair_fixer_same_lines {x y : S.Point} {l : S.Line}
    (hxl : S.Inc x l) (hyl : S.Inc y l) (hxy : x ≠ y)
    {a : G} (hax : a • x = x) (hal : a • l = l) :
    ∃ g : G, g • x = x ∧ g • y = y ∧
      ∀ m : S.Line, S.Inc x m → g • m = a • m := by
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq G S.basePoint x
  let a' := b⁻¹ * a * b
  have ha' : a' ∈ S.family 0 := by
    rw [← S.stabilizer_basePoint]
    change (b⁻¹ * a * b) • S.basePoint = S.basePoint
    rw [mul_smul, mul_smul, hb, hax, ← hb, inv_smul_smul]
  have hxl' : S.Inc S.basePoint (b⁻¹ • l) := by
    simpa only [← hb, inv_smul_smul] using hxl.smul S b⁻¹
  have hyl' := hyl.smul S b⁻¹
  have hxy' : S.basePoint ≠ b⁻¹ • y := fun h => hxy (by
    simpa only [hb, smul_inv_smul] using congrArg (b • ·) h)
  have hal' : a' • (b⁻¹ • l) = b⁻¹ • l := by
    simp only [a', mul_smul, smul_inv_smul, hal]
  obtain ⟨c, hcx, hcy, hcl⟩ := S.base_pair_fixer_same_lines hxl' hyl' hxy' ha' hal'
  refine ⟨b * c * b⁻¹, ?_, ?_, ?_⟩
  · rw [← hb, mul_smul, mul_smul, inv_smul_smul, hcx]
  · simpa only [mul_smul, smul_inv_smul] using congrArg (b • ·) hcy
  · intro m hm
    have hm' : S.Inc S.basePoint (b⁻¹ • m) := by
      simpa only [← hb, inv_smul_smul] using hm.smul S b⁻¹
    simpa only [a', mul_smul, smul_inv_smul, inv_smul_smul] using
      congrArg (b • ·) (hcl (b⁻¹ • m) hm')

/-- The line kernel at x fixes one line pointwise and exchanges points of a different line. -/
theorem exists_line_pointwise_fixer_transporter {x : S.Point} {l m : S.Line}
    (hl : S.Inc x l) (hm : S.Inc x m) (hne : l ≠ m)
    {y z : S.Point} (hy : S.Inc y m) (hz : S.Inc z m) (hxy : x ≠ y) (hxz : x ≠ z) :
    ∃ g : G, (∀ u : S.Point, S.Inc u l → g • u = u) ∧
      (∀ k : S.Line, S.Inc x k → g • k = k) ∧ g • y = z := by
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq G S.basePoint x
  have hl' : S.Inc S.basePoint (b⁻¹ • l) := by
    simpa only [← hb, inv_smul_smul] using hl.smul S b⁻¹
  have hm' : S.Inc S.basePoint (b⁻¹ • m) := by
    simpa only [← hb, inv_smul_smul] using hm.smul S b⁻¹
  have hne' : b⁻¹ • l ≠ b⁻¹ • m := (MulAction.injective b⁻¹).ne hne
  have hxy' : S.basePoint ≠ b⁻¹ • y := fun h => hxy (by
    simpa only [hb, smul_inv_smul] using congrArg (b • ·) h)
  have hxz' : S.basePoint ≠ b⁻¹ • z := fun h => hxz (by
    simpa only [hb, smul_inv_smul] using congrArg (b • ·) h)
  obtain ⟨q, hq, he⟩ := S.pointLineKernel_otherLine_transitive hl' hm' hne'
    (hy.smul S b⁻¹) (hz.smul S b⁻¹) hxy' hxz'
  refine ⟨b * q * b⁻¹, ?_, ?_, ?_⟩
  · intro u hu
    have hf := (mem_fixingSubgroup_iff G).mp hq.2 _ (hu.smul S b⁻¹)
    simpa only [mul_smul, smul_inv_smul] using congrArg (b • ·) hf
  · intro k hk
    have hk' : S.Inc S.basePoint (b⁻¹ • k) := by
      simpa only [← hb, inv_smul_smul] using hk.smul S b⁻¹
    have hf := S.core_fixes_incident_coset 0 1 (by decide) hq.1 hk'
    simpa only [mul_smul, smul_inv_smul] using congrArg (b • ·) hf
  · simpa only [mul_smul, smul_inv_smul] using congrArg (b • ·) he

end Quasithin.I5.DSystem
