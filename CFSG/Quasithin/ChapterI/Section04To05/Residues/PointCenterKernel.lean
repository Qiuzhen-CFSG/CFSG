module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PointCoreBound

/-!
# The center of the original point group fixes every neighbor

The center lies in the point core and hence in the original point-plane
intersection. Its image in the plane parabolic is central. Both plane
parabolics are the actual symmetric group on four letters, whose center
is trivial, so the point-group center lies in the plane core. It therefore
fixes the base line pointwise. Centrality transports this to every line
through the base point.

This is the final local input of the I.5.13 contradiction, printed p.423.
-/

private theorem symmetric_four_center_element :
    ∀ a : Equiv.Perm (Fin 4), (∀ b, b * a = a * b) → a = 1 := by
  decide +kernel

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem plane_point_parabolic_center
    (e : (S.family 2 ⧸ pCore 2 (S.family 2)) ≃* Matrix.PSL3Two.PSL)
    (he : (localParabolic S.family 2 0).map (S.localQuotientMap 2 e) =
      Matrix.PSL3Two.pointParabolic ∨
      (localParabolic S.family 2 0).map (S.localQuotientMap 2 e) =
      Matrix.PSL3Two.lineParabolic) :
    center ((localParabolic S.family 2 0).map (S.localQuotientMap 2 e)) = ⊥ := by
  have h {K : Type} [Group K] (f : K ≃* Equiv.Perm (Fin 4)) : center K = ⊥ := by
    apply le_bot_iff.mp
    intro a ha
    rw [mem_bot]
    apply f.injective
    rw [map_one]
    apply symmetric_four_center_element
    intro b
    obtain ⟨c, rfl⟩ := f.surjective b
    simpa only [map_mul] using congrArg f (mem_center_iff.mp ha c)
  rcases he with he | he
  · rw [he]
    exact h Matrix.PSL3Two.pointParabolicEquivS4
  · rw [he]
    exact h Matrix.PSL3Two.lineParabolicEquivS4

theorem point_center_le_planeCore {a : S.family 0} (ha : a ∈ center (S.family 0)) :
    a.val ∈ S.Q 2 := by
  have hqa : a.val ∈ S.Q 0 := mem_map.mpr ⟨a, S.point_center_le_core ha, rfl⟩
  have h2a : a.val ∈ S.family 2 := S.T_le 2 (S.Q_le_T 0 hqa)
  let b : S.pair 2 0 := ⟨a.val, h2a, a.property⟩
  obtain ⟨e, he⟩ := S.plane_standard_quotientMark
  let f := S.pairQuotientMap 2 0 e
  have hb : f b ∈ center ((localParabolic S.family 2 0).map (S.localQuotientMap 2 e)) := by
    rw [mem_center_iff]
    intro c
    obtain ⟨u, rfl⟩ := S.pairQuotientMap_surjective 2 0 e c
    have hcomm : u * b = b * u := by
      apply Subtype.ext
      change u.val * a.val = a.val * u.val
      exact congrArg (fun v : S.family 0 => v.val) (mem_center_iff.mp ha ⟨u.val, u.property.2⟩)
    simpa only [map_mul] using congrArg f hcomm
  rw [S.plane_point_parabolic_center e (he.imp And.left And.left), mem_bot] at hb
  have hk : b ∈ f.ker := hb
  rw [S.pairQuotientMap_ker] at hk
  exact hk

theorem point_center_mem_neighborCore {a : S.family 0} (ha : a ∈ center (S.family 0)) :
    a.val ∈ S.neighborCore := by
  have hqa : a.val ∈ S.Q 0 := mem_map.mpr ⟨a, S.point_center_le_core ha, rfl⟩
  have hfix {y : S.Point} (hy : S.Inc y S.baseLine) : a.val • y = y := by
    apply S.core_fixes_incident_coset 2 0 (by decide) (S.point_center_le_planeCore ha)
    apply CosetGeometry.Incident.symm S.family
    exact S.point_line_plane hy (show S.Inc S.baseLine S.basePlane from ⟨1, rfl, rfl⟩)
  refine ⟨hqa, (mem_fixingSubgroup_iff G).mpr ?_⟩
  rintro y ⟨l, hxl, hyl⟩
  obtain ⟨g, hg, hgl⟩ := (CosetGeometry.incident_base_iff S.family 0 ⟨1, l⟩).mp hxl
  have hl : g • S.baseLine = l := by
    change ((g * 1 : G) : G ⧸ S.family 1) = l
    simpa only [mul_one] using hgl
  have hy : S.Inc (g⁻¹ • y) S.baseLine := by
    simpa only [← hl, inv_smul_smul] using hyl.smul S g⁻¹
  have hf := congrArg (g • ·) (hfix hy)
  have hc : g * a.val = a.val * g := congrArg Subtype.val (mem_center_iff.mp ha ⟨g, hg⟩)
  have hh : (g * a.val) • (g⁻¹ • y) = y := by
    simpa only [mul_smul, smul_inv_smul] using hf
  simpa only [hc, mul_smul, smul_inv_smul] using hh

end Quasithin.I5.DSystem
