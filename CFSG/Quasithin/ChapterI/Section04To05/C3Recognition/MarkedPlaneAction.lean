module

public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.MarkedPlane

/-!
# The actual plane vertex on its marked three-space

The original plane group is transitive on its Fano points, hence on every
nonzero vector of the retained three-space. Its center maps trivially to
PSL₃(2), so lies in the actual plane core and fixes that space pointwise.
These are the literal action hypotheses for the odd-Lagrangian centralizer
argument; no unmarked abstract isomorphism is used for the plane vertex.
-/

public noncomputable section
namespace Quasithin.I5.C3Recognition
open Subgroup Matrix Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G] {S : DSystem .C3 G}

theorem plane_center_le_core : center (S.family 2) ≤ pCore 2 (S.family 2) := by
  obtain ⟨e⟩ := S.plane_quotient
  let f := (Matrix.PSL3Two.equiv.symm.toMonoidHom).comp (S.localQuotientMap 2 e)
  have hf : Function.Surjective f := Matrix.PSL3Two.equiv.symm.surjective.comp
    (S.localQuotientMap_surjective 2 e)
  intro a ha
  have hz : f a ∈ center Matrix.PSL3Two.SL := by
    rw [mem_center_iff]
    intro b
    obtain ⟨c, rfl⟩ := hf b
    simpa only [map_mul] using congrArg f (mem_center_iff.mp ha c)
  rw [Matrix.PSL3Two.center_eq_bot, mem_bot] at hz
  have hk : S.localQuotientMap 2 e a = 1 := Matrix.PSL3Two.equiv.symm.injective
    (hz.trans (map_one _).symm)
  change a ∈ (S.localQuotientMap 2 e).ker at hk
  rwa [S.localQuotientMap_ker] at hk

namespace SymplecticMark
variable (m : SymplecticMark S)

theorem plane_vertex_preserves_space (g : S.family 2) (u : Vector (ZMod 2))
    (hu : u ∈ m.planeSpace S.basePlane) :
    toLinear (m.hom g.val) u ∈ m.planeSpace S.basePlane := by
  have hgp : g.val • S.basePlane = S.basePlane := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [S.stabilizer_basePlane]
    exact g.property
  rcases (m.mem_planeSpace_iff S.basePlane u).mp hu with rfl | ⟨x, hx, rfl⟩
  · exact (map_zero (toLinear (m.hom g.val))) ▸ Submodule.zero_mem _
  · rw [toLinear_apply, Theory.SpecificGroups.SymplecticSix.smul_eq_mulVec, m.equivariant]
    apply m.point_mem_planeSpace
    simpa only [hgp] using hx.smul S g.val

theorem plane_vertex_transitive (u v : Vector (ZMod 2))
    (hu : u ∈ m.planeSpace S.basePlane) (hu0 : u ≠ 0)
    (hv : v ∈ m.planeSpace S.basePlane) (hv0 : v ≠ 0) :
    ∃ g : S.family 2, toLinear (m.hom g.val) u = v := by
  obtain ⟨x, hx, rfl⟩ := ((m.mem_planeSpace_iff S.basePlane u).mp hu).resolve_left hu0
  obtain ⟨y, hy, rfl⟩ := ((m.mem_planeSpace_iff S.basePlane v).mp hv).resolve_left hv0
  let e := S.pointedCosetEquiv 2 0 (by decide)
  let x' := e.symm ⟨x, CosetGeometry.Incident.symm S.family hx⟩
  let y' := e.symm ⟨y, CosetGeometry.Incident.symm S.family hy⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (S.family 2) x' y'
  refine ⟨g, ?_⟩
  rw [toLinear_apply, Theory.SpecificGroups.SymplecticSix.smul_eq_mulVec, m.equivariant]
  apply congrArg m.point
  have he := S.pointedCosetEquiv_smul 2 0 (by decide) g x'
  rw [hg] at he
  simpa only [x', y', e, Equiv.apply_symm_apply] using he.symm

theorem plane_center_fixes_space {a : S.family 2} (ha : a ∈ center (S.family 2))
    (u : Vector (ZMod 2)) (hu : u ∈ m.planeSpace S.basePlane) :
    toLinear (m.hom a.val) u = u := by
  rcases (m.mem_planeSpace_iff S.basePlane u).mp hu with rfl | ⟨x, hx, rfl⟩
  · exact map_zero _
  have hq : a.val ∈ S.Q 2 := mem_map.mpr ⟨a, plane_center_le_core ha, rfl⟩
  have hf := S.core_fixes_incident_coset 2 0 (by decide) hq
    (CosetGeometry.Incident.symm S.family hx)
  rw [toLinear_apply, Theory.SpecificGroups.SymplecticSix.smul_eq_mulVec, m.equivariant, hf]

end SymplecticMark
end Quasithin.I5.C3Recognition
