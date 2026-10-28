module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LineAction

/-!
# The edge stabilizer escapes the plane stabilizer

The actual K acts trivially on all five points of the source line. Its marked
three-space action nevertheless exchanges z and r, so K supplies an element
fixing both ends of every edge on that line and lying outside C_G(z).
This discharges the unchanged Input edge-fixer premise.
Source: Aschbacher–Segev (1991), (4.4), (5.1), and the system of §7.
-/
public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
namespace LocalData
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

theorem edge_fixer (t : G) (ht : t ∈ a.L.G₂) :
    ¬ a.P.M ⊓ a.P.M.comap (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer z := by
  obtain ⟨k,hk⟩ := a.d.exists_K_marked_permutation h (Equiv.swap 0 1)
  have hkz : (k : G)*z*(k : G)⁻¹ = a.d.r := by
    simpa [SourceRecognition.ThreeSpaceData.markedPoint,Equiv.swap_apply_def] using hk 0
  have hkN : (k : G) ∈ a.L.G₂ := by
    rw [a.line_normalizer]
    exact a.d.K_le_normalizer k.property
  have hfix := (a.point_action_kernel ⟨k,hkN⟩).mpr k.property
  have hkM : (k : G) ∈ a.P.M := by
    apply (Cosets.vertex_eq_base _ _).mp
    simpa only [Cosets.smul_vertex,mul_one] using
      hfix (Cosets.vertex a.P.M 1) ⟨1,rfl,rfl⟩
  have hkt : (k : G) ∈ a.P.M.comap (MulAut.conj t⁻¹).toMonoidHom := by
    rw [←Cosets.stabilizer_vertex]
    exact hfix (Cosets.vertex a.P.M t) ⟨t,rfl,(Cosets.vertex_eq_base _ _).mpr ht⟩
  intro hle
  have hc := mem_centralizer_singleton_iff.mp (hle ⟨hkM,hkt⟩)
  have hz : (k : G)*z*(k : G)⁻¹ = z := by rw [hc,mul_inv_cancel_right]
  exact a.d.r_ne (hkz.symm.trans hz)

end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
