module
public import Theory.Representation.SpecialLinearThreeFrameGeometry
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.Coordinates

/-!
# The SL₃ model geometry in the source coordinates of G.2.5

The source's three independent points give a concrete frame. The exact
model equivalence carries each displacement-defined source root onto its
matrix root. In particular the printed root with center V₁ and axis
V₁+V₁ᵍ fixes the second natural point and equals the corresponding dual root.

Transport of the contragredient action identifies the common F-linear fixed
space of the first two point radicals with the marked plane annihilator.
No identification of ambient U* with a point radical is assumed here; that
separate source identification is still needed when applying these facts to U.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.1.1–4 and
G.2.5(6), printed pp.327–328,335–336, PDF pp.338–339,346–347.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
open Subgroup Setup Projective Matrix
namespace DualGeometry.ModelGeometry
open CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)

/-- The source frame in the actual natural coordinates. -/
def frame : FrameGeometry.Frame F where
  point := ![d.point, (conjugatePoint d ⟨g, d.g_mem⟩).val,
    (conjugatePoint d ⟨h, d.h_mem⟩).val]
  dimension := by
    intro i
    fin_cases i
    · exact d.point_dimension
    · exact (conjugatePoint d ⟨g, d.g_mem⟩).property
    · exact (conjugatePoint d ⟨h, d.h_mem⟩).property
  disjoint := natural_points_disjoint d
  third_disjoint := natural_third_disjoint d
  span := natural_points_span d

/-- The source roots are precisely the inverse images of the matrix roots. -/
theorem rootGroup_eq_comap (A B : Submodule F (Fin 3 → F)) :
    rootGroup (naturalAction d) A B =
      (FrameGeometry.root A B).comap d.model.toMonoidHom := rfl

/-- The model equivalence maps the whole root, with no lost scalar kernel. -/
theorem map_rootGroup (A B : Submodule F (Fin 3 → F)) :
    (rootGroup (naturalAction d) A B).map d.model.toMonoidHom = FrameGeometry.root A B := by
  rw [rootGroup_eq_comap]
  exact Subgroup.map_comap_eq_self_of_surjective d.model.surjective _

/-- The center and axis of the root in the printed dual argument. -/
theorem marked_root_eq_comap :
    rootGroup (naturalAction d) d.point (pairPlane d) =
      ((frame d).axisRoot 0 1).comap d.model.toMonoidHom := rfl

/-- The dual root in the printed argument is the same literal frame root. -/
theorem marked_dual_root_eq_comap :
    rootGroup (dualAction d) (dualPoint d).val d.point.dualAnnihilator =
      ((frame d).axisRoot 0 1).comap d.model.toMonoidHom := by
  change rootGroup (dualAction d) (pairPlane d).dualAnnihilator d.point.dualAnnihilator = _
  rw [← dual_rootGroup]
  exact marked_root_eq_comap d

/-- This root fixes the indicated second point, in the exact natural action. -/
theorem marked_root_stabilizes_second (a : D.star D.L)
    (ha : a ∈ rootGroup (naturalAction d) d.point (pairPlane d)) :
    (conjugatePoint d ⟨g, d.g_mem⟩).val.map (naturalAction d a) =
      (conjugatePoint d ⟨g, d.g_mem⟩).val := by
  apply (FrameGeometry.mem_stabilizer_iff _ (d.model a)).mp
  exact FrameGeometry.root_le_stabilizer_of_le_axis
    (show (conjugatePoint d ⟨g, d.g_mem⟩).val ≤ pairPlane d from le_sup_right) ha

/-- Both point radicals preserve the natural pair plane. -/
theorem pair_radicals_stabilize_plane (a : D.star D.L)
    (ha : a ∈ rootGroup (naturalAction d) d.point d.point ⊔
      rootGroup (naturalAction d) (conjugatePoint d ⟨g, d.g_mem⟩).val
        (conjugatePoint d ⟨g, d.g_mem⟩).val) :
    (pairPlane d).map (naturalAction d a) = pairPlane d := by
  apply (FrameGeometry.mem_stabilizer_iff _ (d.model a)).mp
  have hmap : d.model a ∈ FrameGeometry.pointRadical d.point ⊔
      FrameGeometry.pointRadical (conjugatePoint d ⟨g, d.g_mem⟩).val := by
    change d.model a ∈ FrameGeometry.root d.point d.point ⊔
      FrameGeometry.root (conjugatePoint d ⟨g, d.g_mem⟩).val (conjugatePoint d ⟨g, d.g_mem⟩).val
    rw [← map_rootGroup d d.point d.point,
      ← map_rootGroup d (conjugatePoint d ⟨g, d.g_mem⟩).val
        (conjugatePoint d ⟨g, d.g_mem⟩).val, ← Subgroup.map_sup]
    exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  exact (sup_le (FrameGeometry.root_le_stabilizer_of_center_le
      (show d.point ≤ pairPlane d from le_sup_left))
    (FrameGeometry.root_le_stabilizer_of_center_le
      (show (conjugatePoint d ⟨g, d.g_mem⟩).val ≤ pairPlane d from le_sup_right))) hmap

/-- The source dual action uses inverse matrices under the same model equivalence. -/
theorem dualAction_model (a : D.star D.L) (f : Module.Dual F (Fin 3 → F)) :
    dualAction d a f = FrameGeometry.natural.dual (d.model a) f := by
  apply LinearMap.ext
  intro v
  change f (FrameGeometry.natural (d.model a⁻¹) v) =
    f (FrameGeometry.natural ((d.model a)⁻¹) v)
  rw [map_inv]

/-- Pullback along the actual model preserves common fixed spaces in the F-dual. -/
theorem dualFixed_comap (H : Subgroup SL(3, F)) :
    Representation.invariants ((dualAction d).comp
      (H.comap d.model.toMonoidHom).subtype) = FrameGeometry.dualFixed H := by
  ext f
  constructor
  · intro hf
    change ∀ a : H, FrameGeometry.natural.dual a.val f = f
    intro a
    have he := hf ⟨d.model.symm a.val, by
      change d.model (d.model.symm a.val) ∈ H
      rw [d.model.apply_symm_apply]
      exact a.property⟩
    change dualAction d (d.model.symm a.val) f = f at he
    simpa only [dualAction_model, d.model.apply_symm_apply] using he
  · intro hf
    change ∀ a : H.comap d.model.toMonoidHom, dualAction d a.val f = f
    intro a
    rw [dualAction_model]
    exact hf ⟨d.model a.val, a.property⟩

/-- The plane annihilator is exactly the fixed space of the two point radicals
in the genuine F-linear contragredient representation. -/
theorem pair_radicals_dual_fixed :
    Representation.invariants ((dualAction d).comp
      (rootGroup (naturalAction d) d.point d.point ⊔
        rootGroup (naturalAction d) (conjugatePoint d ⟨g, d.g_mem⟩).val
          (conjugatePoint d ⟨g, d.g_mem⟩).val).subtype) = pairAnnihilator d := by
  have he : rootGroup (naturalAction d) d.point d.point ⊔
      rootGroup (naturalAction d) (conjugatePoint d ⟨g, d.g_mem⟩).val
        (conjugatePoint d ⟨g, d.g_mem⟩).val =
      (FrameGeometry.pointRadical d.point ⊔ FrameGeometry.pointRadical
        (conjugatePoint d ⟨g, d.g_mem⟩).val).comap d.model.toMonoidHom := by
    apply Subgroup.map_injective (f := d.model.toMonoidHom) d.model.injective
    rw [Subgroup.map_sup, map_rootGroup, map_rootGroup,
      Subgroup.map_comap_eq_self_of_surjective d.model.surjective]
    rfl
  rw [he, dualFixed_comap]
  exact FrameGeometry.dualFixed_pair _ _ ((frame d).point_ne_top 0) ((frame d).point_ne_top 1)

end DualGeometry.ModelGeometry
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
