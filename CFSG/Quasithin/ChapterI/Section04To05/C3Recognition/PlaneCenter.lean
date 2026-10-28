module

public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.MarkedPlaneAction
public import Theory.LinearAlgebra.OddLagrangianCentralizer

/-!
# Trivial center of the original plane vertex

The marked Fano plane spans an odd-dimensional Lagrangian in the recognized
symplectic six-space. A central plane-vertex element fixes that Lagrangian
pointwise. Its displacement map has image in the Lagrangian. If nonzero,
transitivity on its nonzero vectors forces rank three; the resulting
symmetric displacement form is alternating by the same transitivity and has
odd rank, impossible. Thus the marked action is trivial and faithfulness
kills the original plane-vertex center.
-/

public noncomputable section
namespace Quasithin.I5.C3Recognition
open Subgroup Matrix Theory.LinearAlgebra Theory.SpecificGroups.SymplecticSix
open Theory.SpecificGroups.SymplecticSix.TwoLocalCover
variable {G : Type*} [Group G] {S : DSystem .C3 G}

theorem plane_center_eq_bot (S : DSystem .C3 G) : center (S.family 2) = ⊥ := by
  let d := S.source_local_polar_facts
  let m : SymplecticMark S := Classical.choice
    (exists_symplecticMark S ⟨S.c3_points_card d, S.faithful_points, S.c3_exists_noncollinear,
      fun x y h => S.source_one_or_all_triples d x y h⟩)
  let W := m.planeSpace S.basePlane
  have hW : (form (ZMod 2)).orthogonal W = W := m.planeSpace_orthogonal _
  have hdim : 1 < Module.finrank (ZMod 2) W := by rw [m.planeSpace_finrank]; decide
  have hodd : Odd (Module.finrank (ZMod 2) W) := by rw [m.planeSpace_finrank]; decide
  apply le_bot_iff.mp
  intro a ha
  let ρ : S.family 2 →* (Vector (ZMod 2) ≃ₗ[ZMod 2] Vector (ZMod 2)) :=
    toLinear.comp (m.hom.comp (S.family 2).subtype)
  have hc : toLinear (m.hom a.val) = 1 :=
    centralizer_eq_one_of_odd_lagrangian (form (ZMod 2)) form_nondegenerate form_alternating
      W hW hodd hdim ρ (fun g x y => preserves_form (m.hom g.val) x y)
      (fun u hu hu0 v hv hv0 => m.plane_vertex_transitive u v hu hu0 hv hv0)
      (toLinear (m.hom a.val)) (fun x y => preserves_form (m.hom a.val) x y)
      (fun w hw => m.plane_center_fixes_space ha w hw) (fun g x => by
        have h := congrArg (fun b : S.family 2 => ρ b x) (mem_center_iff.mp ha g)
        change ρ a (ρ g x) = ρ g (ρ a x)
        simpa only [map_mul, LinearEquiv.mul_apply] using h.symm)
  rw [mem_bot]
  apply Subtype.ext
  let : FaithfulSMul G S.Point := S.faithful_points
  apply eq_of_smul_eq_smul (α := S.Point)
  intro x
  apply m.point_injective
  rw [← m.equivariant]
  change toLinear (m.hom a.val) (m.point x) = m.point ((1 : G) • x)
  rw [hc, one_smul]
  rfl

end Quasithin.I5.C3Recognition
