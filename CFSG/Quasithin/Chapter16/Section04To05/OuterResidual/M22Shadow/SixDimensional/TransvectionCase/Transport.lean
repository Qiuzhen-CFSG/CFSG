module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.TransvectionCase.SevenPointInterface

/-!
# Faithful-image and displacement transports

The linear action image and the automorphism action image are canonically
isomorphic through their common kernel C_M(V). The plane spanned by the
marked vectors is exactly the subspace of the ambient subgroup ⟨r,z⟩.
Thus the computed displacement equality concerns the original subgroup,
rather than an unrelated two-dimensional space.

Source: Aschbacher–Smith, proof of Lemma 16.4.7, printed p.1187.
-/

@[expose] public section

open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.TransvectionCase
open Subgroup BinaryTransvectionGroups
variable {G : Type*} [Group G]
variable (L : Subgroup G) (g r z : G) [IsElementaryAbelian 2 (shadowSpace L r z)]

/-- The two faithful images of the same conjugation action. -/
noncomputable def imageEquivActionRange :
    image L g r z ≃* (shadowAction L g r z).range :=
  (QuotientGroup.quotientKerEquivRange (linearAction L g r z)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      ((linearAction_ker L g r z).trans (shadowAction_ker L g r z).symm)).trans
      (shadowActionQuotientEquivRange L g r z))

theorem imageEquivActionRange_on_element (m : shadowOvergroup L g r z) :
    imageEquivActionRange L g r z ((linearAction L g r z).rangeRestrict m) =
      (shadowAction L g r z).rangeRestrict m := by
  have he : (QuotientGroup.quotientKerEquivRange (linearAction L g r z))
      (QuotientGroup.mk' (linearAction L g r z).ker m) =
        (linearAction L g r z).rangeRestrict m := rfl
  rw [← he]
  simp only [imageEquivActionRange, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

/-- This equivalence intertwines evaluation on the actual shadow space. -/
theorem imageEquivActionRange_apply (a : image L g r z) (v : Space L r z) :
    ((imageEquivActionRange L g r z a).val v.toMul) = (a.val v).toMul := by
  obtain ⟨m, rfl⟩ := (linearAction L g r z).rangeRestrict_surjective a
  rw [imageEquivActionRange_on_element]
  rfl

theorem marked_plane_eq_subspace :
    centerLine (rVector L r z) ⊔ centerLine (zVector L r z) =
      subspace L r z (zpowers r ⊔ zpowers z) := by
  apply le_antisymm (marked_plane_le_subspace L r z)
  let P := centerLine (rVector L r z) ⊔ centerLine (zVector L r z)
  let A : Subgroup (shadowSpace L r z) := P.toAddSubgroup.toSubgroup'
  have hle : zpowers r ⊔ zpowers z ≤ A.map (shadowSpace L r z).subtype := by
    apply sup_le <;> apply zpowers_le.mpr
    · refine ⟨(rVector L r z).toMul, ?_, rfl⟩
      change rVector L r z ∈ P
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    · refine ⟨(zVector L r z).toMul, ?_, rfl⟩
      change zVector L r z ∈ P
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  intro v hv
  obtain ⟨w, hw, he⟩ := hle hv
  have he' : w = v.toMul := Subtype.ext he
  rw [he'] at hw
  exact hw

variable {L g r z}

/-- [V,X] is exactly the actual marked elementary subgroup ⟨r,z⟩. -/
theorem MarkedTransvections.displacement_eq_subspace {T : Sylow 2 G}
    (d : MarkedTransvections T L g r z) :
    displacementSpan (zpowers (linearAction L g r z d.first) ⊔
      zpowers (linearAction L g r z d.second)) =
        subspace L r z (zpowers r ⊔ zpowers z) :=
  d.displacement_eq.trans (marked_plane_eq_subspace L r z)

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.TransvectionCase
