module
public import Theory.SpecificGroups.PSL3Four.CentralCover.InvolutionClasses.Lifting
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter

/-!
# Field-coset fusion from the marked diagonal action

The nontrivial diagonal action on the covering center has order three.
Its inversion by the field involution forces that involution to move the
center, which discharges the central lifting premise of field-coset fusion.
Both the intrinsic and original ambient statements retain an actual
component conjugator.
Source: Aschbacher–Smith, 15.3.38, printed pp.1136–1137.
-/

public section
open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer
open CoverCentralizers
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

/-- The field involution moves the covering center because it inverts the
nontrivial diagonal action of order three. -/
theorem NormalizerGeometry.field_moves_center {d : Overgroup L}
    (n : NormalizerGeometry d) :
    ∃ z : center L, n.fieldI * ((z : L) : I) * n.fieldI⁻¹ ≠ ((z : L) : I) := by
  by_contra! hf
  have hfcentral : n.fieldI ∈ centralizer ((center L).map L.subtype : Set I) := by
    intro z hz
    obtain ⟨z, hz, rfl⟩ := hz
    exact (mul_inv_eq_iff_eq_mul.mp (hf ⟨z, hz⟩)).symm
  let a := centralFourAction d n.graphFieldI
  have hf1 : a (fieldInCentralizer n) = 1 :=
    (centralFourAction_eq_one_iff d n.graphFieldI
      n.graphField_mem_centerCentralizer _).mpr hfcentral
  have hi : a n.diagonalInCentralizer = (a n.diagonalInCentralizer)⁻¹ := by
    simpa only [map_mul, map_inv, hf1, inv_one, one_mul, mul_one] using
      congrArg a (fieldInCentralizer_inverts_diagonal n)
  have h2 : a n.diagonalInCentralizer ^ 2 = 1 := by
    calc
      _ = (a n.diagonalInCentralizer)⁻¹ * a n.diagonalInCentralizer := by
        rw [pow_two]; exact congrArg (· * a n.diagonalInCentralizer) hi
      _ = 1 := inv_mul_cancel _
  have h3 : a n.diagonalInCentralizer ^ 3 = 1 := by
    rw [← map_pow, show n.diagonalInCentralizer ^ 3 = 1 from
      Subtype.ext n.diagonalElement_cube, map_one]
  have h1 : a n.diagonalInCentralizer = 1 := by
    simpa only [pow_succ, h2, one_mul] using h3
  exact DiagonalCenter.diagonal_moves_center d n
    ((centralFourAction_eq_one_iff d n.graphFieldI
      n.graphField_mem_centerCentralizer _).mp h1)

/-- Every involution in the actual field coset is conjugate by the component. -/
theorem NormalizerGeometry.field_coset_conjugate {d : Overgroup L}
    (n : NormalizerGeometry d) (x : I) (hx : x ^ 2 = 1)
    (hxL : x * n.fieldI⁻¹ ∈ L) :
    ∃ b : L, (b : I) * n.fieldI * (b : I)⁻¹ = x :=
  InvolutionClasses.field_coset_conjugate d n.fieldI n.field_sq
    n.field_frobenius.symm n.field_moves_center x hx hxL

variable {G : Type*} [Group G]

/-- The same conjugacy statement in the original ambient group. -/
theorem NormalizerGeometry.ambient_field_coset_conjugate
    (I : Subgroup G) {L : Subgroup I} [L.Normal] {d : Overgroup L}
    (n : NormalizerGeometry d) (x : G) (hx : orderOf x = 2)
    (hxL : x * (n.fieldI : G)⁻¹ ∈ L.map I.subtype) :
    IsConj x (n.fieldI : G) := by
  have hprod : x * (n.fieldI : G)⁻¹ ∈ I := map_subtype_le L hxL
  have hxI : x ∈ I := by
    simpa only [inv_mul_cancel_right] using I.mul_mem hprod n.fieldI.property
  have hxL' : (⟨x, hxI⟩ : I) * n.fieldI⁻¹ ∈ L := by
    obtain ⟨z, hz, he⟩ := hxL
    exact (show z = (⟨x, hxI⟩ : I) * n.fieldI⁻¹ from Subtype.ext he) ▸ hz
  obtain ⟨b, hb⟩ := n.field_coset_conjugate ⟨x, hxI⟩
    (Subtype.ext (hx ▸ pow_orderOf_eq_one x)) hxL'
  exact (isConj_iff.mpr ⟨((b : I) : G), congrArg Subtype.val hb⟩).symm

end Matrix.PSL3Four.ExtendedCentralizer
