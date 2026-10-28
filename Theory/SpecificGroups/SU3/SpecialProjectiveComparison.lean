module

public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction
public import Mathlib.GroupTheory.PGroup

/-!
# The special-to-projective comparison for SU₃

The natural map onto the actual projective image has central kernel. Its
members are scalar matrices, and determinant one forces their cubes to be
one. Thus the finite kernel has odd order. When the projective image is
centerless, the kernel equals the special-unitary center; when the special
unitary group is centerless, the natural map itself is an isomorphism.

These facts let fixed-action arguments split off the odd-center case without
assuming that every automorphism of the projective group lifts to SU₃.
They apply to every stored nondegenerate Hermitian form and require no
simplicity or group-order certification.

Source: the special/projective alternatives in Aschbacher–Smith,
*The Classification of Quasithin Groups*, F.6.18(10)–(11), printed pp.309–310,
and their use in 15.4.18, printed pp.1162–1163.
-/

open Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The kernel of the natural projective map consists of central special-unitary elements. -/
public theorem specialToProjective_ker_le_center :
    J.specialToProjective.ker ≤ center J.specialSubgroup := by
  intro x hx
  have hz : x.val ∈ center (GL (Fin 3) E) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hz y.val)

/-- A scalar special-unitary matrix in dimension three has cube one. -/
public theorem specialToProjective_ker_cube (x : J.specialToProjective.ker) : x ^ 3 = 1 := by
  have hz : x.val.val ∈ center (GL (Fin 3) E) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
      congrArg Subtype.val (MonoidHom.mem_ker.mp x.property)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨u, hu⟩ := hz
  have hu3 : u ^ 3 = 1 := by
    have hd := x.val.property.2
    change Matrix.GeneralLinearGroup.det x.val.val = 1 at hd
    rw [← hu, Matrix.GeneralLinearGroup.det_scalar] at hd
    simpa using hd
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val ^ 3 = 1
  rw [← hu, ← map_pow, hu3, map_one]

/-- The finite scalar kernel has odd order, without an order formula for SU₃. -/
public theorem odd_card_specialToProjective_ker [Finite E] :
    Odd (Nat.card J.specialToProjective.ker) := by
  have h3 : IsPGroup 3 J.specialToProjective.ker :=
    fun x => ⟨1, by simpa using J.specialToProjective_ker_cube x⟩
  obtain ⟨n, hn⟩ := h3.exists_card_eq
  rw [hn]
  exact (by decide : Odd 3).pow

/-- If the actual projective image is centerless, its scalar kernel is the whole special-unitary center. -/
public theorem specialToProjective_ker_eq_center
    (hZ : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥) :
    J.specialToProjective.ker = center J.specialSubgroup := by
  apply le_antisymm J.specialToProjective_ker_le_center
  intro x hx
  have hc : J.specialToProjective x ∈ center (ProjectiveSpecialUnitaryMatrixGroup J) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := J.specialToProjective_surjective y
    simpa only [map_mul] using congrArg J.specialToProjective (mem_center_iff.mp hx z)
  simpa only [hZ, mem_bot, MonoidHom.mem_ker] using hc

/-- For a centerless special-unitary group, the natural projective map is an actual group isomorphism. -/
public noncomputable def specialProjectiveEquivOfCenterEqBot
    (hZ : center J.specialSubgroup = ⊥) :
    J.specialSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  MulEquiv.ofBijective J.specialToProjective
    ⟨J.specialToProjective.ker_eq_bot_iff.mp (le_bot_iff.mp
      (J.specialToProjective_ker_le_center.trans_eq hZ)), J.specialToProjective_surjective⟩

end BenderSuzuki.MatrixGroups.HermitianForm
