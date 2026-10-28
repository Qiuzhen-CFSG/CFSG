module

public import Theory.GroupTheory.DihedralInvolutionLift

/-!
# The cyclic-four quotient of a split dihedral extension

A surjection to D₈ gives a cyclic-four quotient of the rotation preimage.
Its kernel is the original kernel, and any lift of a generating rotation
supplements that kernel. A section of the surjection supplies involutory
reflection lifts and an order-four rotation lift, including the relation
`t τ t⁻¹ = τ f` with `f = w²`.

This is the elementary group-theoretic construction used in the proof of
Aschbacher--Smith 15.3.38, combined manuscript (1 March 2004), printed p.1136.
The existence of the section and the interpretation of its reflections as
specific automorphisms are separate hypotheses. No fusion statement is
assumed or proved in this module.
-/

public section

open Subgroup
namespace DihedralGroup

/-- The actual rotation subgroup of D₈. -/
abbrev RotationsFour := zpowers (r 1 : DihedralGroup 4)
/-- The distinguished generating rotation. -/
def rotationGeneratorFour : RotationsFour := ⟨r 1, mem_zpowers _⟩

private theorem rotationGeneratorFour_generates (x : RotationsFour) :
    x ∈ zpowers rotationGeneratorFour := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp x.property
  exact mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩

/-- Rotation coordinates, sending the distinguished rotation to 1 modulo 4. -/
noncomputable def rotationsFourEquiv : RotationsFour ≃* Multiplicative (ZMod 4) :=
  (zmodMulEquivOfGenerator rotationGeneratorFour_generates
    (by rw [Nat.card_zpowers, orderOf_r_one])).symm

theorem rotationsFourEquiv_generator :
    rotationsFourEquiv rotationGeneratorFour = Multiplicative.ofAdd (1 : ZMod 4) := by
  exact zmodMulEquivOfGenerator_symm_apply_generator _ _

/-- Restrict a dihedral map to its rotation preimage. -/
def rotationRestriction {T : Type*} [Group T] (ρ : T →* DihedralGroup 4) :
    rotationPreimage ρ →* RotationsFour :=
  { toFun := fun x => ⟨ρ x, x.property⟩
    map_one' := Subtype.ext ρ.map_one
    map_mul' := fun x y => Subtype.ext (ρ.map_mul x y) }

/-- The cyclic-four quotient map on the rotation preimage. -/
noncomputable def rotationQuotient {T : Type*} [Group T] (ρ : T →* DihedralGroup 4) :
    rotationPreimage ρ →* Multiplicative (ZMod 4) :=
  rotationsFourEquiv.toMonoidHom.comp (rotationRestriction ρ)

theorem rotationQuotient_surjective {T : Type*} [Group T]
    (ρ : T →* DihedralGroup 4) (hρ : Function.Surjective ρ) :
    Function.Surjective (rotationQuotient ρ) := by
  apply rotationsFourEquiv.surjective.comp
  intro y
  obtain ⟨x, hx⟩ := hρ y
  exact ⟨⟨x, show ρ x ∈ RotationsFour from hx ▸ y.property⟩, Subtype.ext hx⟩

theorem rotationQuotient_eq_one_iff {T : Type*} [Group T]
    (ρ : T →* DihedralGroup 4) (x : rotationPreimage ρ) :
    rotationQuotient ρ x = 1 ↔ ρ x = 1 := by
  change rotationsFourEquiv (rotationRestriction ρ x) = 1 ↔ ρ x = 1
  rw [map_eq_one_iff _ rotationsFourEquiv.injective]
  exact Subtype.ext_iff

theorem rotationQuotient_generator {T : Type*} [Group T]
    (ρ : T →* DihedralGroup 4) (w : rotationPreimage ρ) (hw : ρ w = r 1) :
    rotationQuotient ρ w = Multiplicative.ofAdd (1 : ZMod 4) := by
  have h : rotationRestriction ρ w = rotationGeneratorFour := Subtype.ext hw
  change rotationsFourEquiv (rotationRestriction ρ w) = _
  rw [h, rotationsFourEquiv_generator]

theorem rotationPreimage_eq_zpowers_sup_ker {T : Type*} [Group T]
    (ρ : T →* DihedralGroup 4) (w : T) (hw : ρ w = r 1) :
    rotationPreimage ρ = zpowers w ⊔ ρ.ker := by
  rw [rotationPreimage, ← hw, ← MonoidHom.map_zpowers, comap_map_eq]

end DihedralGroup

namespace DihedralGroup
variable {P : Type*} [Group P]

/-- An actual split epimorphism to D₈ with prescribed kernel. The record
contains no transfer or fusion conclusions. -/
structure SplitSection (R : Subgroup P) where
  projection : P →* DihedralGroup 4
  sectionMap : DihedralGroup 4 →* P
  rightInverse : Function.RightInverse sectionMap projection
  kernel : projection.ker = R

namespace SplitSection
variable {R : Subgroup P} (d : SplitSection R)

/-- The lift of the generating rotation. -/
def rotation : P := d.sectionMap (r 1)
/-- The lift of the first reflection. No model action is asserted by this name. -/
def firstReflection : P := d.sectionMap (sr 0)
/-- The adjacent reflection, conjugating the first reflection by the half-turn. -/
def secondReflection : P := d.sectionMap (sr 1)
/-- The central half-turn in the chosen dihedral complement. -/
def halfTurn : P := d.sectionMap (r 2)

theorem section_injective : Function.Injective d.sectionMap :=
  d.rightInverse.injective

theorem projection_surjective : Function.Surjective d.projection :=
  d.rightInverse.surjective

theorem rotation_order : orderOf d.rotation = 4 := by
  rw [rotation, orderOf_injective d.sectionMap d.section_injective, orderOf_r_one]

theorem firstReflection_order : orderOf d.firstReflection = 2 := by
  rw [firstReflection, orderOf_injective d.sectionMap d.section_injective, orderOf_sr]

theorem secondReflection_order : orderOf d.secondReflection = 2 := by
  rw [secondReflection, orderOf_injective d.sectionMap d.section_injective, orderOf_sr]

theorem halfTurn_eq_rotation_sq : d.halfTurn = d.rotation ^ 2 := by
  rw [halfTurn, rotation, ← map_pow]
  rfl

theorem halfTurn_order : orderOf d.halfTurn = 2 := by
  rw [halfTurn, orderOf_injective d.sectionMap d.section_injective]
  exact orderOf_eq_prime (by decide) (by decide)

theorem conjugate_firstReflection : (MulAut.conj d.secondReflection) d.firstReflection = d.firstReflection * d.halfTurn := by
  change d.sectionMap (sr 1) * d.sectionMap (sr 0) * (d.sectionMap (sr 1))⁻¹ =
    d.sectionMap (sr 0) * d.sectionMap (r 2)
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  congr 1

/-- The preimage of the rotation subgroup. -/
def transferSubgroup : Subgroup P := rotationPreimage d.projection

theorem transferSubgroup_eq :
    d.transferSubgroup = zpowers d.rotation ⊔ R := by
  rw [transferSubgroup, rotationPreimage_eq_zpowers_sup_ker d.projection d.rotation
    (d.rightInverse (r 1)), d.kernel]

theorem transferSubgroup_index : d.transferSubgroup.index = 2 :=
  rotationPreimage_index d.projection d.projection_surjective

/-- The generating rotation lift, as an element of the preimage. -/
def rotationInTransfer : d.transferSubgroup :=
  ⟨d.rotation, show d.projection d.rotation ∈ RotationsFour by
    rw [show d.projection d.rotation = r 1 from d.rightInverse _]
    exact mem_zpowers _⟩

/-- The square of the rotation lift, as an element of the preimage. -/
def halfTurnInTransfer : d.transferSubgroup := d.rotationInTransfer ^ 2

theorem halfTurnInTransfer_coe : (d.halfTurnInTransfer : P) = d.halfTurn :=
  d.halfTurn_eq_rotation_sq.symm

/-- The specified cyclic-four quotient of the rotation preimage. -/
noncomputable def cyclicQuotient : d.transferSubgroup →* Multiplicative (ZMod 4) :=
  rotationQuotient d.projection

theorem cyclicQuotient_surjective : Function.Surjective d.cyclicQuotient :=
  rotationQuotient_surjective d.projection d.projection_surjective

theorem cyclicQuotient_kernel (x : d.transferSubgroup) :
    d.cyclicQuotient x = 1 ↔ (x : P) ∈ R := by
  apply (rotationQuotient_eq_one_iff d.projection x).trans
  change (x : P) ∈ d.projection.ker ↔ _
  rw [d.kernel]

theorem cyclicQuotient_rotation :
    d.cyclicQuotient d.rotationInTransfer = Multiplicative.ofAdd (1 : ZMod 4) :=
  rotationQuotient_generator d.projection d.rotationInTransfer (d.rightInverse _)

theorem cyclicQuotient_halfTurn :
    d.cyclicQuotient d.halfTurnInTransfer = Multiplicative.ofAdd (2 : ZMod 4) := by
  rw [halfTurnInTransfer, map_pow, d.cyclicQuotient_rotation]
  rfl

/-- An actual quotient isomorphism; `cyclicQuotient_ker_eq` identifies the
denominator with the prescribed kernel inside the rotation preimage. -/
noncomputable def quotientEquiv :
    (d.transferSubgroup ⧸ d.cyclicQuotient.ker) ≃* Multiplicative (ZMod 4) :=
  QuotientGroup.quotientKerEquivOfSurjective d.cyclicQuotient d.cyclicQuotient_surjective

theorem cyclicQuotient_ker_eq :
    d.cyclicQuotient.ker = (R).subgroupOf d.transferSubgroup := by
  ext x
  exact d.cyclicQuotient_kernel x

end SplitSection
end DihedralGroup
