module

public import Theory.GroupTheory.Amalgam.MixedDihedralEight.Models

/-!
# Concrete exceptional vertices of order twenty-four

Reflection parity gives D₂₄: its rotation is the product of the D₈ rotation
and a three-cycle. Rotation parity gives the specified extension of C₃×E₄
by an involution; that involution inverts the cubic and exchanges the two
marked noncentral involutions of E₄. These coordinates distinguish the
extension and its marked overlap from other groups of the same order.

Source: Aschbacher–Smith F.6.5(2)(iii–iv), printed p.305.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.RankTwoAmalgam.MixedEight

def cubic : CubicFiber.S3 := Equiv.swap 0 1 * Equiv.swap 1 2

def dihedralWord : DihedralGroup 12 → D8 × CubicFiber.S3
  | .r i => (.r i.val, cubic ^ i.val)
  | .sr i => (.sr i.val, Equiv.swap 0 1 * cubic ^ i.val)

def dihedralHom : DihedralGroup 12 →* CubicFiber.group reflectionCharacter :=
  ({ toFun := dihedralWord
     map_one' := by decide +kernel
     map_mul' := by decide +kernel } : DihedralGroup 12 →* D8 × CubicFiber.S3).codRestrict
    (CubicFiber.group reflectionCharacter) (by
      change ∀ d, reflectionCharacter (dihedralWord d).1 = Equiv.Perm.sign (dihedralWord d).2
      decide +kernel)

theorem dihedralHom_injective : Function.Injective dihedralHom := by decide +kernel

/-- The bad vertex in row (iii) is the dihedral group of order twenty-four. -/
noncomputable def reflectionVertexEquiv : CubicFiber.group reflectionCharacter ≃* DihedralGroup 12 :=
  (MulEquiv.ofBijective dihedralHom ((Nat.bijective_iff_injective_and_card dihedralHom).mpr
    ⟨dihedralHom_injective, by rw [CubicFiber.card]; norm_num [DihedralGroup.nat_card, DihedralGroup.card, D8]⟩)).symm

abbrev Three := Multiplicative (ZMod 3)
abbrev Bit := Multiplicative (ZMod 2)
abbrev Four := Bit × Bit

def baseWord : Three × Four → D8 × CubicFiber.S3 := fun x =>
  ((DihedralGroup.r 2) ^ x.2.1.toAdd.val * (DihedralGroup.sr 0) ^ x.2.2.toAdd.val,
    cubic ^ x.1.toAdd.val)

def baseHom : Three × Four →* CubicFiber.group rotationCharacter :=
  ({ toFun := baseWord
     map_one' := by decide +kernel
     map_mul' := by decide +kernel } : Three × Four →* D8 × CubicFiber.S3).codRestrict
    (CubicFiber.group rotationCharacter) (by
      change ∀ x, rotationCharacter (baseWord x).1 = Equiv.Perm.sign (baseWord x).2
      decide +kernel)

theorem baseHom_injective : Function.Injective baseHom := by decide +kernel

def extensionParity : CubicFiber.group rotationCharacter →* ℤˣ :=
  rotationCharacter.comp ((MonoidHom.fst _ _).comp (CubicFiber.group rotationCharacter).subtype)

def outer : CubicFiber.group rotationCharacter :=
  ⟨(.sr 1, Equiv.swap 0 1), by
    change rotationCharacter (.sr 1) = Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1)
    decide +kernel⟩

theorem outer_square : outer ^ 2 = 1 := by decide +kernel

theorem outer_parity : extensionParity outer = -1 := by decide +kernel

theorem base_range_eq_kernel : baseHom.range = extensionParity.ker := by
  have cert : ∀ d : D8, ∀ s : CubicFiber.S3,
      rotationCharacter d = Equiv.Perm.sign s →
      ((∃ x : Three × Four, baseWord x = (d,s)) ↔ rotationCharacter d = 1) := by decide +kernel
  ext x
  change (∃ y, baseHom y = x) ↔ rotationCharacter x.val.1 = 1
  rw [← cert x.val.1 x.val.2 x.property]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

/-- The displayed extension has the literal normal base `C₃ × E₄`. -/
noncomputable def baseEquiv : Three × Four ≃* extensionParity.ker :=
  (MonoidHom.ofInjective baseHom_injective).trans (MulEquiv.subgroupCongr base_range_eq_kernel)

/-- The outer involution inverts the cubic and shears the two binary coordinates.
This specifies its action on all twelve elements of the normal base. -/
theorem outer_action : ∀ x : Three × Four,
    outer * baseHom x * outer⁻¹ = baseHom (x.1⁻¹, x.2.1 * x.2.2, x.2.2) := by decide +kernel

end Theory.GroupTheory.RankTwoAmalgam.MixedEight
