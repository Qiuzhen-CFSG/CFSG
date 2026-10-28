module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.NormNum

/-!
# Sylow two-subgroups of the concrete `SL₂(2)` wreath product

Every Sylow two-subgroup of `SL₂(2) ≀ᵣ C₂` is isomorphic to `DihedralGroup 4`.
The isomorphism has the actual Sylow subgroup subtype as its domain, so it can
transport subgroup and centralizer calculations without replacing the ambient
group by an abstract model.

The upper-unitriangular transvection supplies an involution in `SL₂(2)`.
Placing it in one base coordinate and composing with the factor swap gives a
rotation of order four; the pure swap is a reflection. The resulting map from
the eight-element dihedral group is multiplicative and injective, as checked
by kernel reduction over its finite domain. The same finite calculation gives
`|SL₂(2)| = 6`, hence the wreath product has order `6² · 2 = 72`. Its embedded
dihedral subgroup therefore has the full two-part of the ambient order.
`Sylow.ofCard` makes it a Sylow subgroup and `Sylow.equiv` transports the model
to any specified Sylow subgroup. The concrete embedding is exposed as
`wreathTwoDihedralHom` for kernel-checked ambient centralizer calculations.
Its standard Sylow is available through the opaque value `wreathTwoSylow`
and the range specification `wreathTwoSylow_coe`; clients need not depend
on the implementation of the Sylow certificate.

This independent concrete calculation supplies the Sylow model used in the
centralizer step of Stellmacher (9.1), relation (9), journal p.47. It uses only
Mathlib's wreath-product, dihedral-group, and Sylow APIs.
-/

private abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev Wreath := RegularWreathProduct SL2 C2

private instance : DecidableEq Wreath :=
  fun first second => decidable_of_iff
    (first.left = second.left ∧ first.right = second.right)
    (RegularWreathProduct.ext_iff.symm)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The standard dihedral eight inside the concrete SL₂(2) wreath product. -/
@[expose] public def wreathTwoDihedralHom : DihedralGroup 4 →*
    RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (Multiplicative (ZMod 2)) :=
  let transvection : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
    ⟨!![1, 1; 0, 1], by decide⟩
  let rotation : RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (Multiplicative (ZMod 2)) :=
    ⟨fun coordinate => if coordinate = 1 then transvection else 1, Multiplicative.ofAdd 1⟩
  let reflection : RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (Multiplicative (ZMod 2)) := ⟨1, Multiplicative.ofAdd 1⟩
  let modelMap : DihedralGroup 4 →
      RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
        (Multiplicative (ZMod 2)) := fun x => match x with
    | .r exponent => rotation ^ exponent.val
    | .sr exponent => reflection * rotation ^ exponent.val
  { toFun := modelMap
    map_one' := by decide +kernel
    map_mul' := by decide +kernel }

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
public theorem wreathTwoDihedralHom_injective : Function.Injective wreathTwoDihedralHom := by
  decide +kernel

private theorem sl2_card : Nat.card SL2 = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem wreath_card : Nat.card Wreath = 72 := by
  rw [RegularWreathProduct.card, sl2_card]
  norm_num [Nat.card_eq_fintype_card]

/-- The standard Sylow two-subgroup supplied by the concrete dihedral model. -/
public noncomputable def wreathTwoSylow : Sylow 2 (RegularWreathProduct
    (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))) := by
  let modelEquiv := MonoidHom.ofInjective wreathTwoDihedralHom_injective
  have image_card : Nat.card wreathTwoDihedralHom.range = 8 := by
    rw [← Nat.card_congr modelEquiv.toEquiv, DihedralGroup.nat_card]
  have image_sylow_card :
      Nat.card wreathTwoDihedralHom.range = 2 ^ (Nat.card Wreath).factorization 2 := by
    rw [image_card, wreath_card]
    decide +kernel
  exact Sylow.ofCard wreathTwoDihedralHom.range image_sylow_card

/-- The standard Sylow is exactly the range of the exposed dihedral embedding. -/
public theorem wreathTwoSylow_coe :
    (wreathTwoSylow : Subgroup (RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)))) =
      wreathTwoDihedralHom.range := by rfl

public theorem wreath_two_sylow_mulEquiv_dihedral_four
    (P : Sylow 2 (RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)))) :
    Nonempty (P ≃* DihedralGroup 4) := by
  let modelEquiv := MonoidHom.ofInjective wreathTwoDihedralHom_injective
  have hmodel : P ≃* wreathTwoDihedralHom.range :=
    (P.equiv wreathTwoSylow).trans (MulEquiv.subgroupCongr wreathTwoSylow_coe)
  exact ⟨hmodel.trans modelEquiv.symm⟩
