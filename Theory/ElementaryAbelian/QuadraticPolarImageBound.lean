module

public import Theory.ElementaryAbelian.AnisotropicQuadratic
public import Mathlib.GroupTheory.Index

/-!
# Anisotropic quadratic maps with restricted polar image

If the polar map of an anisotropic binary quadratic map `V → W` lands in
`R ≤ W`, then `|V| ≤ |W| |R|`. Modulo `R`, the square map is a homomorphism.
Its kernel carries an anisotropic quadratic map to `R`, so has order at most
`|R|²`; its index is at most `|W/R|`.

This refines the Chevalley–Warning bound in `AnisotropicQuadratic` using only
its application to the kernel. It supplies the square-class counting argument
motivated by MacWilliams, *On 2-groups with no normal abelian subgroups of rank
3, and their occurrence as Sylow 2-subgroups of finite simple groups*,
Trans. Amer. Math. Soc. 150 (1970), §3, pp. 366–374.
-/

open Subgroup
open scoped IsMulCommutative
namespace IsElementaryAbelian
/-- A restricted polar image improves the anisotropic quadratic counting bound
from `|W|²` to `|W| |R|`. -/
public theorem card_le_card_mul_card_of_polar_mem
    {V W : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (R : Subgroup W)
    (square : V → W) (polar : V → V → W)
    (hone : square 1 = 1)
    (hquadratic : ∀ x y, square (x * y) = square x * square y * polar x y)
    (hbilinear : ∀ x y z, polar (x * y) z = polar x z * polar y z)
    (hanisotropic : ∀ x, square x = 1 → x = 1)
    (hpolar : ∀ x y, polar x y ∈ R) :
    Nat.card V ≤ Nat.card W * Nat.card R := by
  let q := QuotientGroup.mk' R
  let f : V →* W ⧸ R := {
    toFun := fun x => q (square x)
    map_one' := by simp [hone]
    map_mul' := by
      intro x y
      simp only [hquadratic, map_mul]
      have hp : q (polar x y) = 1 := (QuotientGroup.eq_one_iff _).mpr (hpolar x y)
      rw [hp, mul_one] }
  let K := f.ker
  let : IsElementaryAbelian 2 K := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) (x : V)) }
  let : IsElementaryAbelian 2 R := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W) (x : W)) }
  have hmem (x : K) : square (x : V) ∈ R :=
    (QuotientGroup.eq_one_iff _).mp x.property
  let squareK (x : K) : R := ⟨square x, hmem x⟩
  let polarK (x y : K) : R := ⟨polar x y, hpolar x y⟩
  have hK : Nat.card K ≤ (Nat.card R)^2 :=
    card_le_sq_of_anisotropic_quadratic squareK polarK
      (Subtype.ext hone) (fun x y => Subtype.ext (hquadratic x y))
      (fun x y z => Subtype.ext (hbilinear x y z))
      (fun x hx => Subtype.ext (hanisotropic x (congrArg Subtype.val hx)))
  have hindex : K.index ≤ R.index := by
    rw [show K = f.ker from rfl, index_ker, index_eq_card]
    exact Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
  calc
    Nat.card V = Nat.card K * K.index := K.card_mul_index.symm
    _ ≤ (Nat.card R)^2 * R.index := Nat.mul_le_mul hK hindex
    _ = Nat.card W * Nat.card R := by rw [← R.card_mul_index]; ring
end IsElementaryAbelian
