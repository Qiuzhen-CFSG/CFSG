module
public import Theory.FieldTheory.CubicTorusDisplacement
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Field automorphisms with at most three multiplicative displacements

The kernel of u ↦ σ(u)u⁻¹ is the unit group of the fixed field. If σ is
nontrivial and that field has r elements, the ambient field has at least
r² elements. An image of order at most three gives r²−1 ≤ 3(r−1), forcing
r = 2 and ambient order four. This uses no assumed involution or Frobenius
coordinates.

Source application: Aschbacher–Smith 5.1.13, the inverted Cartan argument,
printed p.638, refs/quasithin.pdf.
-/

public section
open Subgroup
namespace FiniteField.BinaryTorusInvolution
variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
private theorem displacement_kernel_card (σ : F ≃+* F) :
    Nat.card (displacement σ).ker = Nat.card (FixedBy.subfield F σ) - 1 := by
  let K := FixedBy.subfield F σ
  let f : Kˣ →* Fˣ := Units.map K.subtype.toMonoidHom
  let g : Kˣ →* (displacement σ).ker := f.codRestrict _ (by
    intro u
    change Units.map σ.toMonoidHom (f u) * (f u)⁻¹ = 1
    apply mul_inv_eq_one.mpr
    exact Units.ext (u : K).property)
  have hg : Function.Bijective g := by
    constructor
    · intro u v huv
      apply Units.ext
      apply Subtype.ext
      exact congrArg (fun a : (displacement σ).ker => (a.val : F)) huv
    · intro u
      have hu : σ (u.val : F) = (u.val : F) :=
        congrArg Units.val (mul_inv_eq_one.mp u.property)
      let x : K := ⟨(u.val : F),hu⟩
      have hx : x ≠ 0 := fun hh => Units.ne_zero u.val (congrArg Subtype.val hh)
      exact ⟨Units.mk0 x hx,Subtype.ext (Units.ext rfl)⟩
  exact (Nat.card_congr (MulEquiv.ofBijective g hg).toEquiv).symm.trans (Nat.card_units K)

theorem card_eq_four_of_small_displacement (σ : F ≃+* F) (hne : σ ≠ 1)
    (hc : Nat.card (displacement σ).range ≤ 3) : Nat.card F = 4 := by
  let K := FixedBy.subfield F σ
  let r := Nat.card K
  let m := Module.finrank K F
  have hr : 2 ≤ r := Finite.one_lt_card
  have hm : 2 ≤ m := by
    have hp : 0 < m := Module.finrank_pos
    by_contra hh
    have hm1 : m = 1 := by omega
    have he : Nat.card F = Nat.card K := by
      rw [Module.natCard_eq_pow_finrank (K:=K),show Module.finrank K F = 1 from hm1,pow_one]
    have hs : Function.Surjective K.subtype :=
      (K.subtype_injective.bijective_of_nat_card_le he.le).surjective
    apply hne
    ext x
    obtain ⟨y,rfl⟩ := hs x
    exact y.property
  have hpower : r ^ 2 ≤ Nat.card F := by
    rw [Module.natCard_eq_pow_finrank (K:=K)]
    exact Nat.pow_le_pow_right (by omega : 0 < r) hm
  have he := (displacement σ).ker.card_mul_index
  rw [index_ker,displacement_kernel_card,Nat.card_units] at he
  have hbound : Nat.card F - 1 ≤ (r - 1) * 3 := by
    rw [←he]
    exact Nat.mul_le_mul_left _ hc
  have hF : 1 < Nat.card F := Finite.one_lt_card
  have hr1 : r - 1 + 1 = r := Nat.sub_add_cancel (by omega)
  have hF1 : Nat.card F - 1 + 1 = Nat.card F := Nat.sub_add_cancel (by omega)
  have hr2 : r = 2 := by nlinarith
  rw [hr2] at hpower hbound
  norm_num at hpower hbound
  omega
end FiniteField.BinaryTorusInvolution
