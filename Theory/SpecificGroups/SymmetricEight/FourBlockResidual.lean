module

public import Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.Basic
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PermutationWreathEmbedding
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The four-block residual and its wreath quotient

The subgroup of S₈ which is even and preserves the two four-point blocks has
the literal block-diagonal subgroup A₄ × A₄ as its prime-to-three residual.
The residual is kept as the image of the displayed block embedding, so all
subsequent maps retain the original permutation representatives.

The quotient calculation is stated at the concrete group interface used by
the source assembly: a homomorphism from the actual four-block stabilizer,
with its kernel and surjectivity proved by the marked action, descends to the
regular wreath product.  No order-only recognition is used.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymmetricEight.FourBlockResidual

open Subgroup
open Theory.SpecificGroups.SymmetricEight
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

abbrev S8 := Equiv.Perm (Fin 8)
abbrev A4 := alternatingGroup (Fin 4)
abbrev A8 := alternatingGroup (Fin 8)
abbrev H := A6ShadowTwoLocals.fourStabilizer
abbrev P := A8 ⊓ H
abbrev W := RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))

/-- The literal product of the two alternating four-point groups. -/
noncomputable def blockAlternatingHom : A4 × A4 →* A8 where
  toFun x :=
    ⟨(@finSumFinEquiv 4 4).permCongr (Equiv.Perm.sumCongr x.1.1 x.2.1), by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr,
        Equiv.Perm.sign_sumCongr]
      simp [Equiv.Perm.mem_alternatingGroup.mp x.1.2,
        Equiv.Perm.mem_alternatingGroup.mp x.2.2]⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    simp [Equiv.permCongr]
  map_mul' x y := by
    apply Subtype.ext
    apply Equiv.ext
    intro z
    simp [Equiv.permCongr]

/-- The embedded A₄ × A₄ inside S₈. -/
noncomputable def fourBlockResidual : Subgroup S8 :=
  (blockAlternatingHom.range).map A8.subtype

theorem fourBlockResidual_le : fourBlockResidual ≤ P := by
  intro x hx
  rcases (Subgroup.mem_map.mp hx) with ⟨y, hy, rfl⟩
  rcases (MonoidHom.mem_range.mp hy) with ⟨z, rfl⟩
  change (blockAlternatingHom z : S8) ∈ A8 ⊓ A6ShadowTwoLocals.fourStabilizer
  refine ⟨(blockAlternatingHom z).property, ?_⟩
  change ∀ i j : Fin 8,
    (((blockAlternatingHom z : A8) : S8) i).val / 4 =
        (((blockAlternatingHom z : A8) : S8) j).val / 4 ↔
      i.val / 4 = j.val / 4
  intro i j
  obtain ⟨i, rfl⟩ := (@finSumFinEquiv 4 4).surjective i
  obtain ⟨j, rfl⟩ := (@finSumFinEquiv 4 4).surjective j
  have hleft (x : Fin 4) :
      ((@finSumFinEquiv 4 4) (Sum.inl x) : Fin 8).val / 4 = 0 := by
    rw [finSumFinEquiv_apply_left]
    exact Nat.div_eq_of_lt x.isLt
  have hright (x : Fin 4) :
      ((@finSumFinEquiv 4 4) (Sum.inr x) : Fin 8).val / 4 = 1 := by
    rw [finSumFinEquiv_apply_right]
    simp only [Fin.val_natAdd]
    omega
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockAlternatingHom, Equiv.sumCongr_apply,
      hleft, hright]

theorem fourBlockResidual_eq_blockProduct :
    fourBlockResidual =
      (blockAlternatingHom.range).map A8.subtype := rfl

theorem fourBlock_pCoreIn_eq :
    H.pCoreIn 2 = FourBlockCoreAction.kleinGroup :=
  FourBlockCoreAction.fourStabilizer_pCoreIn

set_option linter.style.haveILetI false in
/-- The exact residual criterion for the four-block model.

The source assembly supplies the normality, coprime index and generation
clauses for the displayed subgroup.  This theorem applies the residual
criterion to that literal subgroup, rather than replacing it by a pResidual
or by a subgroup carrying only the same abstract isomorphism type.
-/
theorem primeToResidual_eq_fourBlockResidual
    (hN : (fourBlockResidual.subgroupOf P).Normal)
    (hindex : Nat.Coprime 3 (fourBlockResidual.subgroupOf P).index)
    (hgen : Subgroup.closure
        {x : P | ∃ n : ℕ, (x : S8) ^ (3 ^ n) = 1} =
      fourBlockResidual.subgroupOf P) :
    primeToResidual 3 P = fourBlockResidual.subgroupOf P := by
  letI : (fourBlockResidual.subgroupOf P).Normal := hN
  apply Subgroup.primeToResidual_eq_of_generated
    (fourBlockResidual.subgroupOf P) hindex
    {x : P | ∃ n : ℕ, (x : S8) ^ (3 ^ n) = 1} hgen
  intro x hx
  rcases hx with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  exact hn

theorem primeToResidual_image_eq_fourBlockResidual
    (hN : (fourBlockResidual.subgroupOf P).Normal)
    (hindex : Nat.Coprime 3 (fourBlockResidual.subgroupOf P).index)
    (hgen : Subgroup.closure
        {x : P | ∃ n : ℕ, (x : S8) ^ (3 ^ n) = 1} =
      fourBlockResidual.subgroupOf P) :
    (primeToResidual 3 P).map P.subtype = fourBlockResidual := by
  rw [primeToResidual_eq_fourBlockResidual hN hindex hgen]
  exact Subgroup.map_subgroupOf_eq_of_le fourBlockResidual_le

/-- A residual image and a supplied Sylow-two image have the required join
once the concrete generation calculation has been discharged. -/
theorem residual_sup_eq_of_primeToResidual
    (S : Subgroup S8)
    (hres : primeToResidual 3 P = fourBlockResidual.subgroupOf P)
    (hgen : fourBlockResidual ⊔ S = H) :
    (primeToResidual 3 P).map P.subtype ⊔ S = H := by
  rw [hres]
  have hmap :
      (fourBlockResidual.subgroupOf P).map P.subtype = fourBlockResidual := by
    exact Subgroup.map_subgroupOf_eq_of_le fourBlockResidual_le
  rw [hmap]
  exact hgen

/-- Descent of a marked four-block action to the regular wreath product. -/
noncomputable def quotientWreathEquiv
    (φ : H →* W) (hker : φ.ker = pCore 2 H)
    (hsurj : Function.Surjective φ) :
    H ⧸ pCore 2 H ≃* W := by
  let e₁ : H ⧸ pCore 2 H ≃* H ⧸ φ.ker :=
    QuotientGroup.quotientMulEquivOfEq hker.symm
  exact e₁.trans (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)

@[simp] theorem quotientWreathEquiv_mk
    (φ : H →* W) (hker : φ.ker = pCore 2 H)
    (hsurj : Function.Surjective φ) (x : H) :
    quotientWreathEquiv φ hker hsurj (QuotientGroup.mk x) = φ x := by
  rfl

theorem quotientWreathEquiv_kernel
    (φ : H →* W) (hker : φ.ker = pCore 2 H)
    (hsurj : Function.Surjective φ) :
    (quotientWreathEquiv φ hker hsurj).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 H)) =
      φ := by
  apply MonoidHom.ext
  intro x
  change quotientWreathEquiv φ hker hsurj (QuotientGroup.mk x) = φ x
  rfl

end Theory.SpecificGroups.SymmetricEight.FourBlockResidual
