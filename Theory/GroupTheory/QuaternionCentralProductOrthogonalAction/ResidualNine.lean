module

public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.WreathOuter
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.AutomorphismLocalDisplacement
public import Theory.ElementaryAbelian.ExtraspecialAbelianBound
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.ElementaryStabilizerSign
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.ResidualFourSquare
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Quaternion central products and the elementary order-nine residual

An action on a quaternion central product of order 32 embeds its central-
quotient image in O₄⁺(2). A Sylow two-subgroup preserving an elementary eight
forces the image into the S₃ × S₃ kernel of the factor sign. Its two-residual
is elementary of order dividing nine. When the two-core is trivial and the
image has order greater than six, the residual has order nine.

The centralizer bound excludes residual orders one and three. Automorphisms
fixing an elementary eight pointwise square to one; this supplies the actual
centralizer consumer in the Chapter 14 swapping branch.

Source: Aschbacher–Smith, 14.4.4(1)–(3), printed p.1007.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Subgroup.QuaternionCentralProductData
variable {Q H : Type*} [Group Q] [Finite Q] [Group H] [Finite H]

omit [Finite H] in
theorem wreath_quotient_embedding (d : QuaternionCentralProductData Q)
    (α : H →* MulAut Q) (N : Subgroup H) [N.Normal]
    (hk : ((quotientAut (center Q)).comp α).ker = N) :
    ∃ f : (H ⧸ N) →* BinaryFourPlus.Wreath, Function.Injective f ∧
      ∀ x : H, f (QuotientGroup.mk' N x) = d.quotientWreathAction (α x) := by
  let f := d.quotientWreathAction.comp α
  have hf : f.ker = N := by
    rw [← hk]
    ext x
    change d.quotientWreathAction (α x) = 1 ↔ quotientAut (center Q) (α x) = 1
    rw [← MonoidHom.mem_ker, d.quotientWreathAction_ker, d.quotientAut_eq_one_iff_inner]
  let e := QuotientGroup.quotientMulEquivOfEq hf.symm
  exact ⟨(QuotientGroup.kerLift f).comp e.toMonoidHom,
    (QuotientGroup.kerLift_injective f).comp e.injective, fun _ => rfl⟩

theorem square_quotient_embedding (d : QuaternionCentralProductData Q)
    (α : H →* MulAut Q) (N : Subgroup H) [N.Normal]
    (hk : ((quotientAut (center Q)).comp α).ker = N)
    (T : Sylow 2 H) (E : Subgroup Q) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (hTE : ∀ t ∈ (T : Subgroup H), ∀ v ∈ E, α t v ∈ E) :
    ∃ f : (H ⧸ N) →* BinaryFourPlus.factorSign.ker, Function.Injective f ∧
      ∀ x : H, (f (QuotientGroup.mk' N x) : BinaryFourPlus.Wreath) =
        d.quotientWreathAction (α x) := by
  let χ := BinaryFourPlus.factorSign.comp (d.quotientWreathAction.comp α)
  have ht : (T : Subgroup H) ≤ χ.ker := by
    intro t ht
    exact d.quotientWreathAction_factorSign_one_of_elementary_eight E hE (α t) (hTE t ht)
  have hr : pResidual 2 H ≤ χ.ker := pResidual_le_ker_of_isPGroup 2 χ
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_eq_fintype_card]; decide))
  have hall : χ.ker = ⊤ := top_unique (pResidual_sup_sylow_eq_top T ▸ sup_le hr ht)
  obtain ⟨f, hf, he⟩ := d.wreath_quotient_embedding α N hk
  have hsign (x : H ⧸ N) : f x ∈ BinaryFourPlus.factorSign.ker := by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [he]
    exact (show y ∈ χ.ker from hall.symm ▸ mem_top y)
  exact ⟨f.codRestrict _ hsign, fun x y h => hf (congrArg Subtype.val h), he⟩

theorem square_eq_one_of_fixes_eight (d : QuaternionCentralProductData Q)
    (E : Subgroup Q) [IsElementaryAbelian 2 E] (hc : Nat.card E = 8)
    (α : MulAut Q) (hfix : ∀ x ∈ E, α x = x) : α ^ 2 = 1 := by
  let : IsExtraspecial 2 Q := d.extraspecial
  obtain ⟨hEn,hZE⟩ := IsExtraspecial.elementary_eight_normal_and_center_le_of_card_thirty_two
    d.card E hc
  let : E.Normal := hEn
  have hself : centralizer (E : Set Q) ≤ E :=
    (extraspecial_two_centralizer_eq_of_card_sq E hZE (by rw [hc,d.card]; decide)).le
  apply MulEquiv.ext
  intro x
  exact MulAut.square_apply_eq_on_normalizer E hself α hfix
    (by rw [E.normalizer_eq_top]; exact mem_top x)

end Subgroup.QuaternionCentralProductData

namespace BinaryFourPlus
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem residual_elementary_bound_of_embedding
    (f : H →* Wreath) (hf : Function.Injective f) :
    IsElementaryAbelian 3 (pResidual 2 H) ∧ Nat.card (pResidual 2 H) ∣ 9 := by
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let e : Wreath ≃* WreathTwoResidual.Actor :=
    RegularWreathProduct.congr eSL.symm (MulEquiv.refl _)
  let g := e.toMonoidHom.comp f
  let R := pResidual 2 H
  let S := pResidual 2 WreathTwoResidual.Actor
  let j : R →* S := (g.comp R.subtype).codRestrict S
    (fun x => map_pResidual_le 2 g (mem_map_of_mem g x.property))
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (hf (e.injective (congrArg Subtype.val he)))
  obtain ⟨r⟩ := WreathTwoResidual.residual_equiv_elementaryNine
  let h := r.toMonoidHom.comp j
  have hh : Function.Injective h := r.injective.comp hj
  let : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      change (3 : ℕ) • x.toAdd = 0
      ext i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      change (3 : ZMod 3) * x.toAdd i = 0
      rw [show (3 : ZMod 3) = 0 by decide, zero_mul]) }
  refine ⟨IsElementaryAbelian.of_injective h hh, ?_⟩
  have hd := h.range.card_subgroup_dvd_card
  rw [Nat.card_congr (MonoidHom.ofInjective hh).toEquiv.symm] at hd
  simpa [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    Fintype.card_fun, Fintype.card_fin, ZMod.card, R] using hd

theorem residual_nine_of_embedding (f : H →* Wreath) (hf : Function.Injective f)
    (hcore : pCore 2 H = ⊥) (hlarge : 6 < Nat.card H) :
    IsElementaryAbelian 3 (pResidual 2 H) ∧ Nat.card (pResidual 2 H) = 9 := by
  obtain ⟨he, hd⟩ := residual_elementary_bound_of_embedding f hf
  refine ⟨he, ?_⟩
  have hcases : Nat.card (pResidual 2 H) = 1 ∨ Nat.card (pResidual 2 H) = 3 ∨
      Nat.card (pResidual 2 H) = 9 := by
    have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : 9 ≠ 0)⟩
    have hv : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hv] at hm
    simpa using hm
  rcases hcases with h1 | h3 | h9
  · have hb := Subgroup.card_eq_one.mp h1
    have hc := centralizer_pResidual_le_of_pCore_eq_bot hcore
    have ht : (⊤ : Subgroup H) = ⊥ := by
      apply bot_unique
      intro x _
      exact hb ▸ hc (by rw [hb]; intro y hy; have hy1 : y = 1 := hy; simp [hy1])
    have hh := congrArg (fun S : Subgroup H => Nat.card S) ht
    simp only [card_top, card_bot] at hh
    omega
  · let R := pResidual 2 H
    let : IsCyclic R := isCyclic_of_prime_card h3
    let a : H →* MulAut R := MulAut.conjNormal
    have hk : a.ker ≤ R := by
      rw [MulAut.conjNormal_ker_eq_centralizer]
      exact centralizer_pResidual_le_of_pCore_eq_bot hcore
    have hc : Nat.card a.ker ≤ 3 := (card_le_of_le hk).trans_eq h3
    have hA : Nat.card (MulAut R) = 2 := by
      rw [IsCyclic.card_mulAut, h3, Nat.totient_prime Nat.prime_three]
    have hi : Nat.card a.range ≤ 2 := (Nat.card_le_card_of_injective a.range.subtype Subtype.val_injective).trans_eq hA
    have hmul := a.ker.card_mul_index
    rw [index_ker] at hmul
    have hh := Nat.mul_le_mul hc hi
    rw [hmul] at hh
    omega
  · exact h9

omit [Finite H] in
theorem sixth_pow_eq_one_of_square_embedding
    (f : H →* factorSign.ker) (hf : Function.Injective f) (x : H) : x ^ 6 = 1 := by
  apply hf
  apply factorSignEquiv.injective
  rw [map_pow, map_one, map_pow, map_one]
  have hp (p : Equiv.Perm (Fin 3)) : p ^ 6 = 1 := by
    have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    simpa only [hc] using pow_card_eq_one' (x := p)
  exact Prod.ext (hp _) (hp _)

end BinaryFourPlus
