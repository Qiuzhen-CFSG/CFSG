module

public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.PGroup

/-!
# Two-group images on a four-element module

The image of a finite two-group acting on an elementary abelian group of
order four has order at most two. The image acts faithfully, so its natural
two-dimensional representation embeds it in GL2(2), of order six. Its order
is a power of two dividing six and therefore is at most two.

This finite-action bound supplies each coordinate in the faithful product
argument identifying the Baumann subgroup in Stellmacher (1.7), journal
page 19, refs/latex/stellmacher-n-group.tex. It requires no ambient faithful
action: faithfulness is automatic after passing to the action image.
-/

namespace Representation
open scoped IsMulCommutative
universe u v

public theorem card_action_image_le_two_of_card_four
    {A : Type u} {U : Type v} [Group A] [Group U] [Finite A] [Finite U]
    [IsElementaryAbelian 2 U] [MulDistribMulAction A U]
    (hA : IsPGroup 2 A) (hU : Nat.card U = 4) :
    Nat.card (MulDistribMulAction.toMulAut A U).range ≤ 2 := by
  classical
  let f : A →* MulAut U := MulDistribMulAction.toMulAut A U
  let X : Subgroup (MulAut U) := f.range
  have hX : IsPGroup 2 X := hA.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let ρ := Representation.ofElementaryAbelianAction (A := X) (G := U) (p := 2)
  have hinj : Function.Injective ρ.asGroupHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro x hx
      have heq : ρ x = 1 := congrArg Units.val (MonoidHom.mem_ker.mp hx)
      apply Subtype.ext
      ext u
      change x • u = u
      apply Additive.ofMul.injective
      have hv := LinearMap.congr_fun heq (Additive.ofMul u)
      simpa only [ρ, Representation.ofElementaryAbelianAction_apply_ofMul,
        Module.End.one_apply] using hv
    · exact bot_le
  have hdim : Module.finrank (ZMod 2) (Additive U) = 2 := by
    have hc : Nat.card (Additive U) = 4 := (Nat.card_congr Additive.toMul).trans hU
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] at hc
    norm_num at hc
    exact Nat.pow_right_injective (by omega : 1 < 2) hc
  let b : Module.Basis (Fin 2) (ZMod 2) (Additive U) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive U) hdim
  let φ : X →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
  have hφinj : Function.Injective φ :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hinj
  have hdiv := Subgroup.card_dvd_of_injective φ hφinj
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  rw [hGL] at hdiv
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra hnle
    have hfourdvd : 4 ∣ 6 := by
      rw [hn] at hdiv
      exact (show 4 ∣ 2 ^ n from by
        exact (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n))).trans hdiv
    omega
  change Nat.card X ≤ 2
  rw [hn]
  exact (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hnle).trans_eq (by norm_num)

end Representation

