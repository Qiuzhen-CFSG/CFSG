module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupTheory.PResidual.PrimeTo
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.FieldTheory.Finiteness

/-!
# Recognition of the small binary flag quotient

A binary representation on at most four vectors with nontrivial two-residual
action has dimension two: the zero space and the binary line have trivial
linear automorphism groups. Transporting the actual action to this plane
then gives a homomorphism to SL₂(2). Its image has order dividing six.
Nontrivial two-residual action excludes a two-group image, and a full
prime-to-two residual excludes a nontrivial odd-order image. Thus the
homomorphism is onto, with the same coordinates intertwining the action.

This is the representation-theoretic recognition step for the binary case
of Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), claim (1) in the proof of (4.6.8), printed p.905. The geometric
bound on the source quotient is an explicit premise here; its proof and
the assembly of the source claim belong to the natural-section consumer.
-/

open Subgroup
open BinaryLinear.OuterCyclic

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne

private theorem binary_scalar_aut_trivial (f : ZMod 2 ≃ₗ[ZMod 2] ZMod 2) (x : ZMod 2) :
    f x = x := by
  by_cases hx : x = 0
  · simp [hx]
  have hf : f x ≠ 0 := by
    intro hzero
    apply hx
    apply f.injective
    simpa only [map_zero] using hzero
  have h : ∀ y : ZMod 2, y ≠ 0 → y = 1 := by decide
  rw [h _ hf, h _ hx]

private theorem finrank_eq_two_of_residual_movement {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) A W)
    (hm : ¬ pResidual 2 A ≤ ρ.ker) (hc : Nat.card W ≤ 4) :
    Module.finrank (ZMod 2) W = 2 := by
  have hd : Module.finrank (ZMod 2) W ≤ 2 := by
    have hp : 2 ^ Module.finrank (ZMod 2) W ≤ 2 ^ 2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod] at hc
      exact hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
  by_contra hne
  have hsmall : Module.finrank (ZMod 2) W = 0 ∨ Module.finrank (ZMod 2) W = 1 := by omega
  apply hm
  rcases hsmall with hz | ho
  · let : Subsingleton W := Module.finrank_zero_iff.mp hz
    intro a _
    exact Subsingleton.elim (ρ a) 1
  · let e : W ≃ₗ[ZMod 2] ZMod 2 := LinearEquiv.ofFinrankEq _ _ (by simpa using ho)
    let σ : Representation (ZMod 2) A (ZMod 2) := e.conjRingEquiv.toMonoidHom.comp ρ
    intro a _
    change ρ a = 1
    apply LinearMap.ext
    intro w
    apply e.injective
    let f := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (ZMod 2)
      (σ.asGroupHom a)
    have hf := binary_scalar_aut_trivial f (e w)
    change e (ρ a (e.symm (e w))) = e w at hf
    simpa only [LinearEquiv.symm_apply_apply, Module.End.one_apply] using hf

private theorem surjective_of_residuals_card_six {A D : Type*} [Group A] [Group D] [Finite D]
    (f : A →* D) (hD : Nat.card D = 6)
    (hprime : primeToResidual 2 A = ⊤) (hres : ¬ pResidual 2 A ≤ f.ker) :
    Function.Surjective f := by
  have hdiv : Nat.card f.range ∣ 6 := hD ▸ f.range.card_subgroup_dvd_card
  have htwo : ¬ Nat.card f.range ∣ 2 := by
    intro h
    apply hres
    have hp : IsPGroup 2 f.range := IsPGroup.of_card_dvd_pow (n := 1) (by simpa using h)
    exact sInf_le ⟨inferInstance, hp.of_equiv (QuotientGroup.quotientKerEquivRange f).symm⟩
  have hodd : ¬ Nat.Coprime 2 (Nat.card f.range) := by
    intro h
    have hk := primeToResidual_le_ker f.rangeRestrict h
    rw [hprime] at hk
    apply hres
    intro a _
    have ha := hk (mem_top a)
    exact congrArg Subtype.val ha
  have hr : Nat.card f.range = 6 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hdiv
    interval_cases Nat.card f.range <;> norm_num at *
  apply MonoidHom.range_eq_top.mp
  apply f.range.eq_top_of_card_eq
  exact hr.trans hD.symm

/-- A binary representation of order at most four is the actual natural
SL₂(2) representation when its two-residual moves the space and its full
actor is the prime-to-two residual. Both the onto actor map and the linear
coordinates are constructed from these premises. -/
public theorem exists_natural_sl2_of_residuals_card_le_four {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) A W)
    (hprime : primeToResidual 2 A = ⊤)
    (hres : ¬ pResidual 2 A ≤ ρ.ker) (hcard : Nat.card W ≤ 4) :
    ∃ π : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      Function.Surjective π ∧ ∃ e : W ≃ₗ[ZMod 2] (Fin 2 → ZMod 2),
        ∀ a w, e (ρ a w) = (π a).val.mulVec (e w) := by
  let e : W ≃ₗ[ZMod 2] Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using finrank_eq_two_of_residual_movement ρ hres hcard)
  let σ : Representation (ZMod 2) A (Space 2) := e.conjRingEquiv.toMonoidHom.comp ρ
  let θ : A →* LinearGroup 2 :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space 2)).toMonoidHom.comp
      σ.asGroupHom
  let π : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
    (slEquivLinear 2).symm.toMonoidHom.comp θ
  have he (a : A) (w : W) : e (ρ a w) = (π a).val.mulVec (e w) := by
    change e (ρ a w) = slEquivLinear 2 ((slEquivLinear 2).symm (θ a)) (e w)
    rw [MulEquiv.apply_symm_apply]
    change e (ρ a w) = e (ρ a (e.symm (e w)))
    rw [LinearEquiv.symm_apply_apply]
  have hπres : ¬ pResidual 2 A ≤ π.ker := by
    intro h
    apply hres
    intro a ha
    change ρ a = 1
    apply LinearMap.ext
    intro w
    apply e.injective
    have hpa : π a = 1 := h ha
    simpa [hpa] using he a w
  have hmodel : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    obtain ⟨f⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    rw [Nat.card_congr f.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  exact ⟨π, surjective_of_residuals_card_six π hmodel hprime hπres, e, he⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
