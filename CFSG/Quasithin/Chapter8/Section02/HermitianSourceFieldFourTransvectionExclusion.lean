module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddLinearTwo.SmallImage
public import Theory.Representation.PSL2ThirtyOneTransvection

/-!
# Excluding the actual PSL₂(31) residual using its marked transvection

The minimal-parabolic theorem places the nontrivial elementary marker in
its normal PSL₂(31) subgroup. The given embedding of the faithful action
quotient contains that whole subgroup, so its torus and conjugating elements
lift through this embedding. The marked transvection then contradicts the
order-fifteen torus calculation on the same action.

The original chosen-module application supplies the literal quotient of
O²(H)V, its faithful F₄ multiplicity action, and its original V-involution.
No extension to a faithful action of all of H/O₂(H) is required.
Source: Aschbacher–Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterB ChapterE
variable {X : Type*} [Group X] [Finite X]
set_option backward.isDefEq.respectTransparency false

/-- A faithful four-element-field action of a subgroup containing the residual
cannot realize the original parabolic marker as a transvection in the PSL₂(31) row. -/
theorem corefree_parabolic_no_thirty_one_transvection
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (K : Subgroup X) [K.Normal] (hgen : K ⊔ (S : Subgroup X)=⊤)
    (hO : pCore 2 X=⊥)
    (W : Subgroup X) [IsElementaryAbelian 2 W]
    (hWS : W ≤ S) (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    {A k Y : Type*} [Group A] [Field k] [Finite k] [CharP k 2]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (hk : Nat.card k=4)
    (j : A →* X) (hj : Function.Injective j) (hKj : K ≤ j.range)
    (μ : A →* (Y ≃ₗ[k] Y)) (hμ : Function.Injective μ)
    (a : A) (haW : j a ∈ W) (hane : j a ≠ 1)
    (hr : Module.finrank k (LinearMap.range ((μ a).toLinearMap-1)) ≤ 1)
    (hm : ClassicalGroup.IsPSL K 2 31) : False := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  have hWM : W ≤ (minimalParabolicMax S hP).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W)
      (hWS.trans (minimalParabolicMax_spec S hP).2) hMW
  have hTW : (S : Subgroup X) ≤ normalizer (W : Set X) :=
    (minimalParabolicMax_spec S hP).2.trans hMW
  have hWne : W ≠ ⊥ := by
    intro hh
    exact hane (by simpa only [hh,mem_bot] using haW)
  obtain ⟨hW,t,ht,htW⟩ := Witnesses.OddLinearTwo.corefree_odd_image_involution
    S hP K hgen hO (p := 31) (n := 1) (by decide) (by decide) (Or.inl rfl)
    (by simpa only [pow_one] using hcard) (by rw [hcard]; decide)
    e W hWS hTW hWM hWne
  have htne : (t : X) ≠ 1 := by
    intro hh
    have ht1 : t=1 := Subtype.ext hh
    rw [ht1,orderOf_one] at ht
    omega
  have hta : (t : X)=j a := by
    obtain ⟨u,_,hu⟩ := (Nat.card_eq_two_iff' (1 : W)).mp hW
    have ht1 : (⟨t,htW⟩ : W) ≠ 1 := fun he => htne (congrArg Subtype.val he)
    have ha1 : (⟨j a,haW⟩ : W) ≠ 1 := fun he => hane (congrArg Subtype.val he)
    exact congrArg Subtype.val ((hu _ ht1).trans (hu _ ha1).symm)
  let ej : A ≃* j.range := MulEquiv.ofBijective j.rangeRestrict
    ⟨fun x y h => hj (congrArg Subtype.val h),j.rangeRestrict_surjective⟩
  let ι : K →* A := ej.symm.toMonoidHom.comp (inclusion hKj)
  have hι (x : K) : j (ι x)=(x : X) := by
    exact congrArg Subtype.val (ej.apply_symm_apply (inclusion hKj x))
  have hiι : Function.Injective ι := by
    intro x y h
    apply Subtype.ext
    simpa only [hι] using congrArg j h
  have hιt : ι t=a := hj ((hι t).trans hta)
  exact Representation.no_faithful_thirty_one_field_four_transvection hcard hk e
    (μ.comp ι) (hμ.comp hiι) t ht ((congrArg (fun z : A =>
      Module.finrank k (LinearMap.range ((μ z).toLinearMap-1)) ≤ 1) hιt).mpr hr)

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
