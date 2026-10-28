module


public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.Criteria

/-!
# Mixed one-dimensional covers of the doubled binary natural module

A one-dimensional-kernel cover of two copies of the binary natural module is
identified with the mixed universal cover. Every cover is first obtained as a
quotient of `U × U`; its kernel line lies in the two-dimensional kernel of the
universal doubled projection. Over `ZMod 2`, the three nonzero lines are
carried to the second coordinate line by the swap and shear automorphisms.
The resulting equal-kernel quotient maps give the required equivariant
equivalence with `U × V`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Remark I.1.5
and Lemma I.1.6(4), printed p.408 (PDF p.419).
-/

@[expose] public section

open Representation Representation.OneCohomology Module
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels

namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels

private noncomputable def mixedLift : doubled.IntertwiningMap mixed :=
  (IntertwiningMap.fst (ZMod 2) cover cover).prod
    (projection.comp (IntertwiningMap.snd (ZMod 2) cover cover))

private lemma mixedLift_surjective : Function.Surjective mixedLift := by
  intro x
  obtain ⟨v, hv⟩ := projection_isCover.1 x.2
  refine ⟨(x.1, v), ?_⟩
  exact Prod.ext rfl hv

private lemma mixedLift_kernel_finrank : Module.finrank (ZMod 2) mixedLift.toLinearMap.ker = 1 := by
  have h := mixedLift.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr mixedLift_surjective, finrank_top,
    finrank_doubled, finrank_mixed] at h
  omega

private noncomputable def swapEquiv : doubled.Equiv doubled :=
  Representation.Equiv.mk (LinearEquiv.prodComm (ZMod 2) U U) (by
    intro g
    apply LinearMap.ext
    intro x
    rfl)

private noncomputable def shearLinear : (U × U) ≃ₗ[ZMod 2] (U × U) :=
  LinearEquiv.ofBijective
    ((LinearMap.fst (ZMod 2) U U + LinearMap.snd (ZMod 2) U U).prod
      (LinearMap.snd (ZMod 2) U U)) (by
        constructor
        · intro x y h
          change (x.1 + x.2, x.2) = (y.1 + y.2, y.2) at h
          apply Prod.ext
          · have h₁ := congrArg Prod.fst h
            have h₂ := congrArg Prod.snd h
            rw [h₂] at h₁
            exact add_right_cancel h₁
          · exact (Prod.ext_iff.mp h).2
        · intro y
          refine ⟨(y.1 + y.2, y.2), ?_⟩
          apply Prod.ext
          · simp [add_assoc, ZModModule.add_self]
          · rfl)

private noncomputable def shearEquiv : doubled.Equiv doubled :=
  Representation.Equiv.mk shearLinear (by
    intro g
    apply LinearMap.ext
    intro x
    change (cover g x.1 + cover g x.2, cover g x.2) =
      (cover g (x.1 + x.2), cover g x.2)
    simp [map_add])

private lemma doubledProjection_mem_ker_iff (x : U × U) :
    x ∈ doubledProjection.toLinearMap.ker ↔
      x.1 ∈ projection.toLinearMap.ker ∧ x.2 ∈ projection.toLinearMap.ker := by
  constructor
  · intro hx
    have hz := congrArg pairEquiv (show doubledProjection x = 0 from hx)
    change pairEquiv (pairEquiv.symm (projection x.1, projection x.2)) = pairEquiv 0 at hz
    rw [pairEquiv.apply_symm_apply, map_zero] at hz
    exact ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩
  · rintro ⟨hx, hy⟩
    apply pairEquiv.injective
    change pairEquiv (pairEquiv.symm (projection x.1, projection x.2)) = pairEquiv 0
    rw [pairEquiv.apply_symm_apply, map_zero]
    exact Prod.ext hx hy

private theorem equiv_of_surj_same_ker {α β γ : Type*}
    [AddCommGroup α] [AddCommGroup β] [AddCommGroup γ]
    [Module (ZMod 2) α] [Module (ZMod 2) β] [Module (ZMod 2) γ]
    {ρ : Representation (ZMod 2) MatrixGroup α}
    {σ : Representation (ZMod 2) MatrixGroup β}
    {τ : Representation (ZMod 2) MatrixGroup γ}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (p : ρ.IntertwiningMap τ) (hp : Function.Surjective p)
    (hker : f.toLinearMap.ker = p.toLinearMap.ker) : Nonempty (σ.Equiv τ) := by
  let ef := f.toLinearMap.quotKerEquivOfSurjective hf
  let ep := p.toLinearMap.quotKerEquivOfSurjective hp
  let e := ef.symm.trans ((Submodule.quotEquivOfEq _ _ hker).trans ep)
  have he (x : α) : e (f x) = p x := by
    change ep (Submodule.quotEquivOfEq _ _ _ (ef.symm (f x))) = p x
    have hex : ef.symm (f x) = Submodule.Quotient.mk x := by
      simpa only [ef, IntertwiningMap.toLinearMap_apply] using
        LinearMap.quotKerEquivOfSurjective_symm_apply (f := f.toLinearMap) hf x
    rw [hex, Submodule.quotEquivOfEq_mk]
    rfl
  refine ⟨Representation.Equiv.mk e ?_⟩
  intro g
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hf y
  change e (σ g (f x)) = τ g (e (f x))
  rw [← IntertwiningMap.isIntertwining ρ σ f, he,
    IntertwiningMap.isIntertwining ρ τ p, he]

theorem mixedClassification.{u} : CoverModels.MixedClassification.{u} := by
  intro W _ _ _ σ p hp hk
  obtain ⟨q, hq, hcompat⟩ := exists_doubled_quotient p hp
  have hW : Module.finrank (ZMod 2) W = 7 := by
    have h := p.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hp.1, finrank_top, finrank_natural, hk] at h
    omega
  have hqkerdim : Module.finrank (ZMod 2) q.toLinearMap.ker = 1 := by
    have h := q.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hq, finrank_top (ZMod 2) W, finrank_doubled] at h
    rw [hW] at h
    omega
  have hqker_le : q.toLinearMap.ker ≤ doubledProjection.toLinearMap.ker := by
    intro y hy
    have hy' : q y = 0 := hy
    simpa [hy'] using (hcompat y).symm
  have hproj_ne : projection.toLinearMap.ker ≠ ⊥ := by
    intro h
    have hdim := projection_kernel_finrank
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).mp hproj_ne
  have hspan : projection.toLinearMap.ker = (ZMod 2) ∙ z :=
    eq_span_singleton_of_mem_of_finrank_eq_one projection_kernel_finrank hz hz0
  have hqker_ne : q.toLinearMap.ker ≠ ⊥ := by
    intro h
    have hdim := hqkerdim
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hqker_ne
  have hxdp := hqker_le hx
  have hxcoord := (doubledProjection_mem_ker_iff x).mp hxdp
  obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton.mp (hspan ▸ hxcoord.1))
  obtain ⟨b, hb⟩ := (Submodule.mem_span_singleton.mp (hspan ▸ hxcoord.2))
  have ha_cases : x.1 = 0 ∨ x.1 = z := by
    fin_cases a
    · left
      change (0 : ZMod 2) • z = x.1 at ha
      rw [zero_smul] at ha
      exact ha.symm
    · right
      change (1 : ZMod 2) • z = x.1 at ha
      rw [one_smul] at ha
      exact ha.symm
  have hb_cases : x.2 = 0 ∨ x.2 = z := by
    fin_cases b
    · left
      change (0 : ZMod 2) • z = x.2 at hb
      rw [zero_smul] at hb
      exact hb.symm
    · right
      change (1 : ZMod 2) • z = x.2 at hb
      rw [one_smul] at hb
      exact hb.symm
  obtain ⟨A, hAx⟩ : ∃ A : doubled.Equiv doubled, A x = (0, z) := by
    rcases ha_cases with h₁ | h₁ <;> rcases hb_cases with h₂ | h₂
    · exfalso
      apply hx0
      exact Prod.ext h₁ h₂
    · refine ⟨Representation.Equiv.refl doubled, ?_⟩
      exact Prod.ext h₁ h₂
    · refine ⟨swapEquiv, ?_⟩
      exact Prod.ext h₂ h₁
    · refine ⟨shearEquiv, ?_⟩
      change (x.1 + x.2, x.2) = (0, z)
      simp [h₁, h₂, ZModModule.add_self]
  let q' := q.comp A.symm.toIntertwiningMap
  have hq'_surj : Function.Surjective q' := hq.comp A.symm.surjective
  have hq'_ker : q'.toLinearMap.ker = mixedLift.toLinearMap.ker := by
    have hq'dim : Module.finrank (ZMod 2) q'.toLinearMap.ker = 1 := by
      have h := q'.toLinearMap.finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr hq'_surj, finrank_top (ZMod 2) W,
        finrank_doubled] at h
      omega
    have hq'mem : (A x) ∈ q'.toLinearMap.ker := by
      change q (A.symm (A x)) = 0
      rw [A.symm_apply_apply]
      exact hx
    have hq'ne : A x ≠ 0 := by
      intro h
      apply hx0
      apply A.injective
      simpa using h
    have hq'span : q'.toLinearMap.ker = (ZMod 2) ∙ (A x) :=
      eq_span_singleton_of_mem_of_finrank_eq_one hq'dim hq'mem hq'ne
    have hmixmem : ((0, z) : U × U) ∈ mixedLift.toLinearMap.ker := by
      change mixedLift (0, z) = 0
      exact Prod.ext rfl hz
    have hmixspan : mixedLift.toLinearMap.ker = (ZMod 2) ∙ (0, z) :=
      eq_span_singleton_of_mem_of_finrank_eq_one mixedLift_kernel_finrank hmixmem (by
        intro h
        exact hz0 (Prod.ext_iff.mp h).2)
    rw [hAx] at hq'span
    exact hq'span.trans hmixspan.symm
  exact equiv_of_surj_same_ker q' hq'_surj mixedLift mixedLift_surjective hq'_ker

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels
