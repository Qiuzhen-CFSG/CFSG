module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.ExplicitOffenders.ActorProducts
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.ExplicitOffenders.ElementaryRanks
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.ExplicitOffenders.InvolutionDisplacement
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Offender exclusion for the explicit cover actors

A mixed actor fixing the natural summand lies in the central shear subgroup.
Consequently any subgroup containing the shear and having rank at least two
has fixed codimension at least four. Every elementary subgroup has rank at
most three, and every nonidentity involution has displacement at least three
in the mixed group and four in the doubled group. A mixed offender would
therefore have rank three and contain the shear, contradicting the strict
fixed-space bound. The doubled displacement bound excludes offenders directly.

The final theorems discharge every premise of the conditional assembly using
the actual actor product identifications and their proved rank, containment
and displacement bounds. They exclude all elementary offenders in these
generated groups. The full-normalizer coverage needed for arbitrary ambient
overgroups is a separate result.
Source context: Aschbacher–Smith, combined manuscript (1 March 2004),
C.1.34(2),(5), printed pp.136–137, and I.1.5–6, printed p.408.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders

/-- The actual shear has fixed codimension three in the tautological action. -/
lemma mixedShearActor_fixedCodim :
    fixedCodim (subgroupAction mixedActors) (Subgroup.zpowers mixedShearActor) = 3 := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact mixedShear_displacement_finrank

/-- A subgroup of rank at least two containing the shear has strictly smaller
fixed space than the shear alone. -/
lemma mixed_fixedCodim_ge_four (A : Subgroup mixedActors)
    (hs : mixedShearActor ∈ A) (hr : 2 ≤ rank A) :
    4 ≤ fixedCodim (subgroupAction mixedActors) A := by
  let ρ := subgroupAction mixedActors
  let S := Subgroup.zpowers mixedShearActor
  have hS : S ≤ A := Subgroup.zpowers_le.mpr hs
  have hle : fixedSpace ρ A ≤ fixedSpace ρ S := by
    intro v hv a
    exact hv ⟨a.val, hS a.property⟩
  have hne : fixedSpace ρ A ≠ fixedSpace ρ S := by
    intro he
    have hAS : A ≤ S := by
      intro a ha
      apply mixedActor_fixes_natural
      intro v
      have hv : (0,v) ∈ fixedSpace ρ S := by
        rw [mem_fixedSpace_zpowers_iff]
        change (0, v + projection 0) = (0,v)
        simp only [map_zero, add_zero]
      rw [← he] at hv
      exact hv ⟨a,ha⟩
    have hc : Nat.card A ≤ 2 := by
      have hcard := Subgroup.card_le_of_le hAS
      have hcardS : Nat.card S ≤ 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by decide) mixedShearActor_sq
      exact hcard.trans hcardS
    have hlog : rank A ≤ 1 := by
      exact (Nat.log_mono_right hc).trans (by decide : Nat.log 2 2 ≤ 1)
    omega
  have hdim := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
  have hdimA := fixedCodim_add_finrank ρ A
  have hdimS := fixedCodim_add_finrank ρ S
  have hsCodim : fixedCodim ρ S = 3 := mixedShearActor_fixedCodim
  change 4 ≤ fixedCodim ρ A
  omega


private lemma displacement_le_fixedCodim {G M : Type*} [Group G]
    [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (ρ : Representation (ZMod 2) G M) (A : Subgroup G) (a : G) (ha : a ∈ A) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ fixedCodim ρ A := by
  have hle : fixedSpace ρ A ≤ fixedSpace ρ (Subgroup.zpowers a) := by
    intro v hv b
    exact hv ⟨b.val, Subgroup.zpowers_le.mpr ha b.property⟩
  have hdim := Submodule.finrank_mono hle
  have hA := fixedCodim_add_finrank ρ A
  have ha' := fixedCodim_add_finrank ρ (Subgroup.zpowers a)
  rw [fixedCodim_zpowers_eq_displacement_rank] at ha'
  omega

/-- The mixed exclusion follows from elementary rank, extremal shear containment,
and pointwise involution displacement. These three inputs remain explicit. -/
theorem mixedActors_not_isFFModule_of_bounds
    (hrank : ∀ A : Subgroup mixedActors, IsElementaryAbelian 2 A → rank A ≤ 3)
    (hshear : ∀ A : Subgroup mixedActors, IsElementaryAbelian 2 A →
      rank A = 3 → mixedShearActor ∈ A)
    (hdisplace : ∀ a : mixedActors, a ^ 2 = 1 → a ≠ 1 →
      3 ≤ Module.finrank (ZMod 2) (LinearMap.range (a.val.toLinearMap - LinearMap.id))) :
    ¬ IsFFModule (subgroupAction mixedActors) := by
  rintro ⟨A,hA⟩
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1.1
  have ha' : (a : mixedActors) ≠ 1 := fun h => ha (Subtype.ext h)
  have hpow : (a : mixedActors) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ a.property
  have hpoint := hdisplace a.val hpow ha'
  have hcodim := displacement_le_fixedCodim (subgroupAction mixedActors) A a.val a.property
  change Module.finrank (ZMod 2) (LinearMap.range (a.val.val.toLinearMap - LinearMap.id)) ≤
    fixedCodim (subgroupAction mixedActors) A at hcodim
  have hlower : 3 ≤ fixedCodim (subgroupAction mixedActors) A := hpoint.trans hcodim
  have hr := hrank A hA.1.2
  have ho := hA.2
  have hr3 : rank A = 3 := by omega
  have hfour := mixed_fixedCodim_ge_four A (hshear A hA.1.2 hr3) (by omega)
  omega

/-- In the doubled group, displacement at least four excludes every elementary
subgroup of rank at most three. Both bounds remain explicit. -/
theorem doubledActors_not_isFFModule_of_bounds
    (hrank : ∀ A : Subgroup doubledActors, IsElementaryAbelian 2 A → rank A ≤ 3)
    (hdisplace : ∀ a : doubledActors, a ^ 2 = 1 → a ≠ 1 →
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (a.val.toLinearMap - LinearMap.id))) :
    ¬ IsFFModule (subgroupAction doubledActors) := by
  rintro ⟨A,hA⟩
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1.1
  have ha' : (a : doubledActors) ≠ 1 := fun h => ha (Subtype.ext h)
  have hpow : (a : doubledActors) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ a.property
  have hpoint := hdisplace a.val hpow ha'
  have hcodim := displacement_le_fixedCodim (subgroupAction doubledActors) A a.val a.property
  change Module.finrank (ZMod 2) (LinearMap.range (a.val.val.toLinearMap - LinearMap.id)) ≤
    fixedCodim (subgroupAction doubledActors) A at hcodim
  have hlower : 4 ≤ fixedCodim (subgroupAction doubledActors) A := hpoint.trans hcodim
  have hr := hrank A hA.1.2
  have ho := hA.2
  omega

/-- The actual mixed cover action admits no nontrivial elementary abelian
subgroup whose fixed codimension is at most its rank. -/
theorem mixedActors_not_isFFModule :
    ¬ IsFFModule (subgroupAction mixedActors) :=
  mixedActors_not_isFFModule_of_bounds
    mixedActors_elementary_rank_le_three
    mixedShearActor_mem_of_rank_three
    mixedActors_involution_displacement_ge_three

/-- The actual doubled cover action admits no nontrivial elementary abelian
subgroup whose fixed codimension is at most its rank. -/
theorem doubledActors_not_isFFModule :
    ¬ IsFFModule (subgroupAction doubledActors) :=
  doubledActors_not_isFFModule_of_bounds
    doubledActors_elementary_rank_le_three
    doubledActors_involution_displacement_ge_four

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders
