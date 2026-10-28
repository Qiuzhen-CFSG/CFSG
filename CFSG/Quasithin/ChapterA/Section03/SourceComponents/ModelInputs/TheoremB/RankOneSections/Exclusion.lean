module

public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.RankOneSections.Targets
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.RankOneSections.Profiles
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# Excluding the normalized rank-one targets from component outer groups

The complete B-model profile and the actual target orders exclude both
PSU₃(2ˢ), s ≥ 2, and Sz(2²ᵐ⁺¹), m ≥ 1, as nonsolvable simple outer sections.
Perfect central descent embeds Out(K) into Out(K/Z(K)), so the conclusion
retains every quasisimple central cover K and every literal subgroup of Out(K).

Source: Aschbacher--Smith 4.4.10--11, printed p.621. These are the section
exclusions consumed by the normalized Chapter 12 odd-local reduction;
full outer solvability is neither required nor asserted.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents.TheoremBOuter.RankOneSections

/-- The complete simple B-model catalogue has none of the indicated target
sections in its actual outer automorphism group. -/
theorem simple_no_target_section
    {S Q : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hna : ¬ IsMulCommutative S) (hm : Section02.IsTheoremBModel S)
    (hQ : ¬ Group.IsSolvable Q) (ht : IsTarget Q)
    (U : Subgroup (MulAut.Outer S)) (f : U →* Q) : ¬ Function.Surjective f := by
  intro hf
  rcases model_profile hna hm with hsol | ⟨P,hP⟩
  · let : Group.IsSolvable (MulAut.Outer S) := hsol
    exact hQ (Group.isSolvable_of_surjective hf)
  · let : Group.IsSolvable (fixingSubgroup (MulAut S) (P : Set S)) :=
      ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
    exact ht.order_not_dvd_GL_eight
      (MulAut.simple_outer_section_card_dvd_GL_eight P hP hQ U f hf)

/-- Central descent preserves the exclusion for every actual quasisimple
cover of a B-model, without replacing that cover by its central quotient. -/
theorem cover_no_target_section
    {K Q : Type*} [Group K] [Finite K] [IsQuasisimple K]
    [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hm : Section02.IsTheoremBModel (K ⧸ center K))
    (hQ : ¬ Group.IsSolvable Q) (ht : IsTarget Q)
    (U : Subgroup (MulAut.Outer K)) (f : U →* Q) : ¬ Function.Surjective f := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let e := MulEquiv.refl (K ⧸ center K)
  let j := MulAut.centralQuotientOuter e
  let a := U.equivMapOfInjective j (MulAut.centralQuotientOuter_injective e)
  intro hf
  exact simple_no_target_section (Group.IsPerfect.not_isMulCommutative _) hm hQ ht
    (U.map j) (f.comp a.symm.toMonoidHom) (hf.comp a.symm.surjective)

end CFSG.Quasithin.ChapterA.Section03.SourceComponents.TheoremBOuter.RankOneSections
