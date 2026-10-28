module

public import CFSG.Quasithin.Chapter7.NormalizedSource.Alternatives
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.RankOneSections.Profiles
public import Theory.GroupTheory.SylowOuterFrattiniSections
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# Mathieu quotients do not occur in component outer groups

The complete Theorem B profile gives either solvable outer automorphisms or
at most eight binary Sylow Frattini generators. A nonsolvable simple section
in the latter case has order dividing |GL₈(2)|, which is prime to eleven.
Every actual Mathieu quotient in the chosen-module family contains eleven.
Injective central descent applies this exclusion to the full quasisimple
component, retaining its covering center.

This discharges the outer-section input to the residual placement in
`MathieuGeneration.HallFaithfulness`; it does not assume residual uniqueness.
Source: Aschbacher--Smith, 4.4.10--11, printed p.621, and Theorem B, p.33.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

/-- Every actual Mathieu quotient in the chosen-module family has the prime eleven. -/
theorem mathieu_centralQuotient_eleven_dvd {Q : Type*} [Group Q]
    (hm : HasMathieuCentralQuotient Q) : 11 ∣ Nat.card (Q ⧸ center Q) := by
  rcases hm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m12_order]; norm_num
  · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m22_order]; norm_num
  · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m23_order]; norm_num
  · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m24_order]; norm_num

private theorem simple_no_outer_section_of_eleven
    {S Q : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hna : ¬ IsMulCommutative S) (hm : ChapterA.Section02.IsTheoremBModel S)
    (hQ : ¬ Group.IsSolvable Q) (h11 : 11 ∣ Nat.card Q)
    (U : Subgroup (MulAut.Outer S)) (f : U →* Q) : ¬ Function.Surjective f := by
  intro hf
  rcases ChapterA.Section03.SourceComponents.TheoremBOuter.RankOneSections.model_profile
      hna hm with hsol | ⟨P,hP⟩
  · let : Group.IsSolvable (MulAut.Outer S) := hsol
    exact hQ (Group.isSolvable_of_surjective hf)
  · let : Group.IsSolvable (fixingSubgroup (MulAut S) (P : Set S)) :=
      ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
    have hd := h11.trans (MulAut.simple_outer_section_card_dvd_GL_eight P hP hQ U f hf)
    norm_num at hd

/-- The Mathieu simple quotient is not a section of the outer group of any
quasisimple cover of a Theorem B model. -/
theorem mathieu_centralQuotient_no_outer_section
    {K Q : Type*} [Group K] [Finite K] [IsQuasisimple K]
    [Group Q] [Finite Q] [IsQuasisimple Q]
    (hK : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (hm : HasMathieuCentralQuotient Q)
    (U : Subgroup (MulAut.Outer K)) (f : U →* (Q ⧸ center Q)) :
    ¬ Function.Surjective f := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect (Q ⧸ center Q) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
  let e := MulEquiv.refl (K ⧸ center K)
  let j := MulAut.centralQuotientOuter e
  let a := U.equivMapOfInjective j (MulAut.centralQuotientOuter_injective e)
  intro hf
  exact simple_no_outer_section_of_eleven (Group.IsPerfect.not_isMulCommutative _) hK
    (Group.IsPerfect.not_isSolvable _) (mathieu_centralQuotient_eleven_dvd hm)
    (U.map j) (f.comp a.symm.toMonoidHom) (hf.comp a.symm.surjective)

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
