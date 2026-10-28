module

public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.Exchanged

/-!
# Normality of the rank-two containing components

The existing nonnormal ordinary-component theorem gives cubic rank at most
one after the ambient two-core quotient. Its literal component image still
surjects onto the original central quotient. The odd-prime rank-one quotient
bound therefore excludes a central quotient of cubic rank at least two.

This is the normality input for the second pumpup in source 2.5.19,
printed pp.563–564; it retains all central covering kernels.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource
open ChapterA.SQTKStructure ChapterA.SQTKStructure.NonnormalOuterSource

/-- Cubic rank two in the actual central quotient forces an ordinary
component of an SQTK group to be normal. -/
theorem component_normal_of_central_quotient_rank_two
    {E : Type*} [Group E] [Finite E]
    (hE : IsSQTK KnownSimple.IsKnownSimple E) (J : Subgroup E)
    (hJ : IsComponent E J) (hr : 2 ≤ primeRank 3 (J ⧸ center J)) : J.Normal := by
  by_contra hn
  let : IsQuasisimple J := hJ.2
  let : Group.IsNilpotent (pCore 2 E) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 E)
  let C := J.map q
  have hc : C.IsCComponent := hJ.isCComponent.map_quotient (pCore 2 E)
  have hnc : ¬ C.Normal := fun h => hn (cComponent_normal_of_quotient_normal hJ.isCComponent _ h)
  have hC : IsComponent (E ⧸ pCore 2 E) C := by
    rcases hJ.map_surjective q (QuotientGroup.mk'_surjective _) with h | h
    · exact (hc.ne_bot h).elim
    · exact h
  let : IsQuasisimple C := hC.2
  have hQ := ChapterI.RankTwoSource.sqtk_twoCore_quotient hE
  have hf : fittingSubgroup C ≤ center C :=
    (le_solvableRadical _ inferInstance inferInstance).trans IsQuasisimple.solvableRadical_le_center
  have hm := (ordinary_model_of_central_fitting
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hQ C hc hf).2
  have hrC : primeRank 3 C ≤ 1 := FourModels.odd_ranks_of_model hQ.stronglyQuasithin
    (pCore_quotient_pCore_eq_bot 2) C hC hnc hm 3 (by decide) (by decide)
  have hcore : pCore 2 J ≤ center J := by
    let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
    exact (le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center
  let f : (J ⧸ pCore 2 J) →* (J ⧸ center J) :=
    QuotientGroup.lift (pCore 2 J) (QuotientGroup.mk' (center J))
      (by intro x hx; exact (QuotientGroup.eq_one_iff x).mpr (hcore hx))
  have hsur : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center J) y
    exact ⟨QuotientGroup.mk' (pCore 2 J) x,rfl⟩
  let e : (J ⧸ pCore 2 J) ≃* C := cComponentTwoCoreQuotientEquiv hJ.isCComponent
  let g : C →* (J ⧸ center J) := f.comp e.symm.toMonoidHom
  have hg : Function.Surjective g := hsur.comp e.symm.surjective
  have hb := (PrimeRank.le_of_surjective_of_source_le_one
    (by decide : (3 : ℕ) ≠ 2) g hg hrC).trans hrC
  omega

end CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource
