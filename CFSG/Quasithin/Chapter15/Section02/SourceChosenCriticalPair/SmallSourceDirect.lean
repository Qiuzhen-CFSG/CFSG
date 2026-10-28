module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallSourceFinalQuotients
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualDirectAssembly
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Resolver

/-!
# The small-source contradiction from the original source prior

The small-parabolic theorem supplies every actual H-star wreath quotient.
The direct residual-input route gives plane uniqueness and the original
critical-pair contradiction. Thus no residual identity or residual structure
premise remains; the original prior is inherited literally from the
actual 15.1.3 resolver.

Source: Aschbacher--Smith 15.2.1--28, printed pp.1104--1120,
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterF.Source ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The original source prior gives the full chosen small-source
contradiction without any residual-identity or mixed-size premise. -/
theorem source_chosen_contradiction
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hprior : SmallSourcePrior T M V) : False :=
  source_chosen_contradiction_of_wreath_quotients h (h.maximal_overgroups hprior)
    (h.HStar_wreath hprior)


/-- The actual 15.1.3 resolver's small-action premise is discharged using
its literal source prior and the same full-or-proper chosen module. -/
theorem source_smallChosenExclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    SourceSmallChosenExclusionInput hG T Mc := by
  intro hmodel hno M hM hne hJ
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro W hW hp
  let := hp.elementary
  intro hres _ hsmall
  let h : ChosenSmallSource T M Mc W :=
    ⟨hG,hempty,hM,hmany,hJ,hu,hne,hp,hW,hsmall⟩
  exact source_chosen_contradiction h ⟨hres,hmodel,hno⟩

end CFSG.Quasithin.Chapter15.Section02
