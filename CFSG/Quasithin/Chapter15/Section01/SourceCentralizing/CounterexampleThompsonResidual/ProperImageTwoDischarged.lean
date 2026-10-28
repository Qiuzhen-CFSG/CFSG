module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.OmegaSourceDirect
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.CounterexampleThompsonResidual
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonProper

/-!
# Discharge the original proper-support Thompson image branch

The literal proper-support witness supplies the chosen Omega action.
Its Section 15.2 contradiction is now independent of global 15.1.14,
so the same original support discharges the actual counterexample
normalization contract. No minimal-parabolic descent or extra core
centralization premise is used.

Source: Aschbacher--Smith 15.1.13--14 and 15.2.1--28,
printed pp.1090--1091 and 1104--1120.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The actual proper-image-two normalization input, with every additional
premise discharged from the original source ambient hypotheses. -/
theorem source_proper_thompson_image_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    SourceProperThompsonImageTwoInput hG T Mc := by
  intro _hmodel _hno M hM hne hJ
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro U hU W hp _htwo
  let := hp.elementary
  have ho := hU.chosen_omega T M Mc (localModule T M)
    (le_normalizer_conjugateSpanBy _ _) U hp.normalized
  let h : Section02.ChosenSmallSource T M Mc W :=
    ⟨hG,hempty,hM,hmany,hJ,hu,hne,hp,Or.inr ⟨U,hU,rfl⟩,Or.inr ho⟩
  exact (Section02.source_chosen_omega_contradiction h ho).elim

end CFSG.Quasithin.Chapter15.Section01
