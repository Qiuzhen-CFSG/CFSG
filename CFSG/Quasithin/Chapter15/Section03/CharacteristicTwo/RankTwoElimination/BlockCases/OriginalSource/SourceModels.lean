module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RawStarSieve
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenExceptionalSecondChoice

/-!
# Binary models from the original rank-two source

The original characteristic-two component input supplies the literal moved
section and quasisimple B.5 row. The source-specific exclusions close every
small and exceptional row in both local choices. Proper outside-subgroup
induction removes the larger linear rows, leaving only the binary projective
models of degrees three, four and five. The actual central-cover map then
transports this list from the star image to the component two-core quotient.

Source: Aschbacher–Smith 15.3.16–22, printed pp.1126–1128.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

theorem source_15_3_21_raw_exceptionalSeven_row
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    let ρ := (starRepresentation c.L d.R).comp J.subtype
    let C0 := C.subgroupOf J
    ∀ (_hCJ : C ≤ J)
      (qsrc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C0),
    let s := qsrc.sectionData
    ∀ (_hplus : IsIrrPlus ρ C0 s.space.toSubmodule)
      (_hfaith : Function.Injective s.action)
      (_hirr : IsIrreducible (s.action.comp C0.subtype))
      (_hgen : offenderSubgroup s.action = C0) (_hwhole : C0 = ⊤)
      (e : C0 ≃* alternatingGroup (Fin 7))
      (_hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4)
      (_hoff : ∀ A, IsBestOffender s.action A → ∃ g : alternatingGroup (Fin 7),
        ((A.subgroupOf C0).map ((alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom)) =
        (Subgroup.closure {ChapterB.Offenders.kleinFirst 7 (by decide),
          ChapterB.Offenders.kleinSecond 7 (by decide)}).map
          (MulAut.conj (g : Equiv.Perm (Fin 7))).toMonoidHom)
      (_hq : quadraticRatio s.action = 1), False := by
  intro C J ρ C0 hCJ qsrc s hi hfaith hir hgen hwhole e hd hoff hq
  rcases d.choice with hfirst | hsecond
  · exact source_15_3_21_raw_exceptionalSeven_first_choice_of_row
      hG d hempty hM hu hmany hI htwo hf c hfirst hCJ qsrc hi hfaith hir hgen hwhole e hd hoff hq
  · exact source_15_3_21_raw_exceptionalSeven_second_choice_of_row
      hG d hempty hM hu hmany hI htwo hf c hsecond hCJ qsrc hi hfaith hir hgen hwhole e hd hoff hq

/-- The literal star image in the original source has one of the three
surviving binary projective models. -/
theorem source_binary_star_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hproper : ∀ K : Subgroup G, K < I → K ∈ d.Hplus → ¬ HasCharacteristicTwo K)
    : ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nonempty (starImage c.L d.R c.L ≃* PSL(n,ZMod 2)) := by
  exact source_binary_star_models_of_exceptionalSeven_exclusion
    hG d hempty hM hu hmany hI htwo hf c hproper
      (source_15_3_21_raw_exceptionalSeven_row hG d hempty hM hu hmany hI htwo hf c)

/-- The original component two-core quotient has the same surviving binary
list; the central-cover transport is supplied by original 15.3.22. -/
theorem source_binary_core_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hproper : ∀ K : Subgroup G, K < I → K ∈ d.Hplus → ¬ HasCharacteristicTwo K)
    : ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nonempty ((c.L ⧸ pCore 2 c.L) ≃* PSL(n,ZMod 2)) := by
  exact source_binary_core_models_of_exceptionalSeven_exclusion
    hG d hempty hM hu hmany hI htwo hf c hproper
      (source_15_3_21_raw_exceptionalSeven_row hG d hempty hM hu hmany hI htwo hf c)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
