module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneRow
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.LinearThreeRows
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.G2Larger
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.SymplecticStarExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.SymplecticTwoRow
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.SymmetricFiveRow
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenRawTriple
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.BinaryG2Star
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.BinaryCover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSixRaw
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.TripleSixRaw
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenExceptionalRaw
/-!
# Exhausting the actual moved-section rows in original 15.3.13

The selected C.2.7 input constructs its literal star module and supplies the
full B.5 quasisimple moved-section conclusion. Each raw constructor is
consumed using the original rank-two source hypotheses. The exceptional
seven-point action is exposed through a source-specific row interface;
SourceModels supplies both local choices, including control of the possible
odd central component cover in the second choice.

The surviving rows have literal star images PSL3(2), PSL4(2), or PSL5(2).
The eight-point orthogonal and symmetric models are carried through the
A8-PSL4(2) equivalence, without identifying their modules with a linear
natural module. This is the exact source15.3.22 star-model input.

Source: Aschbacher--Smith 15.3.13--22, pp.1125--1128; B.5.1.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

theorem source_binary_star_models_of_exceptionalSeven_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hproper : ∀ K : Subgroup G, K < I → K ∈ d.Hplus → ¬ HasCharacteristicTwo K)
    (noA7 :
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
      (_hq : quadraticRatio s.action = 1), False) :
    ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nonempty (starImage c.L d.R c.L ≃* PSL(n,ZMod 2)) := by
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hCJ,⟨qsrc⟩⟩ := ChapterC.C27Source.star_moved_section_from_source h
  let C := starImage c.L d.R c.L
  let J := offenderSubgroup (starRepresentation c.L d.R)
  let s := qsrc.sectionData
  let ι := (subgroupOfEquivOfLe hCJ).symm
  have hb (n : ℕ) (hn : n = 4 ∨ n = 5)
      (e : C.subgroupOf J ≃* SL(n,ZMod 2)) :
      ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nonempty (C ≃* PSL(n,ZMod 2)) :=
    ⟨n,Or.inr hn,⟨(ι.trans e).trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)).symm⟩⟩
  have ha (e : C.subgroupOf J ≃* alternatingGroup (Fin 8)) :
      ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nonempty (C ≃* PSL(n,ZMod 2)) :=
    ⟨4,Or.inr (Or.inl rfl),⟨(ι.trans e).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩
  cases qsrc.clause_one with
  | irreducible hi hfaith hir row hext =>
    cases row with
    | linearTwo F _ e hoff hq =>
      exact (source_15_3_18_linearTwo_row hG d hempty hM hu hmany hI htwo hf c hCJ s F e hq hoff).elim
    | linearThree F _ e _ =>
      exact ⟨3,Or.inl rfl,source_linearThree_row_binary hG d hempty hM hu hmany hI htwo hf c hproper hCJ s F e⟩
    | symplectic F hF _ e _ =>
      have hc : 4 ≤ Nat.card F.Carrier := by
        rw [F.card_eq]
        exact (show 2^2 ≤ 2^F.degree from Nat.pow_le_pow_right (by decide) hF)
      exact (source_15_3_20_symplectic_star hG d hempty hM hu hmany hI htwo hf c hc (ι.trans e.groupEquiv)).elim
    | symplecticTwo e _ =>
      exact (source_15_3_21_symplecticTwo_row hG d hempty hM hu hmany hI htwo hf c hCJ s _ e).elim
    | g2 F hn _ e _ _ =>
      exact (source_15_3_20_g2_star hG d hempty hM hu hmany hI htwo hf c hproper F.card_eq hn (ι.trans e.groupEquiv)).elim
    | g2Two e _ _ =>
      exact (source_15_3_21_g2Two_row hG d hempty hM hu hmany hI htwo hf c hCJ s _ e).elim
    | symmetric n hn e _ _ =>
      rcases hn with rfl | rfl
      · exact (source_15_3_19_symmetricFive_row hG d hempty hM hu hmany hI htwo hf c hCJ s e).elim
      · exact (source_15_3_21_symmetricSeven_row hG d hempty hM hu hmany hI htwo hf c hCJ s e).elim
    | alternatingSix hgen e hoff hq =>
      exact (source_15_3_21_alternatingSix_row hG d hempty hM hu hmany hI htwo hf c hCJ s hgen e hoff hq).elim
    | alternatingSeven hgen hwhole e hd hoff hq =>
      exact (noA7 hCJ qsrc hi hfaith hir hgen hwhole e hd hoff hq).elim
    | tripleSix _ a _ =>
      exact (source_15_3_21_tripleSix_row hG d hempty hM hu hmany hI htwo hf c hCJ qsrc hi hfaith hir a).elim
    | binaryLinear n hn _ e _ => exact hb n hn e.groupEquiv
    | orthogonalSix _ _ e _ _ => exact ha e.groupEquiv
    | symmetricEight _ e _ => exact ha e.subgroupEquiv
    | exteriorFive _ _ e _ _ _ => exact hb 5 (Or.inr rfl) e
  | doubleThree F _ e _ _ =>
    exact ⟨3,Or.inl rfl,source_doubleThree_row_binary hG d hempty hM hu hmany hI htwo hf c hproper hCJ s F e⟩
  | naturalDual n hn _ he =>
    obtain ⟨e⟩ := he
    exact hb n hn e.groupEquiv
  | repeatedNatural n r hn _ _ _ he =>
    obtain ⟨e⟩ := he
    exact hb n hn e.groupEquiv


/-- The first original choice already yields the complete binary star list. -/
theorem source_binary_star_models_firstChoice
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hproper : ∀ K : Subgroup G, K < I → K ∈ d.Hplus → ¬ HasCharacteristicTwo K)
    (hfirst : d.Yplus = d.Y) :
    ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nonempty (starImage c.L d.R c.L ≃* PSL(n,ZMod 2)) := by
  exact source_binary_star_models_of_exceptionalSeven_exclusion
    hG d hempty hM hu hmany hI htwo hf c hproper
      (source_15_3_21_raw_exceptionalSeven_first_choice_of_row
        hG d hempty hM hu hmany hI htwo hf c hfirst)

/-- Literal source15.3.22 consumer for the first original choice. The covering
map, including its possible central kernel, is discharged by the binary models. -/
theorem source_binary_core_models_firstChoice
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hproper : ∀ K : Subgroup G, K < I → K ∈ d.Hplus → ¬ HasCharacteristicTwo K)
    (hfirst : d.Yplus = d.Y) :
    ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nonempty ((c.L ⧸ pCore 2 c.L) ≃* PSL(n,ZMod 2)) := by
  exact source_15_3_22_from_selection_of_binary_star_models
    hG d hempty hM hu hmany hI (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) c
      (source_binary_star_models_firstChoice hG d hempty hM hu hmany hI htwo hf c hproper hfirst)


/-- Original 15.3.22 on the exact selected component and star quotient.
The only open classification row is the exceptional A7 second choice. -/
theorem source_binary_core_models_of_exceptionalSeven_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hproper : ∀ K : Subgroup G, K < I → K ∈ d.Hplus → ¬ HasCharacteristicTwo K)
    (noA7 :
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
      (_hq : quadraticRatio s.action = 1), False) :
    ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nonempty ((c.L ⧸ pCore 2 c.L) ≃* PSL(n,ZMod 2)) := by
  exact source_15_3_22_from_selection_of_binary_star_models
    hG d hempty hM hu hmany hI (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) c
      (source_binary_star_models_of_exceptionalSeven_exclusion
        hG d hempty hM hu hmany hI htwo hf c hproper noA7)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
