module
public import CFSG.Quasithin.Chapter15.Section01.SourceOmegaNonsolvable
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PreparedChosen

/-!
# Preparing the full Omega chosen module

The original Omega action has quadratic ratio two and odd two-residual.
The full core-containment theorem now puts the actual local module in every
H-star two-core. Together these prove every field of `PreparedChosenModule`.
The source alternatives consequently retain only the rank-two and natural
orthogonal endpoints before the prepared chosen-module branch. The existing
chief-factor consumer applies to this full Omega module as well.

Source: Aschbacher--Smith 15.1.4--12, printed pp.1087--1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original full Omega module satisfies all chosen-module preparation conclusions. -/
theorem source_fullOmega_prepared
    (hA : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    SourceCases.Omega (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) → PreparedChosenModule T M (localModule T M) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro ho
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  have hVne : V ≠ ⊥ := by
    intro he
    exact centralInvolutions_ne_bot_of_maximal_local T hM.1
      (bot_unique ((le_conjugateSpanBy _ _).trans he.le))
  have hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M := by
    have hZV : centralInvolutions T ≤ V := le_conjugateSpanBy _ _
    rw [inf_eq_left.mpr hZV]
    rfl
  have hq : quadraticRatio ρ = 2 := quadraticRatio_eq_two_of_four_cubic ρ
    (by rw [ho.2.2.1])
    (by rw [ho.2.1]; norm_num [ENNReal.lt_div_iff_mul_lt])
    (by rw [ho.2.1, ENNReal.div_le_iff (by norm_num) (by norm_num)]; norm_num)
  have hodd : Odd (Nat.card (pResidual 2 (internalActionImage M V
      (le_normalizer_conjugateSpanBy _ _)))) := by
    obtain ⟨_,e,_⟩ := ho.2.2.2.2
    exact OrthogonalFourBinary.TerminalLines.odd_twoResidual_of_injective
      (OrthogonalFourBinary.omega.subtype.comp e.toMonoidHom)
      (OrthogonalFourBinary.omega.subtype_injective.comp e.injective)
  refine ⟨le_rfl,localModule_le T hM.1.2,hVne,le_normalizer_conjugateSpanBy _ _,
    inferInstance,hspan,hq,?_,?_,?_⟩
  · exact chosen_seed_centralizer_residual_of_odd_residual T hM.1.2
      (localModule_le T hM.1.2) (le_normalizer_conjugateSpanBy _ _) hodd
  · intro H hH
    exact source_15_1_9_4_of_odd_residual hG T hM hH hJ
      (localModule_le T hM.1.2) (le_normalizer_conjugateSpanBy _ _) hodd
  · intro H hH
    exact source_fullOmega_module_le_core hA hC hG T hempty hM hJ hH ho

/-- The literal full-Omega conjugate span is elementary with exactly two noncentral chief factors. -/
theorem source_fullOmega_chief_data
    (hA : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    SourceCases.Omega (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      IsElementaryAbelian 2 (conjugateSpan H (localModule T M)) ∧
      ∀ s : SeriesOn ((conjugateSpan H (localModule T M)).subgroupOf H),
        s.noncentralCount = 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro ho
  exact (source_fullOmega_prepared hA hC hG T hempty hM hJ ho).chief_data hG T hempty hM hJ

/-- The original centralizing alternatives, with the full Omega preparation discharged. -/
theorem source_prepared_chosen_alternatives_from_AC
    (hA : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    (cubicRatio ρ = 1 ∧ Module.finrank (ZMod 2) (Additive V) = 2) ∨
    Nonempty (NaturalOrthogonalAction M V) ∨
    ∃ W : Subgroup G,
      (W = V ∨ ∃ U : Submodule (ZMod 2) (Additive V),
        SourceCases.Proper T M Mc V ρ U ∧
        W = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) ∧
      PreparedChosenModule T M W := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  rcases source_prepared_chosen_alternatives hG T hempty hM hmany hJ hu hne with
    hsmall | hn | ho | hprepared
  · exact Or.inl hsmall
  · exact Or.inr (Or.inl hn)
  · exact Or.inr (Or.inr ⟨localModule T M,Or.inl rfl,
      source_fullOmega_prepared hA hC hG T hempty hM hJ ho⟩)
  · exact Or.inr (Or.inr hprepared)

end CFSG.Quasithin.Chapter15.Section01
