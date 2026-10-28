module
public import Theory.Representation.BinaryPlaneRecognition
public import CFSG.Quasithin.Chapter14.Section02.RankTwoEntry
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PreparedChosen

/-!
# Closing the original plane branch of the chosen-module alternatives

For the original local module of dimension two and cubic ratio one, the
faithful action has trivial two-core and is therefore the full symmetric
three group. The first isomorphism theorem identifies this image with the
literal quotient of M by its centralizer of the module, whose order is four.
The proved source 14.2.4 then supplies the rank-two hypothesis on the original
T, M, and residual.

The final consumer replaces the numeric-only first alternative in the
prepared chosen-module partition with this source rank-two conclusion.
It retains the original natural, omega, and prepared-subgroup alternatives.

Source: Aschbacher--Smith 15.1.2--3, printed pp.1084--1087, the rank-two
alternative, and 14.2.4, printed p.982.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition Chapter12.Section08 Chapter14.SourcePreliminaries
variable {G : Type*} [Group G] [Finite G]

/-- The numeric plane branch identifies the original module order and literal
centralizer quotient, using reducedness of its actual action image. -/
theorem source_localAction_plane_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    cubicRatio (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _))=1 →
    Module.finrank (ZMod 2) (Additive (localModule T M))=2 →
    Nat.card (localModule T M)=4 ∧
      Nonempty ((M⧸(centralizer (localModule T M : Set G)).subgroupOf M)≃*
        Equiv.Perm (Fin 3)) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro hq hd
  let V := localModule T M
  have hcard : Nat.card V=4 := by
    change Nat.card (Additive V)=4
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,hd]
    rfl
  obtain ⟨e⟩ := BinaryPlane.equiv_symmetricThree_of_finite_cubicRatio
    (imageRepresentation M V (le_normalizer_conjugateSpanBy _ _))
    (imageRepresentation_injective _ _ _) hd (source_localAction_twoCore hG T hM)
    (by rw [hq]; simp)
  refine ⟨hcard,⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq
    (actionHom_ker M V (le_normalizer_conjugateSpanBy _ _)).symm).trans
      (actionQuotientEquiv M V (le_normalizer_conjugateSpanBy _ _))).trans e

/-- The rank-two source setup follows from the plane numeric alternative. -/
theorem source_rankTwo_of_plane_numeric
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T=∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1<(maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G))={Mc}) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    cubicRatio (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _))=1 →
    Module.finrank (ZMod 2) (Additive (localModule T M))=2 →
    RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro hq hd
  obtain ⟨hcard,⟨e⟩⟩ := source_localAction_plane_quotient hG T hM hq hd
  exact Chapter14.Section02.source_lemma_14_2_4 hG T hempty hM hu hmany hcard e

/-- The original centralizing alternatives with their numeric plane branch
replaced by the proved rank-two hypothesis on the actual source residual. -/
theorem source_prepared_chosen_or_rankTwo
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T=∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1<(maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G)≤centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G))={Mc})
    (hne : M≠Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M ∨
    Nonempty (NaturalOrthogonalAction M V) ∨ SourceCases.Omega ρ ∨
    ∃ W : Subgroup G,
      (W=V ∨ ∃ U : Submodule (ZMod 2) (Additive V),
        SourceCases.Proper T M Mc V ρ U ∧
        W=(Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) ∧
      PreparedChosenModule T M W := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  rcases source_prepared_chosen_alternatives hG T hempty hM hmany hJ hu hne with
    hsmall | hother
  · exact Or.inl (source_rankTwo_of_plane_numeric hG T hempty hM hmany hu hsmall.1 hsmall.2)
  · exact Or.inr hother

end CFSG.Quasithin.Chapter15.Section01
