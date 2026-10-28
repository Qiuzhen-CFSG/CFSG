module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperOrbitFactors
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ClassifiedNoThree
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.ReducibleEndpoints
public import Theory.Representation.BinaryOrthogonalOmegaIrreducible
/-!
# Actual reducible factors in the proper orbit branch

The marked natural omega four-space is irreducible, and the original
centralizer partner excludes the three-plane factor. A reducible literal
factor consequently has cyclic starred actors, so the genuine cyclic
D.2.17 source producer supplies its marked odd kernel and involution.

Source: Aschbacher--Smith 15.1.2, printed p.1085.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_reducible_factor_cyclic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ i, ¬ IsIrreducible (d.factor i).action →
      ∀ A ∈ QhatStar (d.factor i).action, IsCyclic A := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let f := actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd i hi A hA
  by_contra hncyc
  have hr : 1 < rank A := by
    have hp := hA.1.2.1.rank_pos
    by_contra hn
    have hr : rank A = 1 := by omega
    have hc : Nat.card A = 2 := by rw [hA.1.2.1.card_eq_two_pow_rank,hr]; norm_num
    exact hncyc (isCyclic_of_prime_card hc)
  let F := d.factor i
  let j : F.Carrier →* D := (Jhat ρ).subtype.comp F.embedding.groupMap
  let : Group.IsSolvable F.Carrier := Group.isSolvable_of_isSolvable_injective
    (f := j) ((Jhat ρ).subtype_injective.comp F.embedding.group_injective)
  obtain ⟨B,r,hB,hrB⟩ := c.factor_cover d
    (Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1))
    f.rangeRestrict f.rangeRestrict_surjective i
  have hend := (SourceReduction.source_lemma_D_2_22 F.action hB r hrB F.faithful hA hr
    (generalizedFitting_eq_fitting_of_solvable F.Carrier)
    (c.factor_twoCore d (source_localAction_twoCore hG T hM) i) (hd i) F.generated).2.2.2
  rcases hend with ⟨_,_,c',e,hc⟩ | ⟨hsix,_⟩
  · exact hi (irreducible_of_binaryOmega_coordinates F.action c' e hc)
  · exact source_localAction_factor_noncyclic_finrank_ne_six hG T hempty hM hmany hJ
      hu hne U c d hd i A hA hr hsix

 theorem source_localAction_reducible_factor_localGeneration
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ i, ¬ IsIrreducible (d.factor i).action →
      Nonempty (CyclicSource.LocalGeneration (d.factor i).action) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let f := actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd i hi
  exact c.factor_cyclic_localGeneration d (source_localAction_twoCore hG T hM)
    (source_centralizing_cubicRatio_le_two hG T hempty hM hmany hJ) hd
    (Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1))
    f.rangeRestrict f.rangeRestrict_surjective i
    (source_localAction_reducible_factor_cyclic hG T hempty hM hmany hJ hu hne U c d hd i hi)
/-- The original reducible factor retains its precise marked cyclic endpoint. -/
theorem source_localAction_reducible_factor_endpoints
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ i, ¬ IsIrreducible (d.factor i).action →
    ∃ l : CyclicSource.LocalGeneration (d.factor i).action,
      letI := BinaryGroupAction.action (d.factor i).action
      letI : Finite (d.factor i).Space := Module.finite_of_finite (ZMod 2)
      letI : IsElementaryAbelian 2 (Multiplicative (d.factor i).Space) := BinaryGroupAction.elementary
      letI := l.normal
      (ChapterD.Section02.CyclicThreeEndpoint (V := Multiplicative (d.factor i).Space)
        l.kernel l.involution ∧ Module.finrank (ZMod 2) (d.factor i).Space = 4) ∨
        ChapterD.Section02.ElementaryNineEndpoint (V := Multiplicative (d.factor i).Space)
          l.kernel l.involution := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d hd i hi
  obtain ⟨l⟩ := source_localAction_reducible_factor_localGeneration hG T hempty hM hmany hJ
    hu hne U c d hd i hi
  exact ⟨l,l.endpoints_of_not_irreducible (d.factor i).faithful hi⟩

end CFSG.Quasithin.Chapter15.Section01
