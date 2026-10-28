module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.NaturalModels.Intersections
public import CFSG.Quasithin.Chapter14.Section02.RankTwoEntry
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The noncentral branch of the original reduction 15.1.3

The source 14.1.7 alternatives describe the conjugation action on the
literal module V(M). In the plane case, the two presentations of its
centralizer in M agree. The natural SL₂(2) quotient therefore gives the
actual S₃ quotient required by 14.1.18 and the rank-two construction
14.2.4. The other alternative retains the full orthogonal action.

Thus a failure of both the rank-two setup and the orthogonal alternative
forces J(T) to centralize V(M), exactly the first reduction in 15.1.9.
No classification of that centralizing branch is asserted here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
14.1.7 and 14.2.4, pp.977 and 982; 15.1.3 and 15.1.9, pp.1086 and 1088.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter14.SourcePreliminaries Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The genuine noncentral branch supplies the original rank-two input,
or the full natural orthogonal action, on the same selected local module. -/
theorem source_noncentral_rankTwo_or_orthogonal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : M ≠ Mc)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G)) :
    (Nat.card (localModule T M) = 4 ∧
      Nonempty ((M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
        Equiv.Perm (Fin 3)) ∧
      RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M) ∨
      Nonempty (NaturalOrthogonalAction M (localModule T M)) := by
  let hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1, hM.1.2⟩
  let U := (localModule T M).subgroupOf M
  let := (localModule_reduced_from_source hG T hH).normal
  let := (localModule_reduced_from_source hG T hH).elementary
  rcases local_14_1_7_from_source
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
      hG T hempty hM.1 hu (Or.inl hne) hJ with h | h
  · obtain ⟨c, e, _, hcard, _, _⟩ := h
    have heC : centralizer (U : Set M) =
        (centralizer (localModule T M : Set G)).subgroupOf M := by
      apply map_injective M.subtype_injective
      rw [map_centralizer_subtype,
        map_subgroupOf_eq_of_le (localModule_le T hM.1.2), subgroupOf_map_subtype]
      exact inf_comm _ _
    obtain ⟨eS⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    let e' := (QuotientGroup.quotientMulEquivOfEq heC.symm).trans (e.trans eS)
    exact Or.inl ⟨hcard, ⟨e'⟩,
      Chapter14.Section02.source_lemma_14_2_4 hG T hempty hM hu hmany hcard e'⟩
  · exact Or.inr h.1

/-- The original counterexample reduction at the start of 15.1.9:
after the rank-two and orthogonal branches, J(T) centralizes V(M). -/
theorem source_thompson_centralizes_of_no_natural_branch
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : M ≠ Mc)
    (hplane : ¬ RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (horthogonal : ¬ Nonempty (NaturalOrthogonalAction M (localModule T M))) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) := by
  by_contra hJ
  rcases source_noncentral_rankTwo_or_orthogonal hG T hempty hM hu hmany hne hJ with h | h
  · exact hplane h.2.2
  · exact horthogonal h

end CFSG.Quasithin.Chapter15.Section01
