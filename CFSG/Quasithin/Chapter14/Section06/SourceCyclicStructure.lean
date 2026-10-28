module
public import CFSG.Quasithin.Chapter14.Section06.SourceCyclicModels
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.IndexFiveStructure

/-!
# The quintic closure in the original odd-core reduction

The cyclic primitive residual gives an original Sylow index of three or
five. Cubic recognition closes the former. In the latter the actual
index-five source theorem makes the original closure elementary abelian
of order32 or64 and marks the quotient as D10 or Sz(2). The F.1.1 pair
is unchanged. Applying this to the minimal subgroup selected inside an
odd-core counterexample supplies the concrete module input for the remaining
quintic recognition branch.

Source: Aschbacher--Smith14.6.11--12(2), printed pp.1030--1031, referring
to14.2.20 and14.3.5. Quintic amalgam recognition remains independent.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab

/-- The original cyclic residual either gives an E model or the literal
quintic amalgam with its source elementary closure and exact order alternatives. -/
theorem source_solvable_minimal_cyclic_model_or_quintic_closure
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    (hcyc : IsCyclic (pResidual 2 (J ⧸ pCore 2 J))) :
    ClassificationModels.IsTheoremEModel G ∨
      ((T : Subgroup G).relIndex J = 5 ∧
        ChapterF.Source.HypothesisF11
          ![J, sourceResidual M Mc ⊔ (T : Subgroup G)] (T : Subgroup G) ∧
        IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J) ∧
        (Nat.card (conjugateSpanBy (localModule T M) J) = 32 ∨
          Nat.card (conjugateSpanBy (localModule T M) J) = 64)) := by
  rcases source_solvable_minimal_cyclic_model_or_quintic
    hG T hempty hM hu hmany hcard e hab J hJ hs hcyc with hm | ⟨hi,hf⟩
  · exact Or.inl hm
  · obtain ⟨hU,horder⟩ := Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e J hJ.1 hi
    exact Or.inr ⟨hi,hf,hU,horder⟩

/-- The minimal group selected from an actual odd-core counterexample has
noncyclic residual or the original quintic closure of order32 or64. -/
theorem source_oddCore_counterexample_noncubic_structure
    (hnomodel : ¬ ClassificationModels.IsTheoremEModel G)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ (J : Subgroup G), J ∈ Chapter3.HStar (T : Subgroup G) M ∧
      J ≤ H ∧ Group.IsSolvable J ∧
      (¬ IsCyclic (pResidual 2 (J ⧸ pCore 2 J)) ∨
        ((T : Subgroup G).relIndex J = 5 ∧
          ChapterF.Source.HypothesisF11
            ![J, sourceResidual M Mc ⊔ (T : Subgroup G)] (T : Subgroup G) ∧
          IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J) ∧
          (Nat.card (conjugateSpanBy (localModule T M) J) = 32 ∨
            Nat.card (conjugateSpanBy (localModule T M) J) = 64))) := by
  obtain ⟨J,hJH,hJ,hs⟩ := source_solvable_minimal_outside_of_oddCore
    hG T hempty hM hu hmany hcard e hab H hH hne
  refine ⟨J,hJ,hJH,hs,?_⟩
  by_cases hc : IsCyclic (pResidual 2 (J ⧸ pCore 2 J))
  · exact Or.inr ((source_solvable_minimal_cyclic_model_or_quintic_closure
      hG T hempty hM hu hmany hcard e hab J hJ hs hc).resolve_left hnomodel)
  · exact Or.inl hc

end CFSG.Quasithin.Chapter14.Section06
