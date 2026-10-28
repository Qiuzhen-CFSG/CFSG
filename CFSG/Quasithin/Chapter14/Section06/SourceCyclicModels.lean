module
public import CFSG.Quasithin.Chapter14.Section06.SourceCyclicResidual
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.OriginalCubic
/-!
# The cubic residual branch reaches the original Theorem E models

The cyclic primitive odd residual has original Sylow index three or five.
The now proved cubic recognition closes the first branch in the ambient
simple group. The remaining quintic branch retains the literal F.1.1 pair;
its independent asymmetric recognition is not assumed here.

The second theorem applies this distinction to the actual odd-core
counterexample. Outside the Theorem E models, the selected minimal group
has either noncyclic residual or index five with the original amalgam.
Source: Aschbacher--Smith14.6.12(2), using14.3.5 and14.2.20(2).
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
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


/-- The cubic half of the cyclic residual is discharged by ambient recognition. -/
theorem source_solvable_minimal_cyclic_model_or_quintic
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    (hcyc : IsCyclic (pResidual 2 (J ⧸ pCore 2 J))) :
    ClassificationModels.IsTheoremEModel G ∨
      ((T : Subgroup G).relIndex J = 5 ∧
        ChapterF.Source.HypothesisF11
          ![J, sourceResidual M Mc ⊔ (T : Subgroup G)] (T : Subgroup G)) := by
  rcases source_solvable_minimal_cyclic_residual_small_index
    hG T hempty hM hu hmany hcard e hab J hJ hs hcyc with hc | hq
  · exact Or.inl (Section02.SolvableAmalgam.source_theoremE_of_index_three
      hG T hempty hM hu hmany hcard e J hJ.1.1 hJ.1.2 hc)
  · exact Or.inr ⟨hq,source_solvable_minimal_cyclic_residual_amalgam
      hG T hempty hM hu hmany hcard e hab J hJ hs hcyc⟩

/-- The actual14.6.11 counterexample has no remaining cubic residual branch. -/
theorem source_oddCore_counterexample_noncubic
    (hnomodel : ¬ ClassificationModels.IsTheoremEModel G)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ (J : Subgroup G), J ∈ Chapter3.HStar (T : Subgroup G) M ∧
      J ≤ H ∧ Group.IsSolvable J ∧
      (¬ IsCyclic (pResidual 2 (J ⧸ pCore 2 J)) ∨
        ((T : Subgroup G).relIndex J = 5 ∧
          ChapterF.Source.HypothesisF11
            ![J, sourceResidual M Mc ⊔ (T : Subgroup G)] (T : Subgroup G))) := by
  obtain ⟨J,hJH,hJ,hs⟩ := source_solvable_minimal_outside_of_oddCore
    hG T hempty hM hu hmany hcard e hab H hH hne
  refine ⟨J,hJ,hJH,hs,?_⟩
  by_cases hc : IsCyclic (pResidual 2 (J ⧸ pCore 2 J))
  · exact Or.inr ((source_solvable_minimal_cyclic_model_or_quintic
      hG T hempty hM hu hmany hcard e hab J hJ hs hc).resolve_left hnomodel)
  · exact Or.inl hc

end CFSG.Quasithin.Chapter14.Section06
