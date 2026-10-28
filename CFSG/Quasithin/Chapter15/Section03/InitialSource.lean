module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.LocalAction

/-!
# Source 14.1.3 and 14.1.6 at the original Chapter 15 boundary

The full known-simple QTKE hypotheses and the actual empty family L_f(G,T)
now imply solvable-residual centralization of every reduced module and of
the Chapter 15 conjugate-span module. The distinguished Mc has exactly the
maximal local components, with their literal unique-overgroup conclusions.
The action quotient used by Section 15.3 is consequently solvable.

Only genuine universal earlier Theorems A and C remain explicit. This does
not assert Theorem 15.1.3's natural orthogonal alternative, the subsequent
local geometry, or the six-model conclusion of 15.3.1.
Source: Aschbacher–Smith, printed pp.976–977 and 1120–1121.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- All three clauses of source 14.1.6, with the actual source families,
reduced modules and subgroup inclusions. -/
theorem source_lemma_14_1_6
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (Mc : Subgroup G) (hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    (∀ M ∈ maximalTwoLocalOvergroups (T : Subgroup G), ∀ U : Subgroup M,
      IsPReduced 2 U → solvableResidual M ≤ centralizer (U : Set M)) ∧
    (Chapter1.LStar G (T : Subgroup G) = Chapter1.cComponentsIn Mc ∧
      ∀ L ∈ Chapter1.cComponentsIn Mc,
        maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) = {Mc}) ∧
    (∀ H ∈ Chapter1.HOver G (T : Set G),
      (solvableResidual H).map H.subtype ≤ centralizer (centralInvolutions T : Set G) ∧
        centralizer (centralInvolutions T : Set G) ≤ Mc) := by
  refine ⟨?_, ⟨maximal_local_components_eq hA hC hG T hempty hMc hunique, ?_⟩, ?_⟩
  · intro M hM U hU
    exact residual_le_centralizer_reduced hA hC hG T hempty
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1, hM.2⟩ U hU
  · intro L hL
    exact component_unique_maximal_overgroup hA hC hG T hempty hMc hunique hL
  · intro H hH
    exact ⟨residual_le_centralizer_Z hA hC hG T hempty hH, centralizer_le_partner T hunique⟩

end CFSG.Quasithin.Chapter15.Section03.InitialSource
