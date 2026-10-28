module

public import CFSG.Quasithin.Chapter4.Section04.OddActorLargeComponent
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Action

/-!
# Full component action for a large chosen module

Fixed-residual uniqueness makes the odd normalizer's two-core trivial.
The large-module component-selection theorem then supplies a component
outside N(L). Both the residual and V normalize it; its nontrivial
V-commutator is consequently the whole component. The Mathieu Hall
consumer retains these literal inclusions and the inherited simple class.

Uniqueness is an explicit earlier-source premise here, not a conclusion.
Source: Aschbacher--Smith, 4.4.9--10, printed pp.620--621.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04
variable {G : Type*} [Group G] [Finite G]

/-- Apply component selection using genuine uniqueness of the fixed residual. -/
theorem chosen_oddNormalizer_exists_moved_component_of_large
    {κ : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 κ T L)
    (D : Chapter12.Section02.ChosenModule T L V) (hcard : 8 < Nat.card V)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAN : A ≤ normalizer (L : Set G)) (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2)
    (hodd : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G))
    (hunique : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ ≠ ⊥ ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ IsQuasithin K ∧ κ (K ⧸ center K) :=
  chosen_oddNormalizer_exists_moved_component_of_large_module h D hcard A hne
    hAN hcomm hodd hAV (oddNormalizer_reduction_of_cover_uniqueness D A hunique hout).2

/-- The source data produce a component outside N(L) with full V-commutator. -/
theorem chosen_oddNormalizer_exists_full_component_action_of_large
    {κ : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 κ T L)
    (D : Chapter12.Section02.ChosenModule T L V) (hcard : 8 < Nat.card V)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAN : A ≤ normalizer (L : Set G)) (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2)
    (hodd : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G))
    (hunique : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ IsQuasithin K ∧ κ (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      V.subgroupOf (normalizer (A : Set G)) ≤ normalizer (K : Set (normalizer (A : Set G))) := by
  obtain ⟨K,hK,hm,houtK,hcore,hqt,hclass⟩ := chosen_oddNormalizer_exists_moved_component_of_large
    h D hcard A hne hAN hcomm hodd hAV hunique hout
  obtain ⟨_,hFK,hVK⟩ := chosen_oddNormalizer_component_normalization h D A hAN hcomm hodd hAV K hK
  exact ⟨K,hK,hK.commutator_eq_self_of_normalizes hVK hm,houtK,hcore,hqt,hclass,hFK,hVK⟩

end CFSG.Quasithin.Chapter4.Section04
