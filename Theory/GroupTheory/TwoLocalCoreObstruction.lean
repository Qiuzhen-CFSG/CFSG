module

public import Theory.Quasithin
public import Theory.PGroupCore
import Mathlib.Order.Preorder.Finite

/-!
# Unique two-local overgroups and trivial two-cores

A subgroup with a nontrivial two-core lies in a maximal two-local subgroup:
normalize the ambient image of its two-core, then use finiteness. Consequently,
if `A` has only one maximal two-local overgroup `M`, adjoining a subgroup outside
`M` gives a group with trivial two-core.

This is the local-overgroup argument used in Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined manuscript of 1 March 2004, §14.2, in the
construction preceding Lemma 14.2.21 (printed p. 988).
-/

namespace Theory.GroupTheory

open Subgroup

/-- A nontrivial two-core supplies a maximal two-local overgroup. -/
public theorem exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hH : pCore 2 H ≠ ⊥) :
    ∃ M : Subgroup G, IsMaximalTwoLocal M ∧ H ≤ M := by
  let Q := (pCore 2 H).map H.subtype
  have hQ : Q ≠ ⊥ := by
    exact fun h => hH (((pCore 2 H).map_eq_bot_iff_of_injective
      H.subtype_injective).mp h)
  have hloc : IsTwoLocal (normalizer (Q : Set G)) :=
    ⟨Q, hQ, pCore_isPGroup.map H.subtype, rfl⟩
  have hHN : H ≤ normalizer (Q : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 H).le_normalizer_map H.subtype
  obtain ⟨M, hNM, hmax⟩ := Finite.exists_le_maximal hloc
  exact ⟨M, hmax, hHN.trans hNM⟩

/-- Leaving the unique maximal two-local overgroup forces the generated
subgroup to have trivial two-core. No simplicity hypothesis is needed. -/
public theorem twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup
    {G : Type*} [Group G] [Finite G] (A B M : Subgroup G)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → A ≤ K → K = M)
    (hBM : ¬ B ≤ M) : pCore 2 (A ⊔ B : Subgroup G) = ⊥ := by
  by_contra hcore
  obtain ⟨K, hK, hABK⟩ :=
    exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot (A ⊔ B) hcore
  have hKM := hunique K hK (le_sup_left.trans hABK)
  exact hBM (hKM ▸ le_sup_right.trans hABK)

end Theory.GroupTheory
