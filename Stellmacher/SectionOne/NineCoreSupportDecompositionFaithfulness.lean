module

public import Stellmacher.SectionOne.NineCoreSupportDecompositionTransport

/-!
# Faithfulness of the restricted support action

Ambient faithfulness implies faithfulness of the canonical action of every
subgroup. In particular, the elementary-nine supporting-line count does not
need a separate restricted-faithfulness hypothesis. An action factoring
through a quotient with nontrivial kernel cannot satisfy ambient faithfulness.
-/

@[expose] public section

namespace Stellmacher.SectionOne

theorem nineCoreSupportDecomposition_restricted_faithful
    {K V : Type*} [Group K] [MulAction K V]
    (core : Subgroup K)
    (hfaith : fixingSubgroup K (Set.univ : Set V) = ⊥) :
    fixingSubgroup core (Set.univ : Set V) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro actor hactor
  have hambient : (actor : K) ∈ fixingSubgroup K (Set.univ : Set V) := by
    rw [mem_fixingSubgroup_iff] at hactor ⊢
    exact hactor
  have hone : (actor : K) = 1 := by
    simpa [hfaith] using hambient
  exact Subgroup.mem_bot.mpr (Subtype.ext hone)

theorem nineCoreSupportDecomposition_kernel_core_eq_bot
    {K V : Type*} [Group K] [MulAction K V]
    (core : Subgroup K)
    (hfaith : fixingSubgroup K (Set.univ : Set V) = ⊥)
    (htrivial : ∀ actor : core, ∀ value : V, actor • value = value) :
    core = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro actor hactor
  have hfix : actor ∈ fixingSubgroup K (Set.univ : Set V) := by
    rw [mem_fixingSubgroup_iff]
    intro value _
    exact htrivial ⟨actor, hactor⟩ value
  simpa [hfaith] using hfix

end Stellmacher.SectionOne
