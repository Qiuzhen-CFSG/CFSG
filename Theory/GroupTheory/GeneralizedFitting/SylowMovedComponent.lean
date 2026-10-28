module
public import Theory.GroupTheory.GeneralizedFitting.SylowComponentOrbit

/-!
# Commutator generation from a Sylow-normal actor

If an actor moves a component, the component commutator dichotomy places
that component inside the commutator of its normal orbit with the actor.
A Sylow two-subgroup normalizing the actor normalizes this commutator.
When the component has at most two conjugates, its Sylow orbit is already
its full normal orbit. Thus the commutator is the entire normal orbit.

Source: Aschbacher--Smith G.10.9--10, printed p.360.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Sylow normalization propagates nontrivial action on one component across
its entire normal orbit, when that orbit has size at most two. -/
theorem IsComponent.normalOrbit_eq_commutator_of_sylow_normalizes
    {L : Subgroup G} (hL : IsComponent G L) (S : Sylow 2 G) (X : Subgroup G)
    (hnX : (S : Subgroup G) ≤ normalizer (X : Set G))
    (hi : (normalizer (L : Set G)).index ≤ 2) (hm : ⁅L,X⁆ ≠ ⊥) :
    ⁅componentOrbit L ⊤,X⁆ = componentOrbit L ⊤ := by
  have hidx : L.Normal ∨ (normalizer (L : Set G)).index = 2 := by
    by_cases h1 : (normalizer (L : Set G)).index = 1
    · left
      exact normalizer_eq_top_iff.mp (index_eq_one.mp h1)
    · right
      have hp := (normalizer (L : Set G)).index_ne_zero_of_finite
      omega
  let N := componentOrbit L ⊤
  have hN : (⊤ : Subgroup G) ≤ normalizer (N : Set G) :=
    le_normalizer_componentOrbit L ⊤
  have hSN := componentOrbit_normal_of_normal_or_index_two L S hidx
  let := hSN
  have he : componentOrbit L (S : Subgroup G) = N := by
    apply le_antisymm
    · apply iSup_conjugates_le_of_le_normalizer L (S : Subgroup G) N
        (le_componentOrbit L ⊤) (le_top.trans hN)
    · apply iSup_conjugates_le_of_le_normalizer L ⊤ _ (le_componentOrbit L _)
      rw [normalizer_eq_top]
  have hDX : (S : Subgroup G) ≤ normalizer (⁅N,X⁆ : Subgroup G) := by
    intro s hs
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hN (mem_top s)),
      mem_normalizer_iff_map_conj_eq.mp (hnX hs)]
  have hLD : L ≤ ⁅N,X⁆ := by
    have hd := (hL.commutator_dichotomy X).resolve_left hm
    change ⁅L,X⁆ = componentOrbit L X at hd
    exact (hd.symm ▸ le_componentOrbit L X).trans
      (commutator_mono (le_componentOrbit L ⊤) le_rfl)
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp (le_top.trans hN)
  · exact he.symm.le.trans
      (iSup_conjugates_le_of_le_normalizer L (S : Subgroup G) ⁅N,X⁆ hLD hDX)

end Theory.GroupTheory
