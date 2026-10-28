module
public import Theory.SpecificGroups.AlternatingSix.CentralThreeNonfusionSplit
public import Theory.GroupTheory.Gaschutz
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Splitting the full cubic extension from its index-two centralizer

The actual nonfusion pair splits the central cubic kernel inside its
index-two overgroup. Gaschütz then gives a complement to the same full
kernel in the whole group because its order three is coprime to that index.
This applies even though the kernel is inverted outside the centralizer.
-/

public noncomputable section
open Subgroup
namespace AlternatingSix.CentralThreeNonfusionSplit

/-- Lift the source nonfusion splitting across the actual index-two overgroup. -/
theorem exists_complement_of_index_two_nonfusion
    {N : Type*} [Group N] [Finite N] (V H : Subgroup N) [V.Normal]
    (hV : Nat.card V = 3) (hVH : V ≤ H) (hH : H.index = 2)
    (hc : V.subgroupOf H ≤ center H)
    (e : (H ⧸ V.subgroupOf H) ≃* alternatingGroup (Fin 6))
    (x z : H) (hx : orderOf x = 3) (hxn : x ∉ V.subgroupOf H)
    (hz : z ∈ V.subgroupOf H) (hnf : ¬ IsConj x (z*x)) :
    ∃ K : Subgroup N, V.IsComplement' K := by
  let q : H →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (V.subgroupOf H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = V.subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkc : Nat.card q.ker = 3 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv,hV]
  have hqx : q x ≠ 1 := by
    intro hh
    apply hxn
    exact hk ▸ hh
  have hs := kernel_complement_of_nonfusion q hq (hk ▸ hc) hkc x hx hqx z (hk ▸ hz) hnf
  rw [hk] at hs
  let : IsCyclic V := isCyclic_of_prime_card hV
  let : IsMulCommutative V := inferInstance
  exact exists_complement_of_coprime_overgroup V H hVH
    (by rw [hV,hH]; decide) ⟨commutator H,hs⟩

end AlternatingSix.CentralThreeNonfusionSplit
