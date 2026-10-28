module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.CompiledMarkedActions
public import Theory.SpecificGroups.Held.Model.FourPointBase

/-!
# Held double-coset transition checks through compiled actions

The certified action values feed the existing four-point base for actual Held
elements. Every returned factorization retains the two subgroup-membership
proofs. Source: `CompiledMarkedActions` and `Theory.GroupTheory.DoubleCosetTransitions`.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.CompiledActions
open Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification

/-- Compiled point checks recover the unchanged factorization in Held. -/
public theorem transition_eq_of_images (j k : Fin 4831) (i : Fin 3) (e : Bool)
    (l r : Fin 1024)
    (h : ∀ p : Fin 4,
      representativeAction j (seed i e p) =
        subgroupAction l (representativeAction k (subgroupAction r ⟨p.val, by omega⟩))) :
    representative j * middle i e * move i =
      subgroupElement l * representative k * subgroupElement r := by
  apply Held.eq_of_four_point_images
  intro p
  have hp := h p
  rw [representativeAction_eq j, representativeAction_eq k,
    subgroupAction_eq r, subgroupAction_eq l, seed_eq] at hp
  simp only [representation.map_mul, Equiv.Perm.mul_apply] at hp ⊢
  with_reducible exact hp

/-- The two outer factors supplied by compiled checks lie in the marked subgroup. -/
public theorem covered_of_images (j k : Fin 4831) (i : Fin 3) (e : Bool)
    (l r : Fin 1024)
    (h : ∀ p : Fin 4,
      representativeAction j (seed i e p) =
        subgroupAction l (representativeAction k (subgroupAction r ⟨p.val, by omega⟩))) :
    Theory.GroupTheory.DoubleCosetTransitions.Covered markedSubgroup representative
      (representative j * middle i e * move i) :=
  ⟨k, subgroupElement l, subgroupElement r, subgroupElement_mem l, subgroupElement_mem r,
    transition_eq_of_images j k i e l r h⟩

end Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.CompiledActions
