module

public import Theory.GroupTheory.SylowCentralFusionWitness

/-!
# Normalizer selections for central fusion

The subgroup selection in Glauberman's Lemma 1 is separate from its odd-order
mover. `NormalizerSelection` records containment, the exact Sylow normalizer
map, and nontrivial normalizer action. The shared local argument upgrades these
data to `Witness` without changing the selected subgroup.

`NoncentralNormalClosureSelection` is the remaining selection obligation when
a conjugate of the central involution in the given Sylow subgroup is not central
there. It is an explicit proposition, not an existence assertion.

Source: G. Glauberman, “On the automorphism group of a finite group having no
non-identity normal subgroups of odd order”, Math. Z. 93 (1966), Lemma 1,
pp.155–156, DOI 10.1007/BF01111033.
-/

public section
namespace SylowCentralFusion
open Subgroup
universe u
variable {G : Type u} [Group G]

/-- The subgroup-selection part of the fusion lemma, before adjusting the mover. -/
structure NormalizerSelection (T : Sylow 2 G) (z : G) where
  subgroup : Subgroup G
  le_sylow : subgroup ≤ (T : Subgroup G)
  mem_subgroup : z ∈ subgroup
  normalizer_sylow : ∃ R : Sylow 2 (normalizer (subgroup : Set G)),
    (R : Subgroup (normalizer (subgroup : Set G))).map
      (normalizer (subgroup : Set G)).subtype =
        (T : Subgroup G) ⊓ normalizer (subgroup : Set G)
  moves : ∃ g ∈ normalizer (subgroup : Set G), g * z * g⁻¹ ≠ z

/-- The noncentral-conjugate branch of the normal-closure selection.
Its other branch follows from Burnside fusion in the center of a Sylow subgroup. -/
@[expose] def NoncentralNormalClosureSelection : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (z : G),
    orderOf z = 2 → z ∈ (T : Subgroup G) →
    (∀ t ∈ (T : Subgroup G), t * z = z * t) →
    (∃ g : G, g * z * g⁻¹ ∈ (T : Subgroup G) ∧
      g * z * g⁻¹ ∉ centralizer (T : Set G)) →
    ∃ s : NormalizerSelection T z,
      s.subgroup ≤ normalClosure ({z} : Set G)

end SylowCentralFusion
