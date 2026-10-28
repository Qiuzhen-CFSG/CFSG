module

public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.GroupTheory.SylowNormalizerFrattini
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer

/-!
# Self-normalization of the full triality parabolics

The positive subgroup is Sylow in each full parabolic. Frattini's argument
puts its normalizer in the join of the parabolic and the positive-subgroup
normalizer, which is the Borel. This proves self-normalization at every
positive binary exponent, including q = 2.

Source: GLS3 §§2.3--2.6, the full parabolics of the concrete BN-pair.
-/

public section
namespace Triality.Standard.Parabolics
open Subgroup

theorem normalizer_parabolic_binary (P : Parameters) (hp : P.prime = 2)
    (a : Node) : normalizer (parabolic P a : Set (Carrier P)) = parabolic P a := by
  have hU : (unipotentSylow P hp : Subgroup (Carrier P)) ≤ parabolic P a :=
    (unipotent_le_borel P).trans (borel_le_parabolic P a)
  apply le_antisymm
  · have h := le_normalizer_sylow_sup (parabolic P a)
      (normalizer (parabolic P a : Set (Carrier P)))
      (parabolic P a).le_normalizer le_rfl ((unipotentSylow P hp).subtype hU)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hU, coe_unipotentSylow,
      ConcreteBruhat.normalizer_unipotent_eq_borel P hp] at h
    exact h.trans (sup_le (borel_le_parabolic P a) le_rfl)
  · exact (parabolic P a).le_normalizer

end Triality.Standard.Parabolics
