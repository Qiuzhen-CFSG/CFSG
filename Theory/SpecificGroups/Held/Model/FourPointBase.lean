module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.Preservation
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound.Separation
public import Theory.SpecificGroups.Held.Model.Basic

/-!
# A four-point base for the concrete Held carrier

The published Held graph has trivial pointwise stabilizer on vertices
0, 1, 2, 3, and the literal Held generators preserve this graph. Consequently,
two elements of the actual carrier are equal when they agree at these four
vertices. Apply the graph certificate to their quotient. This is an equality
test for the existing permutation model; no order or simplicity is assumed.

Source: the ATLAS HeG1-p2058B0 graph certificates in `SeventeenSylow.Preservation`
and `Normalizer.GraphCardBound.Separation`.
-/

namespace Held

/-- Equality in the actual Held carrier is detected on vertices 0, 1, 2, 3. -/
public theorem eq_of_four_point_images {x y : He}
    (h : ∀ i : Fin 4,
      representation x ⟨i.val, by omega⟩ = representation y ⟨i.val, by omega⟩) :
    x = y := by
  apply representation_injective
  have he : representation (y⁻¹ * x) = 1 := by
    apply NormalizerGraph.CardBound.four_fixed_eq_one
    · exact Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
        (y⁻¹ * x).property
    · intro z hz
      have hz' : representation x z = representation y z := h ⟨z.val, hz⟩
      change (representation y).symm (representation x z) = z
      rw [hz']
      exact (representation y).symm_apply_apply z
  exact (inv_mul_eq_one.mp (by simpa only [map_mul, map_inv] using he)).symm

end Held
