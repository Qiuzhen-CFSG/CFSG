module

public import Theory.Mathieu.M12.SylowOvergroups.Transversal

/-!
# Exhaustive marked Sylow double-coset coverage in M₁₂

The checked transversal supplies 1,485 different cosets, which is the full
index 95,040/64 of the actual marked Sylow subgroup. Finiteness therefore makes
the transversal surjective. Factoring a general element through its coset gives
the required two Sylow factors and one of the 44 representatives.

This discharges the enumeration premise used in the prime-order obstruction
argument for Aschbacher–Smith, Proposition 1.3.4, printed p.511.
-/

public section
namespace Sporadic.Mathieu.M12SmallPair.SylowOvergroups

theorem card_sylowCosets : Nat.card (M12 ⧸ sylowCandidate) = 1485 := by
  have h := sylowCandidate.card_mul_index
  rw [card_sylowCandidate, m12_order, Subgroup.index_eq_card] at h
  omega

theorem transversal_cosets_surjective : Function.Surjective
    (fun j : Fin 1485 => (QuotientGroup.mk (transversal j) : M12 ⧸ sylowCandidate)) := by
  apply ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨transversal_cosets_injective, ?_⟩).surjective
  rw [Nat.card_fin, card_sylowCosets]

/-- Every element lies in one of the proposed Sylow double cosets. -/
theorem covers : Covers := by
  intro g
  obtain ⟨j, hj⟩ := transversal_cosets_surjective (QuotientGroup.mk g)
  have ht : (transversal j)⁻¹ * g ∈ sylowCandidate :=
    QuotientGroup.eq.mp hj
  refine ⟨(transversalParam j).1,
    SylowAutomorphismGroup.element (transversalParam j).2,
    ⟨(transversal j)⁻¹ * g, ht⟩, ?_⟩
  change transversal j * ((transversal j)⁻¹ * g) = g
  exact mul_inv_cancel_left _ _

end Sporadic.Mathieu.M12SmallPair.SylowOvergroups
