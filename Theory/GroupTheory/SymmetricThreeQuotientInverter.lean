module

public import Theory.GroupTheory.InvertedThreeLift
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# An inverted three-subgroup above an S₃ quotient

In a finite group with a normal two-subgroup and symmetric-three quotient,
every supplied involution outside the kernel inverts a subgroup of order
three. Compose the quotient map with its given isomorphism to S₃ and apply
the product-of-conjugate-involutions construction in `InvertedThreeLift`.

This is the quotient form of the inverted-subgroup step in Parrott,
“A Characterization of the Tits' Simple Group” (1972), p. 676.
-/

namespace Subgroup

/-- An involution outside a two-kernel with quotient S₃ inverts a three-subgroup. -/
public theorem exists_inverted_three_of_symmetric_three_quotient
    {N : Type*} [Group N] [Finite N]
    (K : Subgroup N) [K.Normal] (hK : IsPGroup 2 K)
    (he : Nonempty ((N ⧸ K) ≃* Equiv.Perm (Fin 3)))
    (w : N) (hw : orderOf w = 2) (hwK : w ∉ K) :
    ∃ Q : Subgroup N, Nat.card Q = 3 ∧ ∀ q ∈ Q, w * q * w⁻¹ = q⁻¹ := by
  obtain ⟨e⟩ := he
  let f := e.toMonoidHom.comp (QuotientGroup.mk' K)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective K)
  have hker : f.ker = K := by
    ext x
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ K
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff x).mp (e.injective (hx.trans e.map_one.symm))
    · intro hx
      rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]
  have hw2 : w ^ 2 = 1 := hw ▸ pow_orderOf_eq_one w
  have hfw : f w ≠ 1 := fun h => hwK (hker ▸ (show w ∈ f.ker from h))
  obtain ⟨Q, hQ, _, _, _, hinv⟩ :=
    exists_inverted_three_lift_of_two_kernel f hf (hker.symm ▸ hK) w hw2 hfw
  exact ⟨Q, hQ, hinv⟩

end Subgroup
