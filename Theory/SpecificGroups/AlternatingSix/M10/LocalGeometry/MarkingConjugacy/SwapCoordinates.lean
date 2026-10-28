module

public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.Coordinates

/-!
# Ordered transposition pairs over the standard nine-group

If the product of two transpositions inverts the standard nine-group, their
ordered pair is conjugate to `(standardZ, standardU)` by a permutation
normalizing that group. The conjugator is one of eighteen explicit choices:
an element of the nine-group, optionally followed by the permutation exchanging
its two three-letter supports. The finite calculation uses swap endpoints and
tests inversion only on the two specified three-cycles; all identities are
checked by the kernel.

This supplies the second step of simultaneous marking conjugacy for the local
geometry in Aschbacher, “A 2-local characterization of M12” (2003), 4.8–4.10,
pp.41–42. No distinctness or prescribed support assumption is imposed.
-/

@[expose] public section

namespace AlternatingSix.M10.LocalGeometry.MarkingConjugacy
open Subgroup

private def exchange : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5

private def candidate (i : NineCoordinates) (t : Bool) : Equiv.Perm (Fin 6) :=
  nineEmbedding i * if t then exchange else 1

private theorem candidate_preserves : ∀ (i : NineCoordinates) (t : Bool)
    (j : NineCoordinates), ∃ k : NineCoordinates,
      nineEmbedding k = candidate i t * nineEmbedding j * (candidate i t)⁻¹ := by
  decide +kernel

private theorem candidate_nine_eq (i : NineCoordinates) (t : Bool) :
    standardNine.map (MulAut.conj (candidate i t)).toMonoidHom = standardNine := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact candidate_preserves i t j
  · rw [card_map_of_injective (MulAut.conj (candidate i t)).injective]

private theorem swap_coordinate_coverage : ∀ a b c d : Fin 6,
    let z := Equiv.swap a b
    let u := Equiv.swap c d
    (u * z) * cycle₀ * (u * z)⁻¹ = cycle₀⁻¹ →
    (u * z) * cycle₁ * (u * z)⁻¹ = cycle₁⁻¹ →
    ∃ (i : NineCoordinates) (t : Bool),
      candidate i t * standardZ * (candidate i t)⁻¹ = z ∧
      candidate i t * standardU * (candidate i t)⁻¹ = u := by
  decide +kernel

/-- The standard nine-group's normalizer is transitive on the ordered
transposition pairs whose product acts by inversion. -/
theorem standard_pair_conjugacy (z u : Equiv.Perm (Fin 6))
    (hz : z.IsSwap) (hu : u.IsSwap)
    (hb : ∀ x ∈ standardNine, (u * z) * x * (u * z)⁻¹ = x⁻¹) :
    ∃ τ : Equiv.Perm (Fin 6),
      standardNine.map (MulAut.conj τ).toMonoidHom = standardNine ∧
      τ * standardZ * τ⁻¹ = z ∧ τ * standardU * τ⁻¹ = u := by
  have h₀ : cycle₀ ∈ standardNine :=
    ⟨(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0), by decide +kernel⟩
  have h₁ : cycle₁ ∈ standardNine :=
    ⟨(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1), by decide +kernel⟩
  obtain ⟨a, b, _, rfl⟩ := hz
  obtain ⟨c, d, _, rfl⟩ := hu
  obtain ⟨i, t, hz, hu⟩ := swap_coordinate_coverage a b c d
    (hb cycle₀ h₀) (hb cycle₁ h₁)
  exact ⟨candidate i t, candidate_nine_eq i t, hz, hu⟩

end AlternatingSix.M10.LocalGeometry.MarkingConjugacy
