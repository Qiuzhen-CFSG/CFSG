module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowFixedLine
public import Theory.Representation.BinaryOffender.Defs

/-!
# The Sylow fixed space of the natural A₆ module

The existing invariant-line theorem puts every Sylow-fixed vector on the
line of any nonzero fixed vector. That binary line has two elements, so
this proves the bound without enumerating vectors or Sylow subgroups.
The representation is the literal natural quotient of the six-letter core.

Source: Aschbacher–Smith, B.3.4 and 13.4.10(5), pp.84–85 and909.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation

/-- Every A₆ Sylow subgroup fixes at most two vectors of the natural module. -/
theorem six_natural_sylow_fixed_card_le_two (P : Sylow 2 (alternatingGroup (Fin 6))) :
    Nat.card (fixedSpace (BinaryPermutation.alternatingNaturalRepresentation (Fin 6))
      (P : Subgroup (alternatingGroup (Fin 6)))) ≤ 2 := by
  let ρ := BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
  let F := fixedSpace ρ (P : Subgroup (alternatingGroup (Fin 6)))
  by_cases hF : F = ⊥
  · change Nat.card F ≤ 2
    rw [hF, Nat.card_unique]
    decide
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hF
  have hle : F ≤ Submodule.span (ZMod 2) {v} := by
    intro w hw
    apply Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.fixed_vectors_le_span
      (alternatingGroup (Fin 6)) le_rfl P v hv0
    · rintro a ⟨b,hb,rfl⟩
      exact hv ⟨b,hb⟩
    · rintro a ⟨b,hb,rfl⟩
      exact hw ⟨b,hb⟩
  have hc := Nat.card_le_card_of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)
  have hb : Nat.card (Submodule.span (ZMod 2) {v}) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      finrank_span_singleton hv0]
    decide
  exact hc.trans_eq hb

end BinaryPermutation
