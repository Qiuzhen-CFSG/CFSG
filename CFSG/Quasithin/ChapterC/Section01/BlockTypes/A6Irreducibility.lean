module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ModuleIrreducibility
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport

/-!
# Irreducibility of the intrinsic natural alternating-six block module

Transitivity on the nonzero vectors of the binary natural A₆ module makes
every invariant subgroup trivial or full. Equivariant quotient coordinates
transport this to the normal-subgroup interval in the definition of shortness.
This does not assume that the commutator core itself is elementary.

Source: Aschbacher–Smith C.1.7 and C.1.12, printed pp.123–124.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC

/-- A literal natural A₆ model supplies the irreducibility clause of shortness. -/
theorem IsLinearBlockModel.alternating_six_irreducible {L : Type*} [Group L]
    (h : IsLinearBlockModel L ((BinaryPermutation.naturalRepresentation (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype)) : BlockModuleIrreducible L := by
  let : Nontrivial (BinaryPermutation.natural (Fin 6)) := Module.nontrivial_of_finrank_pos
    (by rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]; decide)
  obtain ⟨ρ, ⟨m⟩, hρ⟩ := h
  apply m.irreducible
  intro W hW
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  have hn : ¬ ∀ x ∈ W, x = 1 := fun h => hb ((Subgroup.eq_bot_iff_forall W).mpr h)
  push Not at hn
  obtain ⟨v, hv, hv1⟩ := hn
  apply top_unique
  intro w _
  by_cases hw : w = 1
  · exact hw ▸ W.one_mem
  have hv0 : v.toAdd ≠ 0 := fun h => hv1 (Multiplicative.toAdd.injective h)
  have hw0 : w.toAdd ≠ 0 := fun h => hw (Multiplicative.toAdd.injective h)
  obtain ⟨g, hg⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero
    v.toAdd w.toAdd hv0 hw0
  have he : ρ g v = w := Multiplicative.toAdd.injective ((hρ g v).trans hg)
  exact he ▸ hW g v hv

end CFSG.Quasithin.ChapterC
