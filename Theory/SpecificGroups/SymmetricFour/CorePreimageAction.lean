module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Mathlib.GroupTheory.Sylow
/-!
# Transitivity of the Sylow preimage of the four-point two-core

The normal Klein four core of S₄ is transitive on the four letters. Its
containment in every Sylow image lifts that transitivity through the literal
intersection T∩f⁻¹(O₂(S₄)). This supplies the actor used on the two fixed maximum
elementary subgroups in Aschbacher–Smith 10.2.1, printed p.743.
-/
public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricFour
theorem twoCore_transitive (i j : Fin 4) :
    ∃ g ∈ pCore 2 (Equiv.Perm (Fin 4)), g i = j := by
  rw [←SymmetricSix.DuadCalculation.core_eq]
  exact (show ∀ i j : Fin 4, ∃ g ∈ SymmetricSix.DuadCalculation.core, g i = j by decide +kernel) i j
end Theory.SpecificGroups.SymmetricFour
namespace Subgroup
variable {H : Type*} [Group H] [Finite H]
theorem sylow_core_preimage_transitive
    (T : Sylow 2 H) (f : H →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (i j : Fin 4) :
    ∃ t ∈ (T : Subgroup H) ⊓ (pCore 2 (Equiv.Perm (Fin 4))).comap f, f t i = j := by
  obtain ⟨g,hg,he⟩ := Theory.SpecificGroups.SymmetricFour.twoCore_transitive i j
  have hle := pCore_isPGroup.le_sylow_of_normal (T.mapSurjective hf)
  obtain ⟨t,ht,rfl⟩ := hle hg
  exact ⟨t,⟨ht,hg⟩,he⟩
end Subgroup
