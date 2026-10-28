module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# The actual degree-six natural action images

The augmentation quotient has dimension four, and its nonzero vectors are
the fifteen duads. A permutation fixing every duad fixes every letter, so
the symmetric action and its alternating restriction are faithful. We retain
their actual embeddings in the invertible endomorphisms of the same module.

These are the model interfaces for Aschbacher–Smith 13.8.26–27, printed
pp.962–963, with the module convention of §B.3, printed pp.83–85.
No identification of the two outer-related natural A₆ actions is made here.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix

open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

abbrev Symmetric := Equiv.Perm (Fin 6)
abbrev Alternating := alternatingGroup (Fin 6)
abbrev Natural := natural (Fin 6)
abbrev Augmentation := core (Fin 6)
abbrev LinearGroup := (Module.End (ZMod 2) Natural)ˣ

/-- The literal symmetric natural representation. -/
abbrev symmetricAction := naturalRepresentation (Fin 6)

/-- The literal alternating restriction, retaining its marking. -/
abbrev alternatingAction := alternatingNaturalRepresentation (Fin 6)

/-- The symmetric action as an embedding into invertible endomorphisms. -/
def symmetricHom : Symmetric →* LinearGroup := symmetricAction.asGroupHom

/-- The alternating action as an embedding into the same linear group. -/
def alternatingHom : Alternating →* LinearGroup := alternatingAction.asGroupHom

def symmetricImage : Subgroup LinearGroup := symmetricHom.range
def alternatingImage : Subgroup LinearGroup := alternatingHom.range

theorem natural_finrank : Module.finrank (ZMod 2) Natural = 4 :=
  finrank_natural_even (Fin 6) (by decide)

theorem augmentation_finrank : Module.finrank (ZMod 2) Augmentation = 5 :=
  finrank_core (Fin 6)

/-- Equality on all duads forces equality on each letter. -/
theorem symmetricAction_injective : Function.Injective symmetricAction := by
  intro g h he
  have hp (i j : Fin 6) (hij : i ≠ j) :
      Theory.SpecificGroups.SymmetricSix.pair (g i) (g j) =
        Theory.SpecificGroups.SymmetricSix.pair (h i) (h j) := by
    apply (pairVector_eq_iff (g.injective.ne hij) (h.injective.ne hij)).mp
    simpa only [← pairVector_map] using LinearMap.congr_fun he (pairVector i j)
  apply Equiv.ext
  intro i
  obtain ⟨j, k, hij, hik, hjk⟩ : ∃ j k : Fin 6, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    revert i
    decide
  have hj := hp i j hij
  have hk := hp i k hik
  have hj' : g i = h i ∨ g i = h j := by
    have hm : g i ∈ Theory.SpecificGroups.SymmetricSix.pair (h i) (h j) :=
      hj ▸ (by simp [Theory.SpecificGroups.SymmetricSix.pair])
    simpa [Theory.SpecificGroups.SymmetricSix.pair] using hm
  have hk' : g i = h i ∨ g i = h k := by
    have hm : g i ∈ Theory.SpecificGroups.SymmetricSix.pair (h i) (h k) :=
      hk ▸ (by simp [Theory.SpecificGroups.SymmetricSix.pair])
    simpa [Theory.SpecificGroups.SymmetricSix.pair] using hm
  rcases hj' with heq | heq
  · exact heq
  rcases hk' with heq' | heq'
  · exact heq'
  exact (hjk (h.injective (heq.symm.trans heq'))).elim

theorem alternatingAction_injective : Function.Injective alternatingAction :=
  symmetricAction_injective.comp Subtype.val_injective

theorem symmetricHom_injective : Function.Injective symmetricHom := by
  intro g h he
  apply symmetricAction_injective
  exact congrArg Units.val he

theorem alternatingHom_injective : Function.Injective alternatingHom := by
  intro g h he
  apply alternatingAction_injective
  exact congrArg Units.val he

theorem alternatingHom_eq_comp :
    alternatingHom = symmetricHom.comp (alternatingGroup (Fin 6)).subtype := rfl

theorem alternatingImage_le_symmetricImage : alternatingImage ≤ symmetricImage := by
  rintro _ ⟨g, rfl⟩
  exact ⟨g.val, rfl⟩

/-- The alternating image is the image of the literal even-permutation subgroup. -/
theorem alternatingImage_eq_map :
    alternatingImage = (alternatingGroup (Fin 6)).map symmetricHom := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact ⟨a.val, a.property, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

/-- Every symmetric natural operator normalizes the alternating natural image. -/
theorem symmetricImage_le_normalizer :
    symmetricImage ≤ Subgroup.normalizer (alternatingImage : Set LinearGroup) := by
  have h := (alternatingGroup (Fin 6)).le_normalizer_map symmetricHom
  rw [Subgroup.normalizer_eq_top, ← symmetricHom.range_eq_map, ← alternatingImage_eq_map] at h
  exact h

/-- The augmentation action is faithful because its natural quotient is. -/
theorem coreAction_injective : Function.Injective (coreRepresentation (Fin 6)) := by
  intro g h he
  apply symmetricAction_injective
  apply LinearMap.ext
  intro v
  obtain ⟨u, rfl⟩ := coreToNatural_surjective v
  rw [← coreToNatural_equivariant, ← coreToNatural_equivariant]
  exact congrArg (coreToNatural (Fin 6)) (LinearMap.congr_fun he u)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
