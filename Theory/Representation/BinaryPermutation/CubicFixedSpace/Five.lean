module

public import Theory.Representation.CubicFixedSpace
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# A cubic fixed-space obstruction for the alternating-five module

The regular Klein four on four of the five letters is normalized by a
three-cycle fixing every Klein-fixed vector of the binary permutation module.
The unused fifth letter makes the assertion descend through the constant line.
The same calculation therefore holds for the four-dimensional natural section.
Cubic lifting transports it through central extensions without a splitting.

This is the degree-five version of `BinaryPermutation.CubicFixedSpace`, needed
in the A₅-block alternative in Aschbacher–Smith, combined manuscript
(1 March 2004), C.2.7(3) (p.145) and 15.4.20 (p.1164).
-/

public section
namespace BinaryPermutation.CubicFixedSpace.Five
open Equiv Representation Representation.BinaryOffender Subgroup

@[expose] def first : alternatingGroup (Fin 5) :=
  ⟨swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨2, by omega⟩ ⟨3, by omega⟩, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩

@[expose] def second : alternatingGroup (Fin 5) :=
  ⟨swap ⟨0, by omega⟩ ⟨2, by omega⟩ * swap ⟨1, by omega⟩ ⟨3, by omega⟩, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩

/-- The three-cycle `(0 1 2)` on the first three letters. -/
@[expose] def cycle : alternatingGroup (Fin 5) :=
  ⟨swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨1, by omega⟩ ⟨2, by omega⟩, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩

private def word : Fin 4 → alternatingGroup (Fin 5) :=
  ![1, first, second, first * second]

/-- The regular Klein four on the first four letters. -/
def klein : Subgroup (alternatingGroup (Fin 5)) where
  carrier := Set.range (word)
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    have hc : ∀ i j, ∃ k, word i * word j = word k := by
      decide +kernel
    rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hc i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    have hc : ∀ i, ∃ j, (word i)⁻¹ = word j := by
      decide +kernel
    rintro a ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hc i
    exact ⟨j, hj.symm⟩

theorem first_mem : first ∈ klein :=
  ⟨1, rfl⟩

theorem second_mem : second ∈ klein :=
  ⟨2, rfl⟩

theorem klein_isPGroup :
    IsPGroup 2 (klein) := by
  apply IsPGroup.of_card (n := 2)
  have hi : Function.Injective (word) := by
    decide +kernel
  change Nat.card (Set.range (word)) = 2 ^ 2
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  simp

theorem cycle_pow : (cycle) ^ 3 = 1 := by
  decide +kernel

theorem cycle_ne_one : cycle ≠ 1 := by
  decide +kernel

theorem cycle_normalizes :
    cycle ∈ normalizer (klein : Set (alternatingGroup (Fin 5))) := by
  have hf : ∀ i, ∃ j,
      cycle * word i * (cycle)⁻¹ = word j := by
    decide +kernel
  have hb : ∀ i, ∃ j,
      (cycle)⁻¹ * word i * cycle = word j := by
    decide +kernel
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hf i
    exact ⟨j, hj.symm⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := hb i
    refine ⟨j, ?_⟩
    rw [← hj, hi]
    simp [mul_assoc]

private theorem full_generator_test :
    ∀ v : Full (Fin 5),
      representation (Fin 5) (first).val v = v →
      representation (Fin 5) (second).val v = v →
      representation (Fin 5) (cycle).val v = v := by
  simp only [funext_iff, representation_apply]
  decide +kernel

private theorem deleted_generator_test
    (v : Deleted (Fin 5))
    (h₁ : deletedRepresentation (Fin 5) (first).val v = v)
    (h₂ : deletedRepresentation (Fin 5) (second).val v = v) :
    deletedRepresentation (Fin 5) (cycle).val v = v := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    have hf₁ : (first).val ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
      decide +kernel
    have hf₂ : (second).val ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
      decide +kernel
    have hv₁ := (deleted_fixed_iff_of_fixed_point _ v _ hf₁).mp h₁
    have hv₂ := (deleted_fixed_iff_of_fixed_point _ v _ hf₂).mp h₂
    exact congrArg (constants (Fin 5)).mkQ (full_generator_test v hv₁ hv₂)

/-- The cubic element fixes the full permutation fixed space. -/
theorem cycle_fixes_full :
    ∀ v ∈ fixedSpace ((representation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype)
      (klein), representation (Fin 5) (cycle).val v = v := by
  intro v hv
  exact full_generator_test v (hv ⟨_, ⟨1, rfl⟩⟩) (hv ⟨_, ⟨2, rfl⟩⟩)

/-- The cubic element fixes the augmentation-core fixed space. -/
theorem cycle_fixes_core :
    ∀ v ∈ fixedSpace ((coreRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype)
      (klein), coreRepresentation (Fin 5) (cycle).val v = v := by
  intro v hv
  apply Subtype.ext
  apply full_generator_test v.val
  · exact congrArg Subtype.val (hv ⟨_, ⟨1, rfl⟩⟩)
  · exact congrArg Subtype.val (hv ⟨_, ⟨2, rfl⟩⟩)

/-- Passing to the deleted quotient introduces no obstruction. -/
theorem cycle_fixes_deleted :
    ∀ v ∈ fixedSpace ((deletedRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype)
      (klein), deletedRepresentation (Fin 5) (cycle).val v = v := by
  intro v hv
  exact deleted_generator_test v (hv ⟨_, ⟨1, rfl⟩⟩) (hv ⟨_, ⟨2, rfl⟩⟩)

/-- The actual four-dimensional natural alternating-five section. -/
theorem cycle_fixes_natural :
    ∀ v ∈ fixedSpace (alternatingNaturalRepresentation (Ω := Fin 5))
      (klein), naturalRepresentation (Fin 5) (cycle).val v = v := by
  intro v hv
  apply Subtype.ext
  apply deleted_generator_test v.val
  · exact congrArg Subtype.val (hv ⟨_, ⟨1, rfl⟩⟩)
  · exact congrArg Subtype.val (hv ⟨_, ⟨2, rfl⟩⟩)


/-- A faithful embedded A₅ with its natural central section has a cubic
element outside every Sylow two-subgroup fixing its entire fixed space. -/
theorem centralSection_enlargement
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (f : alternatingGroup (Fin 5) →* D) (hf : Function.Injective f)
    (U : Subrepresentation (ρ.comp f))
    (q : U.toSubmodule →ₗ[ZMod 2] natural (Fin 5))
    (hq : ∀ g u, q (U.toRepresentation g u) = naturalRepresentation (Fin 5) g.val (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  apply sylow_fixedSpace_enlargement_of_embedded_cubic ρ f hf _
    klein_isPGroup _ cycle_pow cycle_ne_one _ S
  exact cubic_fixedSpace_of_central_section (ρ.comp f)
    (alternatingNaturalRepresentation (Ω := Fin 5)) _ _ cycle_pow
    cycle_normalizes U q hq hker hquot cycle_fixes_natural

end BinaryPermutation.CubicFixedSpace.Five
