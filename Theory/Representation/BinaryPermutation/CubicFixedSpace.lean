module

public import Theory.Representation.CubicFixedSpace
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# A cubic stabilizer of the small alternating permutation fixed spaces

The regular Klein four group on the first four letters is normalized by
the three-cycle on the first three. A Klein-fixed function is constant on
those four letters, so the three-cycle fixes it. Both Klein generators
have an unused fixed letter. Consequently the same argument works modulo
the constant line: a constant displacement must vanish at that letter.
Restriction gives the augmentation core and the natural section as well.

This proves the local calculation for all four actual permutation sections
in degrees six and seven. In degree six, the full, core and deleted modules
include the nonsplit modules of Aschbacher–Smith B.3.3, p.84. The cubic
normalizer also supplies the extension argument for B.5.1, p.99, as used
in Lemma 15.4.18, p.1163.
-/

public section
namespace BinaryPermutation.CubicFixedSpace
open Equiv Representation Representation.BinaryOffender Subgroup

@[expose] def first (n : ℕ) (hn : n = 6 ∨ n = 7) : alternatingGroup (Fin n) :=
  ⟨swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨2, by omega⟩ ⟨3, by omega⟩, by
    rw [Equiv.Perm.mem_alternatingGroup]
    rcases hn with rfl | rfl <;> decide +kernel⟩

@[expose] def second (n : ℕ) (hn : n = 6 ∨ n = 7) : alternatingGroup (Fin n) :=
  ⟨swap ⟨0, by omega⟩ ⟨2, by omega⟩ * swap ⟨1, by omega⟩ ⟨3, by omega⟩, by
    rw [Equiv.Perm.mem_alternatingGroup]
    rcases hn with rfl | rfl <;> decide +kernel⟩

/-- The three-cycle `(0 1 2)` on the first three letters. -/
@[expose] def cycle (n : ℕ) (hn : n = 6 ∨ n = 7) : alternatingGroup (Fin n) :=
  ⟨swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨1, by omega⟩ ⟨2, by omega⟩, by
    rw [Equiv.Perm.mem_alternatingGroup]
    rcases hn with rfl | rfl <;> decide +kernel⟩

private def word (n : ℕ) (hn : n = 6 ∨ n = 7) : Fin 4 → alternatingGroup (Fin n) :=
  ![1, first n hn, second n hn, first n hn * second n hn]

/-- The regular Klein four on the first four letters. -/
def klein (n : ℕ) (hn : n = 6 ∨ n = 7) : Subgroup (alternatingGroup (Fin n)) where
  carrier := Set.range (word n hn)
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    have hc : ∀ i j, ∃ k, word n hn i * word n hn j = word n hn k := by
      rcases hn with rfl | rfl <;> decide +kernel
    rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hc i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    have hc : ∀ i, ∃ j, (word n hn i)⁻¹ = word n hn j := by
      rcases hn with rfl | rfl <;> decide +kernel
    rintro a ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hc i
    exact ⟨j, hj.symm⟩

theorem first_mem (n : ℕ) (hn : n = 6 ∨ n = 7) : first n hn ∈ klein n hn :=
  ⟨1, rfl⟩

theorem second_mem (n : ℕ) (hn : n = 6 ∨ n = 7) : second n hn ∈ klein n hn :=
  ⟨2, rfl⟩

theorem klein_isPGroup (n : ℕ) (hn : n = 6 ∨ n = 7) :
    IsPGroup 2 (klein n hn) := by
  apply IsPGroup.of_card (n := 2)
  have hi : Function.Injective (word n hn) := by
    rcases hn with rfl | rfl <;> decide +kernel
  change Nat.card (Set.range (word n hn)) = 2 ^ 2
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  simp

theorem cycle_pow (n : ℕ) (hn : n = 6 ∨ n = 7) : (cycle n hn) ^ 3 = 1 := by
  rcases hn with rfl | rfl <;> decide +kernel

theorem cycle_ne_one (n : ℕ) (hn : n = 6 ∨ n = 7) : cycle n hn ≠ 1 := by
  rcases hn with rfl | rfl <;> decide +kernel

theorem cycle_normalizes (n : ℕ) (hn : n = 6 ∨ n = 7) :
    cycle n hn ∈ normalizer (klein n hn : Set (alternatingGroup (Fin n))) := by
  have hf : ∀ i, ∃ j,
      cycle n hn * word n hn i * (cycle n hn)⁻¹ = word n hn j := by
    rcases hn with rfl | rfl <;> decide +kernel
  have hb : ∀ i, ∃ j,
      (cycle n hn)⁻¹ * word n hn i * cycle n hn = word n hn j := by
    rcases hn with rfl | rfl <;> decide +kernel
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

private theorem full_generator_test (n : ℕ) (hn : n = 6 ∨ n = 7) :
    ∀ v : Full (Fin n),
      representation (Fin n) (first n hn).val v = v →
      representation (Fin n) (second n hn).val v = v →
      representation (Fin n) (cycle n hn).val v = v := by
  simp only [funext_iff, representation_apply]
  rcases hn with rfl | rfl <;> decide +kernel

private theorem deleted_generator_test (n : ℕ) (hn : n = 6 ∨ n = 7)
    (v : Deleted (Fin n))
    (h₁ : deletedRepresentation (Fin n) (first n hn).val v = v)
    (h₂ : deletedRepresentation (Fin n) (second n hn).val v = v) :
    deletedRepresentation (Fin n) (cycle n hn).val v = v := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    have hf₁ : (first n hn).val ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
      rcases hn with rfl | rfl <;> decide +kernel
    have hf₂ : (second n hn).val ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
      rcases hn with rfl | rfl <;> decide +kernel
    have hv₁ := (deleted_fixed_iff_of_fixed_point _ v _ hf₁).mp h₁
    have hv₂ := (deleted_fixed_iff_of_fixed_point _ v _ hf₂).mp h₂
    exact congrArg (constants (Fin n)).mkQ (full_generator_test n hn v hv₁ hv₂)

/-- The cubic element fixes the full permutation fixed space. -/
theorem cycle_fixes_full (n : ℕ) (hn : n = 6 ∨ n = 7) :
    ∀ v ∈ fixedSpace ((representation (Fin n)).comp (alternatingGroup (Fin n)).subtype)
      (klein n hn), representation (Fin n) (cycle n hn).val v = v := by
  intro v hv
  exact full_generator_test n hn v (hv ⟨_, ⟨1, rfl⟩⟩) (hv ⟨_, ⟨2, rfl⟩⟩)

/-- The cubic element fixes the augmentation-core fixed space. -/
theorem cycle_fixes_core (n : ℕ) (hn : n = 6 ∨ n = 7) :
    ∀ v ∈ fixedSpace ((coreRepresentation (Fin n)).comp (alternatingGroup (Fin n)).subtype)
      (klein n hn), coreRepresentation (Fin n) (cycle n hn).val v = v := by
  intro v hv
  apply Subtype.ext
  apply full_generator_test n hn v.val
  · exact congrArg Subtype.val (hv ⟨_, ⟨1, rfl⟩⟩)
  · exact congrArg Subtype.val (hv ⟨_, ⟨2, rfl⟩⟩)

/-- Passing to the deleted quotient introduces no obstruction. -/
theorem cycle_fixes_deleted (n : ℕ) (hn : n = 6 ∨ n = 7) :
    ∀ v ∈ fixedSpace ((deletedRepresentation (Fin n)).comp (alternatingGroup (Fin n)).subtype)
      (klein n hn), deletedRepresentation (Fin n) (cycle n hn).val v = v := by
  intro v hv
  exact deleted_generator_test n hn v (hv ⟨_, ⟨1, rfl⟩⟩) (hv ⟨_, ⟨2, rfl⟩⟩)

/-- The natural section, of dimension four in degree six and six in degree seven. -/
theorem cycle_fixes_natural (n : ℕ) (hn : n = 6 ∨ n = 7) :
    ∀ v ∈ fixedSpace (alternatingNaturalRepresentation (Ω := Fin n))
      (klein n hn), naturalRepresentation (Fin n) (cycle n hn).val v = v := by
  intro v hv
  apply Subtype.ext
  apply deleted_generator_test n hn v.val
  · exact congrArg Subtype.val (hv ⟨_, ⟨1, rfl⟩⟩)
  · exact congrArg Subtype.val (hv ⟨_, ⟨2, rfl⟩⟩)

end BinaryPermutation.CubicFixedSpace
