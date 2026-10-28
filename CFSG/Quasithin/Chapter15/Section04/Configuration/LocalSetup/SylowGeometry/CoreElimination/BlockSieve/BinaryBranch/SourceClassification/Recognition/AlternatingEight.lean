module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition.Natural
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# The degree-eight natural section in the binary source sieve

The regular four-group on four letters has a normalizing three-cycle
fixing every fixed vector of the deleted permutation module. An unused
letter forces constant displacements to vanish, so this remains true on
the natural six-space. This explicit calculation applies to both the
orthogonal A₈ row and the marked S₈ row of B.4.2 on the actual source
central section, including its two nonsplit extensions.
Source: Aschbacher–Smith, B.4.2(10), p.86; B.5.1, p.99; 15.4.20, p.1164.
-/

@[expose] public section
open Equiv Representation Representation.BinaryOffender Subgroup
open Representation.BinarySylowFixedSpace Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition
open TwoFactors.FFBranch TwoFactors.FFBranch.ClassificationComparison FFAlternatives
namespace AlternatingEight
open BinaryPermutation

private def first : alternatingGroup (Fin 8) :=
  ⟨swap (0 : Fin 8) 1 * swap (2 : Fin 8) 3, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩

private def second : alternatingGroup (Fin 8) :=
  ⟨swap (0 : Fin 8) 2 * swap (1 : Fin 8) 3, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩

/-- The three-cycle `(0 1 2)` on the first three letters. -/
private def cycle : alternatingGroup (Fin 8) :=
  ⟨swap (0 : Fin 8) 1 * swap (1 : Fin 8) 2, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩

private def word : Fin 4 → alternatingGroup (Fin 8) :=
  ![1, first, second, first * second]

/-- The regular Klein four on the first four letters. -/
private def klein : Subgroup (alternatingGroup (Fin 8)) where
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

private theorem first_mem : first ∈ klein :=
  ⟨1, rfl⟩

private theorem second_mem : second ∈ klein :=
  ⟨2, rfl⟩

private theorem klein_isPGroup :
    IsPGroup 2 (klein) := by
  apply IsPGroup.of_card (n := 2)
  have hi : Function.Injective (word) := by
    decide +kernel
  change Nat.card (Set.range (word)) = 2 ^ 2
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  simp

private theorem cycle_pow : (cycle) ^ 3 = 1 := by
  decide +kernel

private theorem cycle_ne_one : cycle ≠ 1 := by
  decide +kernel

private theorem cycle_normalizes :
    cycle ∈ normalizer (klein : Set (alternatingGroup (Fin 8))) := by
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
    ∀ v : Full (Fin 8),
      representation (Fin 8) (first).val v = v →
      representation (Fin 8) (second).val v = v →
      representation (Fin 8) (cycle).val v = v := by
  simp only [funext_iff, representation_apply]
  decide +kernel

private theorem deleted_generator_test
    (v : Deleted (Fin 8))
    (h₁ : deletedRepresentation (Fin 8) (first).val v = v)
    (h₂ : deletedRepresentation (Fin 8) (second).val v = v) :
    deletedRepresentation (Fin 8) (cycle).val v = v := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    have hf₁ : (first).val ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
      decide +kernel
    have hf₂ : (second).val ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
      decide +kernel
    have hv₁ := (deleted_fixed_iff_of_fixed_point _ v _ hf₁).mp h₁
    have hv₂ := (deleted_fixed_iff_of_fixed_point _ v _ hf₂).mp h₂
    exact congrArg (constants (Fin 8)).mkQ (full_generator_test v hv₁ hv₂)

/-- The cubic element fixes the full permutation fixed space. -/
private theorem cycle_fixes_full :
    ∀ v ∈ fixedSpace ((representation (Fin 8)).comp (alternatingGroup (Fin 8)).subtype)
      (klein), representation (Fin 8) (cycle).val v = v := by
  intro v hv
  exact full_generator_test v (hv ⟨_, ⟨1, rfl⟩⟩) (hv ⟨_, ⟨2, rfl⟩⟩)

/-- The cubic element fixes the augmentation-core fixed space. -/
private theorem cycle_fixes_core :
    ∀ v ∈ fixedSpace ((coreRepresentation (Fin 8)).comp (alternatingGroup (Fin 8)).subtype)
      (klein), coreRepresentation (Fin 8) (cycle).val v = v := by
  intro v hv
  apply Subtype.ext
  apply full_generator_test v.val
  · exact congrArg Subtype.val (hv ⟨_, ⟨1, rfl⟩⟩)
  · exact congrArg Subtype.val (hv ⟨_, ⟨2, rfl⟩⟩)

/-- Passing to the deleted quotient introduces no obstruction. -/
private theorem cycle_fixes_deleted :
    ∀ v ∈ fixedSpace ((deletedRepresentation (Fin 8)).comp (alternatingGroup (Fin 8)).subtype)
      (klein), deletedRepresentation (Fin 8) (cycle).val v = v := by
  intro v hv
  exact deleted_generator_test v (hv ⟨_, ⟨1, rfl⟩⟩) (hv ⟨_, ⟨2, rfl⟩⟩)

/-- The actual four-dimensional natural alternating-five section. -/
private theorem cycle_fixes_natural :
    ∀ v ∈ fixedSpace (alternatingNaturalRepresentation (Ω := Fin 8))
      (klein), naturalRepresentation (Fin 8) (cycle).val v = v := by
  intro v hv
  apply Subtype.ext
  apply deleted_generator_test v.val
  · exact congrArg Subtype.val (hv ⟨_, ⟨1, rfl⟩⟩)
  · exact congrArg Subtype.val (hv ⟨_, ⟨2, rfl⟩⟩)

/-- The cubic calculation on the literal alternating-eight natural module. -/
theorem enlargement (S : Sylow 2 (alternatingGroup (Fin 8))) :
    ∃ c : alternatingGroup (Fin 8), c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (alternatingNatural 8) (S : Subgroup _),
        alternatingNatural 8 c v = v :=
  sylow_fixedSpace_enlargement_of_cubic _ klein klein_isPGroup cycle
    cycle_pow cycle_ne_one cycle_fixes_natural S

end AlternatingEight

variable {G : Type*} [Group G] [Finite G]
  {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}

/-- Both A₈ and marked S₈ rows contradict the original source Sylow kernel. -/
theorem sourceAction_not_alternatingEight (h : Input d i j H U K)
    {L : Subgroup (sourceGroup h)}
    (s : let := h.module_properties.1; MovedSection (sourceAction h) L)
    (e : let := h.module_properties.1;
      ActionEquiv (s.action.comp L.subtype) (alternatingNatural 8)) : False := by
  let := h.module_properties.1
  obtain ⟨S, hS⟩ := exists_offenderSylow h.placed.sylow (d.Z.subgroupOf H)
    h.seed_inputs.2.2.1
  let T : Sylow 2 L := Classical.choice inferInstance
  have he := sylow_fixedSpace_enlargement_equivariant _ _ (T : Subgroup L)
    e.groupEquiv e.linearEquiv e.intertwines
    (AlternatingEight.enlargement (T.mapSurjective e.groupEquiv.surjective))
  obtain ⟨c, hc, _, hf⟩ := NativeSections.movedSection_enlargement s T he S
  change ∀ v ∈ fixedSpace
    (offenderAction h.placed.sylow (d.Z.subgroupOf H) h.seed_inputs.2.2.1) (S : Subgroup _),
    offenderAction h.placed.sylow (d.Z.subgroupOf H) h.seed_inputs.2.2.1 c v = v at hf
  exact offenderAction_no_fixedSpace_enlargement h.placed.sylow (d.Z.subgroupOf H)
    h.seed_inputs.2.2.1 (S : Subgroup _) hS c hc hf

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition
