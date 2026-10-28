module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120.Adjoint

/-!
# Literal generator matrices for the native trace-zero code adjoint

The structural entry formula reduces each conjugated matrix unit to two
products in F₂. The finite checks identify these entries with the saved packed
adjoint matrices, retaining the precise basis order and column convention.

Sources: `source/adjoint120-comparison.json`; James, J. Algebra 27 (1973),
57–111; GM02, Proposition 5.1.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120

set_option Elab.async false

private theorem entries0_0 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 0 ⟨i.val + 0, by omega⟩ j =
      adjointMatrix 0 ⟨i.val + 0, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries0_1 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 0 ⟨i.val + 10, by omega⟩ j =
      adjointMatrix 0 ⟨i.val + 10, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries0_2 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 0 ⟨i.val + 20, by omega⟩ j =
      adjointMatrix 0 ⟨i.val + 20, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries0_3 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 0 ⟨i.val + 30, by omega⟩ j =
      adjointMatrix 0 ⟨i.val + 30, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries0_4 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 0 ⟨i.val + 40, by omega⟩ j =
      adjointMatrix 0 ⟨i.val + 40, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries0_5 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 0 ⟨i.val + 50, by omega⟩ j =
      adjointMatrix 0 ⟨i.val + 50, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries0_6 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 0 ⟨i.val + 60, by omega⟩ j =
      adjointMatrix 0 ⟨i.val + 60, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries0_7 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 0 ⟨i.val + 70, by omega⟩ j =
      adjointMatrix 0 ⟨i.val + 70, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries0_8 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 0 ⟨i.val + 80, by omega⟩ j =
      adjointMatrix 0 ⟨i.val + 80, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries0_9 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 0 ⟨i.val + 90, by omega⟩ j =
      adjointMatrix 0 ⟨i.val + 90, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries0_10 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 0 ⟨i.val + 100, by omega⟩ j =
      adjointMatrix 0 ⟨i.val + 100, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries0_11 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 0 ⟨i.val + 110, by omega⟩ j =
      adjointMatrix 0 ⟨i.val + 110, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries1_0 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 1 ⟨i.val + 0, by omega⟩ j =
      adjointMatrix 1 ⟨i.val + 0, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries1_1 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 1 ⟨i.val + 10, by omega⟩ j =
      adjointMatrix 1 ⟨i.val + 10, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries1_2 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 1 ⟨i.val + 20, by omega⟩ j =
      adjointMatrix 1 ⟨i.val + 20, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries1_3 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 1 ⟨i.val + 30, by omega⟩ j =
      adjointMatrix 1 ⟨i.val + 30, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries1_4 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 1 ⟨i.val + 40, by omega⟩ j =
      adjointMatrix 1 ⟨i.val + 40, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries1_5 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 1 ⟨i.val + 50, by omega⟩ j =
      adjointMatrix 1 ⟨i.val + 50, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries1_6 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 1 ⟨i.val + 60, by omega⟩ j =
      adjointMatrix 1 ⟨i.val + 60, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries1_7 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 1 ⟨i.val + 70, by omega⟩ j =
      adjointMatrix 1 ⟨i.val + 70, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries1_8 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 1 ⟨i.val + 80, by omega⟩ j =
      adjointMatrix 1 ⟨i.val + 80, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries1_9 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 1 ⟨i.val + 90, by omega⟩ j =
      adjointMatrix 1 ⟨i.val + 90, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries1_10 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 1 ⟨i.val + 100, by omega⟩ j =
      adjointMatrix 1 ⟨i.val + 100, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem entries1_11 : ∀ (i : Fin 10) (j : Fin 120),
    adjointEntry 1 ⟨i.val + 110, by omega⟩ j =
      adjointMatrix 1 ⟨i.val + 110, by omega⟩ j := by
  unfold adjointMatrix packedMatrix
  decide +kernel

private theorem adjointEntry_eq (a : Fin 2) (i j : Fin 120) :
    adjointEntry a i j = adjointMatrix a i j := by
  let q : Fin 12 := ⟨i.val / 10, by omega⟩
  let r : Fin 10 := ⟨i.val % 10, by omega⟩
  have hi : i.val = r.val + 10 * q.val := by dsimp [q, r]; omega
  clear_value q r
  fin_cases a
  · fin_cases q
    · have he : i = (⟨r.val + 0, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries0_0 r j
    · have he : i = (⟨r.val + 10, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries0_1 r j
    · have he : i = (⟨r.val + 20, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries0_2 r j
    · have he : i = (⟨r.val + 30, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries0_3 r j
    · have he : i = (⟨r.val + 40, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries0_4 r j
    · have he : i = (⟨r.val + 50, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries0_5 r j
    · have he : i = (⟨r.val + 60, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries0_6 r j
    · have he : i = (⟨r.val + 70, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries0_7 r j
    · have he : i = (⟨r.val + 80, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries0_8 r j
    · have he : i = (⟨r.val + 90, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries0_9 r j
    · have he : i = (⟨r.val + 100, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries0_10 r j
    · have he : i = (⟨r.val + 110, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries0_11 r j
  · fin_cases q
    · have he : i = (⟨r.val + 0, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries1_0 r j
    · have he : i = (⟨r.val + 10, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries1_1 r j
    · have he : i = (⟨r.val + 20, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries1_2 r j
    · have he : i = (⟨r.val + 30, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries1_3 r j
    · have he : i = (⟨r.val + 40, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries1_4 r j
    · have he : i = (⟨r.val + 50, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries1_5 r j
    · have he : i = (⟨r.val + 60, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries1_6 r j
    · have he : i = (⟨r.val + 70, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries1_7 r j
    · have he : i = (⟨r.val + 80, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries1_8 r j
    · have he : i = (⟨r.val + 90, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries1_9 r j
    · have he : i = (⟨r.val + 100, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries1_10 r j
    · have he : i = (⟨r.val + 110, by omega⟩ : Fin 120) := by
        apply Fin.ext
        simpa using hi
      rw [he]
      exact entries1_11 r j

/-- Both literal native actors have the recorded adjoint matrices. -/
theorem adjointRepresentation_actor (a : Fin 2) :
    LinearMap.toMatrix' (adjointRepresentation (actor a)) = adjointMatrix a := by
  ext i j
  rw [adjointRepresentation_actor_entry, adjointEntry_eq]

/-- This is a native M24 action, without an irreducibility or density premise. -/
def adjointRealization : NativeRealization 120 adjointMatrix :=
  ⟨adjointRepresentation, adjointRepresentation_actor⟩

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120
