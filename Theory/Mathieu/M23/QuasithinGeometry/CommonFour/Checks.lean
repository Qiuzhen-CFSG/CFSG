module

public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Coordinates
public import Theory.Mathieu.M23.QuasithinGeometry.ElementarySylow.Checks

/-!
# Finite checks for the compatible heptad and quintet marking

The transported Sylow group stabilizes the incident standard octad and sextet.
Its first E16 fixes the individual tetrads; its second fixes the octad
pointwise. Two local conjugators cut the Sylow group down to the respective
E16 subgroups. The intersection test decodes a possible conjugate from two
point images before checking its whole point table, avoiding a quadratic
search through pairs of Sylow elements.

All finite identities are checked in the Lean kernel. Source: Aschbacher–Smith,
H.14.2(1) and H.16.8, printed pp.397,405.
-/

@[expose] public section
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.CommonFour
open M24LocalGeometry MathieuCode FusionCertificate ElementarySylow
set_option maxRecDepth 100000
set_option Elab.async false

def markedPerm (i : Fin 128) : Equiv.Perm (Fin 23) :=
  transportPerm * perm i * transportPerm⁻¹

/-- Checking the six Sylow generators suffices for the whole stabilizer arrangement. -/
theorem stabilizes_generators : ∀ j : Fin 6,
    let p := transportPerm * gen j * transportPerm⁻¹
    (standardSextet.parts.image (fun A => A.image (extendPoint p))) =
      standardSextet.parts ∧
    standardOctad.val.image (extendPoint p) = standardOctad.val := by
  decide +kernel

theorem candidate0_fixes : ∀ (i : Fin 16) (j : Fin 6),
    (standardTetrad j).image (extendPoint (markedPerm (candidateIndex 0 i))) =
      standardTetrad j := by decide +kernel

theorem candidate1_fixes : ∀ (i : Fin 16) (a : Fin 24), a ∈ standardOctad.val →
    extendPoint (markedPerm (candidateIndex 1 i)) a = a := by decide +kernel

def relativePerm0 : Equiv.Perm (Fin 23) where
  toFun := ![0, 1, 11, 21, 7, 19, 6, 4, 22, 9, 17, 2, 12, 14, 13, 18, 16, 10, 15, 5, 20, 3, 8]
  invFun := ![0, 1, 11, 21, 7, 19, 6, 4, 22, 9, 17, 2, 12, 14, 13, 18, 16, 10, 15, 5, 20, 3, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def relativePerm1 : Equiv.Perm (Fin 23) where
  toFun := ![0, 1, 9, 8, 4, 18, 11, 7, 3, 2, 10, 6, 12, 16, 20, 21, 13, 17, 5, 22, 14, 15, 19]
  invFun := ![0, 1, 9, 8, 4, 18, 11, 7, 3, 2, 10, 6, 12, 16, 20, 21, 13, 17, 5, 22, 14, 15, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def relativePerm (b : Fin 2) : Equiv.Perm (Fin 23) :=
  if b = 0 then relativePerm0 else relativePerm1

theorem relative_correct (b : Fin 2) :
    relativePerm b = transportPerm⁻¹ * (if b = 0 then quintetMovePerm else heptadMovePerm) * transportPerm := by
  fin_cases b <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

private def decode (a b : Fin 23) : Fin 128 :=
  (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 3, 0, 0, 4, 0, 5, 0, 0, 0, 6, 0, 7, 0, 0, 8, 0, 9, 0, 0, 0, 10, 0, 11, 0, 0, 0, 0, 12, 0, 13, 0, 0, 0, 14, 0, 15, 0, 0, 16, 0, 17, 0, 0, 0, 18, 0, 19, 0, 0, 20, 0, 21, 0, 0, 0, 22, 0, 23, 0, 0, 24, 0, 25, 0, 0, 0, 26, 0, 27, 0, 0, 0, 0, 28, 0, 29, 0, 0, 0, 30, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 33, 0, 0, 0, 34, 0, 35, 0, 0, 36, 0, 37, 0, 0, 0, 38, 0, 39, 0, 0, 40, 0, 41, 0, 0, 0, 42, 0, 43, 0, 0, 0, 0, 44, 0, 45, 0, 0, 0, 46, 0, 47, 0, 0, 48, 0, 49, 0, 0, 0, 50, 0, 51, 0, 0, 52, 0, 53, 0, 0, 0, 54, 0, 55, 0, 0, 56, 0, 57, 0, 0, 0, 58, 0, 59, 0, 0, 0, 0, 60, 0, 61, 0, 0, 0, 62, 0, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 65, 0, 0, 0, 66, 0, 67, 0, 0, 0, 0, 68, 0, 69, 0, 0, 0, 70, 0, 71, 0, 0, 72, 0, 73, 0, 0, 0, 74, 0, 75, 0, 0, 76, 0, 77, 0, 0, 0, 78, 0, 79, 0, 0, 80, 0, 81, 0, 0, 0, 82, 0, 83, 0, 0, 0, 0, 84, 0, 85, 0, 0, 0, 86, 0, 87, 0, 0, 88, 0, 89, 0, 0, 0, 90, 0, 91, 0, 0, 92, 0, 93, 0, 0, 0, 94, 0, 95, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 0, 97, 0, 0, 0, 98, 0, 99, 0, 0, 0, 0, 100, 0, 101, 0, 0, 0, 102, 0, 103, 0, 0, 104, 0, 105, 0, 0, 0, 106, 0, 107, 0, 0, 108, 0, 109, 0, 0, 0, 110, 0, 111, 0, 0, 112, 0, 113, 0, 0, 0, 114, 0, 115, 0, 0, 0, 0, 116, 0, 117, 0, 0, 0, 118, 0, 119, 0, 0, 120, 0, 121, 0, 0, 0, 122, 0, 123, 0, 0, 124, 0, 125, 0, 0, 0, 126, 0, 127, 0] : Array (Fin 128))[23 * a.val + b.val]'(by change 23 * a.val + b.val < 529; omega)

private theorem decode_correct : ∀ i, decode (pointTable i 1) (pointTable i 2) = i := by
  decide +kernel

private def conjugateIndex (b : Fin 2) (i : Fin 128) : Fin 128 :=
  let p := relativePerm b * perm i * (relativePerm b)⁻¹
  decode (p 1) (p 2)

private theorem intersection_0_0 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 0 + j.val, by omega⟩
    (∀ x, (relativePerm 0 * perm i * (relativePerm 0)⁻¹) x =
      pointTable (conjugateIndex 0 i) x) → ∃ a, i = candidateIndex 0 a := by
  decide +kernel

private theorem intersection_0_1 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 1 + j.val, by omega⟩
    (∀ x, (relativePerm 0 * perm i * (relativePerm 0)⁻¹) x =
      pointTable (conjugateIndex 0 i) x) → ∃ a, i = candidateIndex 0 a := by
  decide +kernel

private theorem intersection_0_2 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 2 + j.val, by omega⟩
    (∀ x, (relativePerm 0 * perm i * (relativePerm 0)⁻¹) x =
      pointTable (conjugateIndex 0 i) x) → ∃ a, i = candidateIndex 0 a := by
  decide +kernel

private theorem intersection_0_3 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 3 + j.val, by omega⟩
    (∀ x, (relativePerm 0 * perm i * (relativePerm 0)⁻¹) x =
      pointTable (conjugateIndex 0 i) x) → ∃ a, i = candidateIndex 0 a := by
  decide +kernel

private theorem intersection_0_4 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 4 + j.val, by omega⟩
    (∀ x, (relativePerm 0 * perm i * (relativePerm 0)⁻¹) x =
      pointTable (conjugateIndex 0 i) x) → ∃ a, i = candidateIndex 0 a := by
  decide +kernel

private theorem intersection_0_5 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 5 + j.val, by omega⟩
    (∀ x, (relativePerm 0 * perm i * (relativePerm 0)⁻¹) x =
      pointTable (conjugateIndex 0 i) x) → ∃ a, i = candidateIndex 0 a := by
  decide +kernel

private theorem intersection_0_6 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 6 + j.val, by omega⟩
    (∀ x, (relativePerm 0 * perm i * (relativePerm 0)⁻¹) x =
      pointTable (conjugateIndex 0 i) x) → ∃ a, i = candidateIndex 0 a := by
  decide +kernel

private theorem intersection_0_7 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 7 + j.val, by omega⟩
    (∀ x, (relativePerm 0 * perm i * (relativePerm 0)⁻¹) x =
      pointTable (conjugateIndex 0 i) x) → ∃ a, i = candidateIndex 0 a := by
  decide +kernel

private theorem intersection_1_0 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 0 + j.val, by omega⟩
    (∀ x, (relativePerm 1 * perm i * (relativePerm 1)⁻¹) x =
      pointTable (conjugateIndex 1 i) x) → ∃ a, i = candidateIndex 1 a := by
  decide +kernel

private theorem intersection_1_1 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 1 + j.val, by omega⟩
    (∀ x, (relativePerm 1 * perm i * (relativePerm 1)⁻¹) x =
      pointTable (conjugateIndex 1 i) x) → ∃ a, i = candidateIndex 1 a := by
  decide +kernel

private theorem intersection_1_2 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 2 + j.val, by omega⟩
    (∀ x, (relativePerm 1 * perm i * (relativePerm 1)⁻¹) x =
      pointTable (conjugateIndex 1 i) x) → ∃ a, i = candidateIndex 1 a := by
  decide +kernel

private theorem intersection_1_3 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 3 + j.val, by omega⟩
    (∀ x, (relativePerm 1 * perm i * (relativePerm 1)⁻¹) x =
      pointTable (conjugateIndex 1 i) x) → ∃ a, i = candidateIndex 1 a := by
  decide +kernel

private theorem intersection_1_4 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 4 + j.val, by omega⟩
    (∀ x, (relativePerm 1 * perm i * (relativePerm 1)⁻¹) x =
      pointTable (conjugateIndex 1 i) x) → ∃ a, i = candidateIndex 1 a := by
  decide +kernel

private theorem intersection_1_5 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 5 + j.val, by omega⟩
    (∀ x, (relativePerm 1 * perm i * (relativePerm 1)⁻¹) x =
      pointTable (conjugateIndex 1 i) x) → ∃ a, i = candidateIndex 1 a := by
  decide +kernel

private theorem intersection_1_6 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 6 + j.val, by omega⟩
    (∀ x, (relativePerm 1 * perm i * (relativePerm 1)⁻¹) x =
      pointTable (conjugateIndex 1 i) x) → ∃ a, i = candidateIndex 1 a := by
  decide +kernel

private theorem intersection_1_7 : ∀ (j : Fin 16),
    let i : Fin 128 := ⟨16 * 7 + j.val, by omega⟩
    (∀ x, (relativePerm 1 * perm i * (relativePerm 1)⁻¹) x =
      pointTable (conjugateIndex 1 i) x) → ∃ a, i = candidateIndex 1 a := by
  decide +kernel

private theorem intersection_chunks (b : Fin 2) (k : Fin 8) (j : Fin 16) :
    let i : Fin 128 := ⟨16 * k.val + j.val, by omega⟩
    (∀ x, (relativePerm b * perm i * (relativePerm b)⁻¹) x =
      pointTable (conjugateIndex b i) x) → ∃ a, i = candidateIndex b a := by
  fin_cases b <;> fin_cases k
  · exact intersection_0_0 j
  · exact intersection_0_1 j
  · exact intersection_0_2 j
  · exact intersection_0_3 j
  · exact intersection_0_4 j
  · exact intersection_0_5 j
  · exact intersection_0_6 j
  · exact intersection_0_7 j
  · exact intersection_1_0 j
  · exact intersection_1_1 j
  · exact intersection_1_2 j
  · exact intersection_1_3 j
  · exact intersection_1_4 j
  · exact intersection_1_5 j
  · exact intersection_1_6 j
  · exact intersection_1_7 j

private theorem intersection_test (b : Fin 2) (i : Fin 128)
    (h : ∀ x, (relativePerm b * perm i * (relativePerm b)⁻¹) x =
      pointTable (conjugateIndex b i) x) : ∃ a, i = candidateIndex b a := by
  let k : Fin 8 := ⟨i.val / 16, by omega⟩
  let j : Fin 16 := ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  have hi : i = ⟨16 * k.val + j.val, by omega⟩ := Fin.ext (by dsimp [k,j]; omega)
  rw [hi] at h ⊢
  exact intersection_chunks b k j h

/-- Exact conjugacy of listed permutations forces membership in the specified sublist. -/
theorem intersection_indices (b : Fin 2) (i j : Fin 128)
    (hconj : relativePerm b * perm i * (relativePerm b)⁻¹ = perm j) :
    ∃ a, i = candidateIndex b a := by
  have hj : conjugateIndex b i = j := by
    change decode ((relativePerm b * perm i * (relativePerm b)⁻¹) 1)
      ((relativePerm b * perm i * (relativePerm b)⁻¹) 2) = j
    rw [hconj]
    exact decode_correct j
  apply intersection_test b i
  intro x
  rw [hj]
  exact Equiv.congr_fun hconj x

end Sporadic.Mathieu.M23Geometry.CommonFour
