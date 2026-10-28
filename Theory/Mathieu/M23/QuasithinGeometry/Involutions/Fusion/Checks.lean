module

public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Fusion.Data

/-!
# Kernel checks for the finite M23 Sylow list

Generator transitions certify closure of the list under arbitrary words.
The two point images at 1 and 2 decode its indices, proving distinctness.
The final check gives a conjugating word for every nonidentity entry squaring
to one. These checks implement the finite step in Lemma 5.2.21 of
Aschbacher--Smith, *The Classification of Quasithin Groups*, printed p.657.
-/

namespace Sporadic.Mathieu.M23Geometry.FusionCertificate
open Theory.GroupTheory

set_option maxRecDepth 100000

-- Check bounded point tables separately to keep kernel reduction small.
set_option Elab.async false

private def generatorPoint : Fin 6 → Fin 23 → Fin 23 :=
  ![![0, 4, 14, 10, 20, 17, 6, 2, 16, 8, 22, 18, 12, 9, 19, 3, 13, 5, 11, 7, 21, 1, 15],
    ![0, 1, 10, 22, 13, 18, 6, 14, 21, 9, 2, 17, 12, 4, 7, 19, 16, 11, 5, 15, 20, 8, 3],
    ![0, 1, 4, 3, 2, 17, 12, 7, 10, 9, 8, 11, 6, 19, 22, 21, 20, 5, 18, 13, 16, 15, 14],
    ![0, 21, 7, 15, 1, 17, 6, 19, 9, 13, 3, 18, 12, 16, 2, 22, 8, 5, 11, 14, 4, 20, 10],
    ![0, 1, 10, 22, 13, 18, 6, 14, 21, 9, 2, 17, 12, 4, 7, 19, 16, 11, 5, 15, 20, 8, 3],
    ![0, 1, 4, 3, 2, 17, 12, 7, 10, 9, 8, 11, 6, 19, 22, 21, 20, 5, 18, 13, 16, 15, 14]]

private theorem generatorPoint_eq : ∀ (i : Fin 6) (x : Fin 23),
    generatorPoint i x = gen i x := by decide +kernel

private def wordPoint : List (Fin 6) → Fin 23 → Fin 23
  | [], x => x
  | i :: w, x => generatorPoint i (wordPoint w x)

private theorem evalWord_apply (w : List (Fin 6)) (x : Fin 23) :
    evalWord gen w x = wordPoint w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change gen i (evalWord gen w x) = generatorPoint i (wordPoint w x)
    rw [ih, generatorPoint_eq]

private def index (k : Fin 8) (j : Fin 16) : Fin 128 :=
  ⟨16 * k.val + j.val, by omega⟩

private theorem from_chunks {P : Fin 128 → Prop}
    (h : ∀ k : Fin 8, ∀ j : Fin 16, P (index k j)) (i : Fin 128) : P i := by
  let k : Fin 8 := ⟨i.val / 16, by omega⟩
  let j : Fin 16 := ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  have hi : index k j = i := by
    apply Fin.ext
    dsimp [index, k, j]
    omega
  rw [← hi]
  exact h k j

private theorem word_chunk0 : ∀ (j : Fin 16) (x : Fin 23),
    wordPoint (representativeWord (index 0 j)) x = pointTable (index 0 j) x := by
  decide +kernel

private theorem word_chunk1 : ∀ (j : Fin 16) (x : Fin 23),
    wordPoint (representativeWord (index 1 j)) x = pointTable (index 1 j) x := by
  decide +kernel

private theorem word_chunk2 : ∀ (j : Fin 16) (x : Fin 23),
    wordPoint (representativeWord (index 2 j)) x = pointTable (index 2 j) x := by
  decide +kernel

private theorem word_chunk3 : ∀ (j : Fin 16) (x : Fin 23),
    wordPoint (representativeWord (index 3 j)) x = pointTable (index 3 j) x := by
  decide +kernel

private theorem word_chunk4 : ∀ (j : Fin 16) (x : Fin 23),
    wordPoint (representativeWord (index 4 j)) x = pointTable (index 4 j) x := by
  decide +kernel

private theorem word_chunk5 : ∀ (j : Fin 16) (x : Fin 23),
    wordPoint (representativeWord (index 5 j)) x = pointTable (index 5 j) x := by
  decide +kernel

private theorem word_chunk6 : ∀ (j : Fin 16) (x : Fin 23),
    wordPoint (representativeWord (index 6 j)) x = pointTable (index 6 j) x := by
  decide +kernel

private theorem word_chunk7 : ∀ (j : Fin 16) (x : Fin 23),
    wordPoint (representativeWord (index 7 j)) x = pointTable (index 7 j) x := by
  decide +kernel

private theorem word_points (i : Fin 128) : ∀ x : Fin 23,
    wordPoint (representativeWord i) x = pointTable i x := by
  apply from_chunks (i := i)
  intro k
  fin_cases k
  · exact word_chunk0
  · exact word_chunk1
  · exact word_chunk2
  · exact word_chunk3
  · exact word_chunk4
  · exact word_chunk5
  · exact word_chunk6
  · exact word_chunk7

public theorem representativeWord_eval (i : Fin 128) :
    evalWord gen (representativeWord i) = perm i := by
  apply Equiv.ext
  intro x
  exact (evalWord_apply _ x).trans (word_points i x)

public theorem initial : perm 0 = 1 := by decide +kernel

private theorem step_chunk0_0 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 0 (pointTable (index 0 j) x) =
      pointTable (step 0 (index 0 j)) x := by
  decide +kernel

private theorem step_chunk0_1 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 0 (pointTable (index 1 j) x) =
      pointTable (step 0 (index 1 j)) x := by
  decide +kernel

private theorem step_chunk0_2 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 0 (pointTable (index 2 j) x) =
      pointTable (step 0 (index 2 j)) x := by
  decide +kernel

private theorem step_chunk0_3 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 0 (pointTable (index 3 j) x) =
      pointTable (step 0 (index 3 j)) x := by
  decide +kernel

private theorem step_chunk0_4 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 0 (pointTable (index 4 j) x) =
      pointTable (step 0 (index 4 j)) x := by
  decide +kernel

private theorem step_chunk0_5 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 0 (pointTable (index 5 j) x) =
      pointTable (step 0 (index 5 j)) x := by
  decide +kernel

private theorem step_chunk0_6 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 0 (pointTable (index 6 j) x) =
      pointTable (step 0 (index 6 j)) x := by
  decide +kernel

private theorem step_chunk0_7 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 0 (pointTable (index 7 j) x) =
      pointTable (step 0 (index 7 j)) x := by
  decide +kernel

private theorem step_chunk1_0 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 1 (pointTable (index 0 j) x) =
      pointTable (step 1 (index 0 j)) x := by
  decide +kernel

private theorem step_chunk1_1 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 1 (pointTable (index 1 j) x) =
      pointTable (step 1 (index 1 j)) x := by
  decide +kernel

private theorem step_chunk1_2 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 1 (pointTable (index 2 j) x) =
      pointTable (step 1 (index 2 j)) x := by
  decide +kernel

private theorem step_chunk1_3 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 1 (pointTable (index 3 j) x) =
      pointTable (step 1 (index 3 j)) x := by
  decide +kernel

private theorem step_chunk1_4 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 1 (pointTable (index 4 j) x) =
      pointTable (step 1 (index 4 j)) x := by
  decide +kernel

private theorem step_chunk1_5 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 1 (pointTable (index 5 j) x) =
      pointTable (step 1 (index 5 j)) x := by
  decide +kernel

private theorem step_chunk1_6 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 1 (pointTable (index 6 j) x) =
      pointTable (step 1 (index 6 j)) x := by
  decide +kernel

private theorem step_chunk1_7 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 1 (pointTable (index 7 j) x) =
      pointTable (step 1 (index 7 j)) x := by
  decide +kernel

private theorem step_chunk2_0 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 2 (pointTable (index 0 j) x) =
      pointTable (step 2 (index 0 j)) x := by
  decide +kernel

private theorem step_chunk2_1 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 2 (pointTable (index 1 j) x) =
      pointTable (step 2 (index 1 j)) x := by
  decide +kernel

private theorem step_chunk2_2 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 2 (pointTable (index 2 j) x) =
      pointTable (step 2 (index 2 j)) x := by
  decide +kernel

private theorem step_chunk2_3 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 2 (pointTable (index 3 j) x) =
      pointTable (step 2 (index 3 j)) x := by
  decide +kernel

private theorem step_chunk2_4 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 2 (pointTable (index 4 j) x) =
      pointTable (step 2 (index 4 j)) x := by
  decide +kernel

private theorem step_chunk2_5 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 2 (pointTable (index 5 j) x) =
      pointTable (step 2 (index 5 j)) x := by
  decide +kernel

private theorem step_chunk2_6 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 2 (pointTable (index 6 j) x) =
      pointTable (step 2 (index 6 j)) x := by
  decide +kernel

private theorem step_chunk2_7 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 2 (pointTable (index 7 j) x) =
      pointTable (step 2 (index 7 j)) x := by
  decide +kernel

private theorem step_chunk3_0 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 3 (pointTable (index 0 j) x) =
      pointTable (step 3 (index 0 j)) x := by
  decide +kernel

private theorem step_chunk3_1 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 3 (pointTable (index 1 j) x) =
      pointTable (step 3 (index 1 j)) x := by
  decide +kernel

private theorem step_chunk3_2 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 3 (pointTable (index 2 j) x) =
      pointTable (step 3 (index 2 j)) x := by
  decide +kernel

private theorem step_chunk3_3 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 3 (pointTable (index 3 j) x) =
      pointTable (step 3 (index 3 j)) x := by
  decide +kernel

private theorem step_chunk3_4 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 3 (pointTable (index 4 j) x) =
      pointTable (step 3 (index 4 j)) x := by
  decide +kernel

private theorem step_chunk3_5 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 3 (pointTable (index 5 j) x) =
      pointTable (step 3 (index 5 j)) x := by
  decide +kernel

private theorem step_chunk3_6 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 3 (pointTable (index 6 j) x) =
      pointTable (step 3 (index 6 j)) x := by
  decide +kernel

private theorem step_chunk3_7 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 3 (pointTable (index 7 j) x) =
      pointTable (step 3 (index 7 j)) x := by
  decide +kernel

private theorem step_chunk4_0 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 4 (pointTable (index 0 j) x) =
      pointTable (step 4 (index 0 j)) x := by
  decide +kernel

private theorem step_chunk4_1 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 4 (pointTable (index 1 j) x) =
      pointTable (step 4 (index 1 j)) x := by
  decide +kernel

private theorem step_chunk4_2 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 4 (pointTable (index 2 j) x) =
      pointTable (step 4 (index 2 j)) x := by
  decide +kernel

private theorem step_chunk4_3 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 4 (pointTable (index 3 j) x) =
      pointTable (step 4 (index 3 j)) x := by
  decide +kernel

private theorem step_chunk4_4 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 4 (pointTable (index 4 j) x) =
      pointTable (step 4 (index 4 j)) x := by
  decide +kernel

private theorem step_chunk4_5 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 4 (pointTable (index 5 j) x) =
      pointTable (step 4 (index 5 j)) x := by
  decide +kernel

private theorem step_chunk4_6 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 4 (pointTable (index 6 j) x) =
      pointTable (step 4 (index 6 j)) x := by
  decide +kernel

private theorem step_chunk4_7 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 4 (pointTable (index 7 j) x) =
      pointTable (step 4 (index 7 j)) x := by
  decide +kernel

private theorem step_chunk5_0 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 5 (pointTable (index 0 j) x) =
      pointTable (step 5 (index 0 j)) x := by
  decide +kernel

private theorem step_chunk5_1 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 5 (pointTable (index 1 j) x) =
      pointTable (step 5 (index 1 j)) x := by
  decide +kernel

private theorem step_chunk5_2 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 5 (pointTable (index 2 j) x) =
      pointTable (step 5 (index 2 j)) x := by
  decide +kernel

private theorem step_chunk5_3 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 5 (pointTable (index 3 j) x) =
      pointTable (step 5 (index 3 j)) x := by
  decide +kernel

private theorem step_chunk5_4 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 5 (pointTable (index 4 j) x) =
      pointTable (step 5 (index 4 j)) x := by
  decide +kernel

private theorem step_chunk5_5 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 5 (pointTable (index 5 j) x) =
      pointTable (step 5 (index 5 j)) x := by
  decide +kernel

private theorem step_chunk5_6 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 5 (pointTable (index 6 j) x) =
      pointTable (step 5 (index 6 j)) x := by
  decide +kernel

private theorem step_chunk5_7 : ∀ (j : Fin 16) (x : Fin 23),
    generatorPoint 5 (pointTable (index 7 j) x) =
      pointTable (step 5 (index 7 j)) x := by
  decide +kernel

private theorem step_points (g : Fin 6) (j : Fin 128) : ∀ x : Fin 23,
    generatorPoint g (pointTable j x) = pointTable (step g j) x := by
  apply from_chunks (i := j)
  intro k
  fin_cases g <;> fin_cases k
  · exact step_chunk0_0
  · exact step_chunk0_1
  · exact step_chunk0_2
  · exact step_chunk0_3
  · exact step_chunk0_4
  · exact step_chunk0_5
  · exact step_chunk0_6
  · exact step_chunk0_7
  · exact step_chunk1_0
  · exact step_chunk1_1
  · exact step_chunk1_2
  · exact step_chunk1_3
  · exact step_chunk1_4
  · exact step_chunk1_5
  · exact step_chunk1_6
  · exact step_chunk1_7
  · exact step_chunk2_0
  · exact step_chunk2_1
  · exact step_chunk2_2
  · exact step_chunk2_3
  · exact step_chunk2_4
  · exact step_chunk2_5
  · exact step_chunk2_6
  · exact step_chunk2_7
  · exact step_chunk3_0
  · exact step_chunk3_1
  · exact step_chunk3_2
  · exact step_chunk3_3
  · exact step_chunk3_4
  · exact step_chunk3_5
  · exact step_chunk3_6
  · exact step_chunk3_7
  · exact step_chunk4_0
  · exact step_chunk4_1
  · exact step_chunk4_2
  · exact step_chunk4_3
  · exact step_chunk4_4
  · exact step_chunk4_5
  · exact step_chunk4_6
  · exact step_chunk4_7
  · exact step_chunk5_0
  · exact step_chunk5_1
  · exact step_chunk5_2
  · exact step_chunk5_3
  · exact step_chunk5_4
  · exact step_chunk5_5
  · exact step_chunk5_6
  · exact step_chunk5_7

public theorem step_correct (i : Fin 6) (j : Fin 128) :
    gen i * perm j = perm (step i j) := by
  apply Equiv.ext
  intro x
  exact (generatorPoint_eq i (pointTable j x)).symm.trans (step_points i j x)

private def decode : Fin 23 → Fin 23 → Fin 128 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 3, 0, 0, 4, 0, 5, 0, 0, 0, 6, 0, 7, 0],
    ![0, 8, 0, 9, 0, 0, 0, 10, 0, 11, 0, 0, 0, 0, 12, 0, 13, 0, 0, 0, 14, 0, 15],
    ![0, 0, 16, 0, 17, 0, 0, 0, 18, 0, 19, 0, 0, 20, 0, 21, 0, 0, 0, 22, 0, 23, 0],
    ![0, 24, 0, 25, 0, 0, 0, 26, 0, 27, 0, 0, 0, 0, 28, 0, 29, 0, 0, 0, 30, 0, 31],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 32, 0, 33, 0, 0, 0, 34, 0, 35, 0, 0, 36, 0, 37, 0, 0, 0, 38, 0, 39, 0],
    ![0, 40, 0, 41, 0, 0, 0, 42, 0, 43, 0, 0, 0, 0, 44, 0, 45, 0, 0, 0, 46, 0, 47],
    ![0, 0, 48, 0, 49, 0, 0, 0, 50, 0, 51, 0, 0, 52, 0, 53, 0, 0, 0, 54, 0, 55, 0],
    ![0, 56, 0, 57, 0, 0, 0, 58, 0, 59, 0, 0, 0, 0, 60, 0, 61, 0, 0, 0, 62, 0, 63],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 64, 0, 65, 0, 0, 0, 66, 0, 67, 0, 0, 0, 0, 68, 0, 69, 0, 0, 0, 70, 0, 71],
    ![0, 0, 72, 0, 73, 0, 0, 0, 74, 0, 75, 0, 0, 76, 0, 77, 0, 0, 0, 78, 0, 79, 0],
    ![0, 80, 0, 81, 0, 0, 0, 82, 0, 83, 0, 0, 0, 0, 84, 0, 85, 0, 0, 0, 86, 0, 87],
    ![0, 0, 88, 0, 89, 0, 0, 0, 90, 0, 91, 0, 0, 92, 0, 93, 0, 0, 0, 94, 0, 95, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 96, 0, 97, 0, 0, 0, 98, 0, 99, 0, 0, 0, 0, 100, 0, 101, 0, 0, 0, 102, 0, 103],
    ![0, 0, 104, 0, 105, 0, 0, 0, 106, 0, 107, 0, 0, 108, 0, 109, 0, 0, 0, 110, 0, 111, 0],
    ![0, 112, 0, 113, 0, 0, 0, 114, 0, 115, 0, 0, 0, 0, 116, 0, 117, 0, 0, 0, 118, 0, 119],
    ![0, 0, 120, 0, 121, 0, 0, 0, 122, 0, 123, 0, 0, 124, 0, 125, 0, 0, 0, 126, 0, 127, 0]]

private theorem decode_correct : ∀ i : Fin 128,
    decode (pointTable i 1) (pointTable i 2) = i := by
  decide +kernel

public theorem perm_injective : Function.Injective perm := by
  intro i j hij
  have h := congrArg (fun p : Equiv.Perm (Fin 23) => decode (p 1) (p 2)) hij
  change decode (pointTable i 1) (pointTable i 2) =
    decode (pointTable j 1) (pointTable j 2) at h
  simpa only [decode_correct] using h

/-- Every listed nonidentity element squaring to one is explicitly conjugate
in M23 to the first certified M22 generator. -/
public theorem conjugation_check : ∀ i : Fin 128,
    perm i * perm i = 1 → perm i ≠ 1 →
    evalWord ambientGen (conjugatingWord i) * m23M22GeneratorA *
      (evalWord ambientGen (conjugatingWord i))⁻¹ = perm i := by
  intro i
  fin_cases i <;> decide +kernel

end Sporadic.Mathieu.M23Geometry.FusionCertificate
