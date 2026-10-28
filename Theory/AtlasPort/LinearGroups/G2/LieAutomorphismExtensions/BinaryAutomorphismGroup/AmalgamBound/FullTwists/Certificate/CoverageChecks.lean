module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Certificate.Basic

/-!
# Exhausting the overlap generator images

The order-eight condition restricts the first image to sixteen choices.
Six necessary positive relations and nontriviality of the other generators
then restrict all triples to the published 256 candidates. This checks only
necessary relations and does not assume completeness of a presentation.

All finite certificates are checked by the Lean kernel. The original table
numbering and ATLAS root conventions are retained; attribution and the
ATLAS Research and Attribution License 1.0 are recorded in `Data`.
Source application: Aschbacher--Smith F.1.12(I)(3), q = 2, pp.262--263.
-/

-- The full 192 by 192 prototype used 4 GB. Small, sequential kernel checks
-- keep peak memory near the import baseline (2 GB) with default threading.
set_option Elab.async false

public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Certificate

theorem middle_idempotent : ∀ i, middleMul i i = i → i = 0 := by decide +kernel

theorem middle_words : ∀ i, eval middleMul 0 generators (middleWord i) = i := by decide +kernel

theorem middle_relations : ∀ w ∈ relations, eval middleMul 0 generators w = 0 := by decide +kernel

theorem middle_fourth : eval middleMul 0 generators [0, 0, 0, 0] ≠ 0 := by decide +kernel

theorem first_coverage : ∀ x : Fin 64,
    eval middleMul 0 ![x, 0, 0] [0, 0, 0, 0] ≠ 0 → firstOption (firstIndex x) = x := by decide +kernel

private theorem image_coverage00 : ∀ y z : Fin 64,
    Candidate (firstOption 0) y z →
      firstImage (candidateNumber 0 y z) = firstOption 0 ∧
      secondImage (candidateNumber 0 y z) = y ∧
      thirdImage (candidateNumber 0 y z) = z := by decide +kernel

private theorem image_coverage01 : ∀ y z : Fin 64,
    Candidate (firstOption 1) y z →
      firstImage (candidateNumber 1 y z) = firstOption 1 ∧
      secondImage (candidateNumber 1 y z) = y ∧
      thirdImage (candidateNumber 1 y z) = z := by decide +kernel

private theorem image_coverage02 : ∀ y z : Fin 64,
    Candidate (firstOption 2) y z →
      firstImage (candidateNumber 2 y z) = firstOption 2 ∧
      secondImage (candidateNumber 2 y z) = y ∧
      thirdImage (candidateNumber 2 y z) = z := by decide +kernel

private theorem image_coverage03 : ∀ y z : Fin 64,
    Candidate (firstOption 3) y z →
      firstImage (candidateNumber 3 y z) = firstOption 3 ∧
      secondImage (candidateNumber 3 y z) = y ∧
      thirdImage (candidateNumber 3 y z) = z := by decide +kernel

private theorem image_coverage04 : ∀ y z : Fin 64,
    Candidate (firstOption 4) y z →
      firstImage (candidateNumber 4 y z) = firstOption 4 ∧
      secondImage (candidateNumber 4 y z) = y ∧
      thirdImage (candidateNumber 4 y z) = z := by decide +kernel

private theorem image_coverage05 : ∀ y z : Fin 64,
    Candidate (firstOption 5) y z →
      firstImage (candidateNumber 5 y z) = firstOption 5 ∧
      secondImage (candidateNumber 5 y z) = y ∧
      thirdImage (candidateNumber 5 y z) = z := by decide +kernel

private theorem image_coverage06 : ∀ y z : Fin 64,
    Candidate (firstOption 6) y z →
      firstImage (candidateNumber 6 y z) = firstOption 6 ∧
      secondImage (candidateNumber 6 y z) = y ∧
      thirdImage (candidateNumber 6 y z) = z := by decide +kernel

private theorem image_coverage07 : ∀ y z : Fin 64,
    Candidate (firstOption 7) y z →
      firstImage (candidateNumber 7 y z) = firstOption 7 ∧
      secondImage (candidateNumber 7 y z) = y ∧
      thirdImage (candidateNumber 7 y z) = z := by decide +kernel

private theorem image_coverage08 : ∀ y z : Fin 64,
    Candidate (firstOption 8) y z →
      firstImage (candidateNumber 8 y z) = firstOption 8 ∧
      secondImage (candidateNumber 8 y z) = y ∧
      thirdImage (candidateNumber 8 y z) = z := by decide +kernel

private theorem image_coverage09 : ∀ y z : Fin 64,
    Candidate (firstOption 9) y z →
      firstImage (candidateNumber 9 y z) = firstOption 9 ∧
      secondImage (candidateNumber 9 y z) = y ∧
      thirdImage (candidateNumber 9 y z) = z := by decide +kernel

private theorem image_coverage10 : ∀ y z : Fin 64,
    Candidate (firstOption 10) y z →
      firstImage (candidateNumber 10 y z) = firstOption 10 ∧
      secondImage (candidateNumber 10 y z) = y ∧
      thirdImage (candidateNumber 10 y z) = z := by decide +kernel

private theorem image_coverage11 : ∀ y z : Fin 64,
    Candidate (firstOption 11) y z →
      firstImage (candidateNumber 11 y z) = firstOption 11 ∧
      secondImage (candidateNumber 11 y z) = y ∧
      thirdImage (candidateNumber 11 y z) = z := by decide +kernel

private theorem image_coverage12 : ∀ y z : Fin 64,
    Candidate (firstOption 12) y z →
      firstImage (candidateNumber 12 y z) = firstOption 12 ∧
      secondImage (candidateNumber 12 y z) = y ∧
      thirdImage (candidateNumber 12 y z) = z := by decide +kernel

private theorem image_coverage13 : ∀ y z : Fin 64,
    Candidate (firstOption 13) y z →
      firstImage (candidateNumber 13 y z) = firstOption 13 ∧
      secondImage (candidateNumber 13 y z) = y ∧
      thirdImage (candidateNumber 13 y z) = z := by decide +kernel

private theorem image_coverage14 : ∀ y z : Fin 64,
    Candidate (firstOption 14) y z →
      firstImage (candidateNumber 14 y z) = firstOption 14 ∧
      secondImage (candidateNumber 14 y z) = y ∧
      thirdImage (candidateNumber 14 y z) = z := by decide +kernel

private theorem image_coverage15 : ∀ y z : Fin 64,
    Candidate (firstOption 15) y z →
      firstImage (candidateNumber 15 y z) = firstOption 15 ∧
      secondImage (candidateNumber 15 y z) = y ∧
      thirdImage (candidateNumber 15 y z) = z := by decide +kernel

theorem image_coverage : ∀ a : Fin 16, ∀ y z : Fin 64,
    Candidate (firstOption a) y z →
      firstImage (candidateNumber a y z) = firstOption a ∧
      secondImage (candidateNumber a y z) = y ∧
      thirdImage (candidateNumber a y z) = z := by
  intro a
  fin_cases a
  · exact image_coverage00
  · exact image_coverage01
  · exact image_coverage02
  · exact image_coverage03
  · exact image_coverage04
  · exact image_coverage05
  · exact image_coverage06
  · exact image_coverage07
  · exact image_coverage08
  · exact image_coverage09
  · exact image_coverage10
  · exact image_coverage11
  · exact image_coverage12
  · exact image_coverage13
  · exact image_coverage14
  · exact image_coverage15

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Certificate
