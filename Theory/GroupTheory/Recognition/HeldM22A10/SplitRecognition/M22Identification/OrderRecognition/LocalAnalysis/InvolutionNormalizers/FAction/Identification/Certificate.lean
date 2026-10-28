module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FAction.Identification.Data

/-!
# Excluding impossible automorphisms by stabilizer words

For each possible last three columns of an automorphism sending z to d,
a short word either produces one of the two canonical generators or fixes z
outside the exact local stabilizer. Singular matrices are discarded by their
nonzero kernel vector. Every finite check uses kernel reduction.

Source: Janko, J. Algebra 9 (1968), Section 2, proof of Lemma 2, pp.4–5.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction.Identification

private def Verified (r : Fin 3 → Fin 16) : Prop :=
  let m : Mat := ![8, r 0, r 1, r 2]
  (∀ i : Fin 16, act m i = 0 → i = 0) →
    (∃ k : Fin 2, evalMat m (witnesses (pick r)) = seeds k) ∨
    ((evalMat m (witnesses (pick r))) 0 = 1 ∧
      ∀ j : Fin 8, evalMat m (witnesses (pick r)) ≠ localTable j)

private instance (r : Fin 3 → Fin 16) : Decidable (Verified r) :=
  inferInstanceAs (Decidable (_ → _ ∨ _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check0 : ∀ y z : Fin 16, Verified ![0, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check1 : ∀ y z : Fin 16, Verified ![1, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check2 : ∀ y z : Fin 16, Verified ![2, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check3 : ∀ y z : Fin 16, Verified ![3, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check4 : ∀ y z : Fin 16, Verified ![4, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check5 : ∀ y z : Fin 16, Verified ![5, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check6 : ∀ y z : Fin 16, Verified ![6, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check7 : ∀ y z : Fin 16, Verified ![7, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check8 : ∀ y z : Fin 16, Verified ![8, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check9 : ∀ y z : Fin 16, Verified ![9, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check10 : ∀ y z : Fin 16, Verified ![10, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check11 : ∀ y z : Fin 16, Verified ![11, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check12 : ∀ y z : Fin 16, Verified ![12, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check13 : ∀ y z : Fin 16, Verified ![13, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check14 : ∀ y z : Fin 16, Verified ![14, y, z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check15 : ∀ y z : Fin 16, Verified ![15, y, z] := by decide +kernel

private theorem verified (x y z : Fin 16) : Verified ![x, y, z] := by
  fin_cases x
  · exact check0 y z
  · exact check1 y z
  · exact check2 y z
  · exact check3 y z
  · exact check4 y z
  · exact check5 y z
  · exact check6 y z
  · exact check7 y z
  · exact check8 y z
  · exact check9 y z
  · exact check10 y z
  · exact check11 y z
  · exact check12 y z
  · exact check13 y z
  · exact check14 y z
  · exact check15 y z

public theorem matrix_certificate (m : Mat) (hm : m 0 = 8)
    (hinj : ∀ i : Fin 16, act m i = 0 → i = 0) :
    ∃ w : List (Fin 4), (∃ k : Fin 2, evalMat m w = seeds k) ∨
      ((evalMat m w) 0 = 1 ∧ ∀ j : Fin 8, evalMat m w ≠ localTable j) := by
  have he : m = ![8, m 1, m 2, m 3] := by
    funext i
    fin_cases i
    · exact hm
    · rfl
    · rfl
    · rfl
  refine ⟨witnesses (pick ![m 1, m 2, m 3]), ?_⟩
  have h := verified (m 1) (m 2) (m 3)
  change (∀ i : Fin 16, act ![8, m 1, m 2, m 3] i = 0 → i = 0) → _ at h
  have hresult :
      (∃ k : Fin 2, evalMat ![8, m 1, m 2, m 3]
        (witnesses (pick ![m 1, m 2, m 3])) = seeds k) ∨
      ((evalMat ![8, m 1, m 2, m 3] (witnesses (pick ![m 1, m 2, m 3]))) 0 = 1 ∧
        ∀ j : Fin 8, evalMat ![8, m 1, m 2, m 3]
          (witnesses (pick ![m 1, m 2, m 3])) ≠ localTable j) := h (he ▸ hinj)
  simpa only [← he] using hresult

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction.Identification
