module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Certificate.Basic

/-!
# The product of endpoint restrictions covers all candidates

For each candidate triple, a positive word in the left restriction
generators and either the identity or the single right restriction
certify the factor equation on every overlap row. Word induction later
identifies an arbitrary overlap automorphism with its candidate values.

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

private def candidateRow (b i : Fin 16) : Fin 256 :=
  ⟨16*b.val + i.val, by omega⟩

private theorem factors00 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 0 a)
      (eval middleMul 0 (images (candidateRow 0 a)) (middleWord i)) =
    leftFactor (candidateRow 0 a) i := by decide +kernel

private theorem factors01 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 1 a)
      (eval middleMul 0 (images (candidateRow 1 a)) (middleWord i)) =
    leftFactor (candidateRow 1 a) i := by decide +kernel

private theorem factors02 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 2 a)
      (eval middleMul 0 (images (candidateRow 2 a)) (middleWord i)) =
    leftFactor (candidateRow 2 a) i := by decide +kernel

private theorem factors03 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 3 a)
      (eval middleMul 0 (images (candidateRow 3 a)) (middleWord i)) =
    leftFactor (candidateRow 3 a) i := by decide +kernel

private theorem factors04 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 4 a)
      (eval middleMul 0 (images (candidateRow 4 a)) (middleWord i)) =
    leftFactor (candidateRow 4 a) i := by decide +kernel

private theorem factors05 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 5 a)
      (eval middleMul 0 (images (candidateRow 5 a)) (middleWord i)) =
    leftFactor (candidateRow 5 a) i := by decide +kernel

private theorem factors06 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 6 a)
      (eval middleMul 0 (images (candidateRow 6 a)) (middleWord i)) =
    leftFactor (candidateRow 6 a) i := by decide +kernel

private theorem factors07 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 7 a)
      (eval middleMul 0 (images (candidateRow 7 a)) (middleWord i)) =
    leftFactor (candidateRow 7 a) i := by decide +kernel

private theorem factors08 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 8 a)
      (eval middleMul 0 (images (candidateRow 8 a)) (middleWord i)) =
    leftFactor (candidateRow 8 a) i := by decide +kernel

private theorem factors09 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 9 a)
      (eval middleMul 0 (images (candidateRow 9 a)) (middleWord i)) =
    leftFactor (candidateRow 9 a) i := by decide +kernel

private theorem factors10 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 10 a)
      (eval middleMul 0 (images (candidateRow 10 a)) (middleWord i)) =
    leftFactor (candidateRow 10 a) i := by decide +kernel

private theorem factors11 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 11 a)
      (eval middleMul 0 (images (candidateRow 11 a)) (middleWord i)) =
    leftFactor (candidateRow 11 a) i := by decide +kernel

private theorem factors12 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 12 a)
      (eval middleMul 0 (images (candidateRow 12 a)) (middleWord i)) =
    leftFactor (candidateRow 12 a) i := by decide +kernel

private theorem factors13 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 13 a)
      (eval middleMul 0 (images (candidateRow 13 a)) (middleWord i)) =
    leftFactor (candidateRow 13 a) i := by decide +kernel

private theorem factors14 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 14 a)
      (eval middleMul 0 (images (candidateRow 14 a)) (middleWord i)) =
    leftFactor (candidateRow 14 a) i := by decide +kernel

private theorem factors15 : ∀ a : Fin 16, ∀ i : Fin 64,
    rightFactor (candidateRow 15 a)
      (eval middleMul 0 (images (candidateRow 15 a)) (middleWord i)) =
    leftFactor (candidateRow 15 a) i := by decide +kernel

theorem factors : ∀ k i,
    rightFactor k (eval middleMul 0 (images k) (middleWord i)) = leftFactor k i := by
  have h : ∀ b a : Fin 16, ∀ i : Fin 64,
      rightFactor (candidateRow b a)
        (eval middleMul 0 (images (candidateRow b a)) (middleWord i)) =
      leftFactor (candidateRow b a) i := by
    intro b
    fin_cases b
    · exact factors00
    · exact factors01
    · exact factors02
    · exact factors03
    · exact factors04
    · exact factors05
    · exact factors06
    · exact factors07
    · exact factors08
    · exact factors09
    · exact factors10
    · exact factors11
    · exact factors12
    · exact factors13
    · exact factors14
    · exact factors15
  intro k i
  have he : candidateRow (@Fin.divNat 16 16 k) (@Fin.modNat 16 16 k) = k := by
    apply Fin.ext
    simp only [candidateRow, Fin.divNat, Fin.modNat]
    omega
  simpa only [he] using h (@Fin.divNat 16 16 k) (@Fin.modNat 16 16 k) i

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Certificate
