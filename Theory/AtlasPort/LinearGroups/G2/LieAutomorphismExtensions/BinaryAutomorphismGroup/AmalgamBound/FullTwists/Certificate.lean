module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Certificate.SeedChecks
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Certificate.CoverageChecks
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Certificate.FactorChecks

/-!
# Complete twist coverage for the full binary G₂ coordinate amalgam

An overlap permutation preserving multiplication fixes the identity and is
determined by the images of the three published generators. Necessary
positive relations restrict these images to 256 certified candidates.
Five checked left endpoint extensions and one checked right endpoint
extension give a factor witness for each candidate. Composition supplies
both endpoint permutations and their literal overlap squares; word induction
identifies their restriction product with the original overlap permutation.

This proves the finite `TwistsVerified` contract without assuming a group
realization, endpoint extension, or an amalgam isomorphism. The independent
realization producer and `FiniteTable.Realization.factorsThrough` transport
it to actual G₂ groups. Source: Aschbacher--Smith F.1.12(I)(3), q = 2,
printed pp.262--263. The underlying root conventions and generated data
retain the ATLAS Research and Attribution License 1.0 and attribution to
Gerald Höhn and the ATLAS contributors (`LICENSES/ATLAS.txt`).
-/

public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists
namespace Certificate

private def leftExtension (k : Fin 5) : Extension leftMul leftOverlap where
  endpoint := ⟨leftSeed k, leftSeedInverse k, left_inverse k, left_inverse_rev k⟩
  middle := ⟨middleSeed k, middleSeedInverse k, middle_inverse k, middle_inverse_rev k⟩
  map_mul := left_mul k
  square := left_square k

private def rightExtension : Extension rightMul rightOverlap where
  endpoint := ⟨rightSeed, rightSeedInverse, right_inverse, right_inverse_rev⟩
  middle := ⟨rightMiddleSeed, rightMiddleSeedInverse, rightMiddle_inverse,
    rightMiddle_inverse_rev⟩
  map_mul := right_mul
  square := right_square

private def leftComplete (k : Fin 256) : Extension leftMul leftOverlap :=
  Extension.word leftExtension (factorWord k)

private def rightComplete (k : Fin 256) : Extension rightMul rightOverlap :=
  if factorRight k then rightExtension else Extension.refl rightMul rightOverlap

private theorem leftComplete_apply (k : Fin 256) (i : Fin 64) :
    (leftComplete k).middle i = leftFactor k i :=
  Extension.word_middle leftExtension (factorWord k) i

private theorem rightComplete_apply (k : Fin 256) (i : Fin 64) :
    (rightComplete k).middle i = rightFactor k i := by
  cases h : factorRight k <;> simp only [rightComplete, rightFactor, h] <;> rfl

private theorem perm_zero (d : Equiv.Perm (Fin 64))
    (hd : ∀ i j, d (middleMul i j) = middleMul (d i) (d j)) : d 0 = 0 := by
  apply middle_idempotent
  calc
    middleMul (d 0) (d 0) = d (middleMul 0 0) := (hd 0 0).symm
    _ = d 0 := congrArg d (by decide +kernel)

private theorem perm_images (d : Equiv.Perm (Fin 64))
    (hd : ∀ i j, d (middleMul i j) = middleMul (d i) (d j)) :
    ∃ k, d 1 = firstImage k ∧ d 2 = secondImage k ∧ d 3 = thirdImage k := by
  have hzero := perm_zero d hd
  have hvec : (fun a => d (generators a)) = ![d 1, d 2, d 3] := by
    funext a
    fin_cases a <;> rfl
  have hc : Candidate (d 1) (d 2) (d 3) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      apply middle_fourth
      apply d.injective
      rw [map_eval middleMul 0 d hzero hd, hvec, h, hzero]
    · intro h
      exact (by decide : (2 : Fin 64) ≠ 0) (d.injective (h.trans hzero.symm))
    · intro h
      exact (by decide : (3 : Fin 64) ≠ 0) (d.injective (h.trans hzero.symm))
    · intro w hw
      rw [← hvec, ← map_eval middleMul 0 d hzero hd, middle_relations w hw, hzero]
  have hx := first_coverage (d 1) hc.1
  have hc' : Candidate (firstOption (firstIndex (d 1))) (d 2) (d 3) := by
    rw [hx]
    exact hc
  obtain ⟨h₁, h₂, h₃⟩ := image_coverage (firstIndex (d 1)) (d 2) (d 3) hc'
  exact ⟨candidateNumber (firstIndex (d 1)) (d 2) (d 3),
    (h₁.trans hx).symm, h₂.symm, h₃.symm⟩

private theorem verified : table.TwistsVerified := by
  intro d hd
  obtain ⟨k, h₁, h₂, h₃⟩ := perm_images d hd
  have hvec : (fun a => d (generators a)) = images k := by
    funext a
    fin_cases a
    · exact h₁
    · exact h₂
    · exact h₃
  have he (i : Fin 64) : d i = eval middleMul 0 (images k) (middleWord i) := by
    calc
      d i = d (eval middleMul 0 generators (middleWord i)) :=
        congrArg d (middle_words i).symm
      _ = eval middleMul 0 (fun a => d (generators a)) (middleWord i) :=
        map_eval middleMul 0 d (perm_zero d hd) hd generators (middleWord i)
      _ = eval middleMul 0 (images k) (middleWord i) := by rw [hvec]
  let l := leftComplete k
  let r := rightComplete k
  refine ⟨{
    left := l.endpoint
    right := r.endpoint
    middleLeft := l.middle
    middleRight := r.middle
    left_mul := l.map_mul
    right_mul := r.map_mul
    left_overlap := l.square
    right_overlap := r.square
    factors := ?_ }⟩
  intro i
  apply r.middle.injective
  rw [r.middle.apply_symm_apply]
  change (rightComplete k).middle (d i) = (leftComplete k).middle i
  rw [rightComplete_apply, leftComplete_apply, he]
  exact factors k i

end Certificate

/-- Every multiplication-preserving overlap permutation has two endpoint
extensions whose restrictions factor it, with both literal squares. -/
theorem full_twistsVerified : table.TwistsVerified := Certificate.verified

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists
