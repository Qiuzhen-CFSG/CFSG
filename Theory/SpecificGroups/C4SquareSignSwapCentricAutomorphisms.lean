module

public import Theory.SpecificGroups.C4SquareSignSwapCentricAutCertificate
public import Theory.SpecificGroups.C4SquareSignSwapCentricExceptions
import Mathlib.Tactic.FinCases

/-!
# Automorphism exclusions for the sign-and-swap candidates

The 22 candidates outside the exceptional index set have two-groups of
automorphisms. The finite certificates reconstruct a map from three generator
images, test necessary power equations and the identity fiber, and check that its
eighth power fixes all generators. Certificate soundness then gives the result
for every automorphism, without assumptions from a small-group classification.

Source: direct calculations in the coordinate model for Stellmacher (8.6)(a),
`refs/latex/stellmacher-n-group.tex`, using the normal forms from
`C4SquareSignSwapCentricGenerators`.
-/

namespace C4SquareSignSwap

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_0 : CentricAutCertificate 0 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_1 : CentricAutCertificate 1 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_2 : CentricAutCertificate 2 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_3 : CentricAutCertificate 3 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_4 : CentricAutCertificate 4 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_5 : CentricAutCertificate 5 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_6 : CentricAutCertificate 6 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_7 : CentricAutCertificate 7 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_8 : CentricAutCertificate 8 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_9 : CentricAutCertificate 9 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_10 : CentricAutCertificate 10 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_12 : CentricAutCertificate 12 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_13 : CentricAutCertificate 13 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_14 : CentricAutCertificate 14 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_15 : CentricAutCertificate 15 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_16 : CentricAutCertificate 16 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_21 : CentricAutCertificate 21 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_22 : CentricAutCertificate 22 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_23 : CentricAutCertificate 23 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_24 : CentricAutCertificate 24 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_25 : CentricAutCertificate 25 := by
  unfold CentricAutCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_27 : CentricAutCertificate 27 := by
  unfold CentricAutCertificate
  decide +kernel

private theorem certificates (i : Fin 32) (hi : ¬ centricExceptionalIndex i) :
    CentricAutCertificate i := by
  fin_cases i <;> simp_all [centricExceptionalIndex]
  · exact certificate_0
  · exact certificate_1
  · exact certificate_2
  · exact certificate_3
  · exact certificate_4
  · exact certificate_5
  · exact certificate_6
  · exact certificate_7
  · exact certificate_8
  · exact certificate_9
  · exact certificate_10
  · exact certificate_12
  · exact certificate_13
  · exact certificate_14
  · exact certificate_15
  · exact certificate_16
  · exact certificate_21
  · exact certificate_22
  · exact certificate_23
  · exact certificate_24
  · exact certificate_25
  · exact certificate_27

/-- Every nonexceptional candidate has a two-group of automorphisms. -/
public theorem centricCandidate_isPGroup_mulAut (i : Fin 32)
    (hi : ¬ centricExceptionalIndex i) : IsPGroup 2 (MulAut (centricCandidate i)) := by
  have hpad : ∀ i : Fin 32, ¬ centricExceptionalIndex i →
      centricCandidateGenerator i 3 = 1 := by decide +kernel
  exact centricAutCertificate_sound i (hpad i hi) (certificates i hi)

end C4SquareSignSwap
