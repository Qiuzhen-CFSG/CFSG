module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport16

/-!
# Lyons plane transport through wordB, step 18

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 18 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b120_valid : valid b119 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b120_check : check atlasBRows b119 b120 = true := by
  decide +kernel

private theorem b120_step :
    matrixRepresentation generatorB * decode b119 = decode b120 :=
  sound atlasBRows b119 b120 b120_valid b120_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b121_valid : valid b120 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b121_check : check atlasBRows b120 b121 = true := by
  decide +kernel

private theorem b121_step :
    matrixRepresentation generatorB * decode b120 = decode b121 :=
  sound atlasBRows b120 b121 b121_valid b121_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b122_valid : valid b121 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b122_check : check atlasARows b121 b122 = true := by
  decide +kernel

private theorem b122_step :
    matrixRepresentation generatorA * decode b121 = decode b122 :=
  sound atlasARows b121 b122 b122_valid b122_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b123_valid : valid b122 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b123_check : check atlasBRows b122 b123 = true := by
  decide +kernel

private theorem b123_step :
    matrixRepresentation generatorB * decode b122 = decode b123 :=
  sound atlasBRows b122 b123 b123_valid b123_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b124_valid : valid b123 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b124_check : check atlasARows b123 b124 = true := by
  decide +kernel

private theorem b124_step :
    matrixRepresentation generatorA * decode b123 = decode b124 :=
  sound atlasARows b123 b124 b124_valid b124_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b125_valid : valid b124 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b125_check : check atlasBRows b124 b125 = true := by
  decide +kernel

private theorem b125_step :
    matrixRepresentation generatorB * decode b124 = decode b125 :=
  sound atlasBRows b124 b125 b125_valid b125_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b126_valid : valid b125 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b126_check : check atlasARows b125 b126 = true := by
  decide +kernel

private theorem b126_step :
    matrixRepresentation generatorA * decode b125 = decode b126 :=
  sound atlasARows b125 b126 b126_valid b126_check

private theorem b_word17 :
    matrixRepresentation wordB * decode b119 = decode b126 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b120_step, b121_step, b122_step, b123_step, b124_step, b125_step, b126_step]

public theorem b_power18 :
    matrixRepresentation (wordB ^ 18) * decode b0 = decode b126 := by
  exact power_step wordB 17 _ _ _ b_power17 b_word17

end Lyons.OrderCertificate.PlaneTransport
