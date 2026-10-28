module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport20

/-!
# Lyons plane transport through wordB, step 22

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 22 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b148_valid : valid b147 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b148_check : check atlasBRows b147 b148 = true := by
  decide +kernel

private theorem b148_step :
    matrixRepresentation generatorB * decode b147 = decode b148 :=
  sound atlasBRows b147 b148 b148_valid b148_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b149_valid : valid b148 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b149_check : check atlasBRows b148 b149 = true := by
  decide +kernel

private theorem b149_step :
    matrixRepresentation generatorB * decode b148 = decode b149 :=
  sound atlasBRows b148 b149 b149_valid b149_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b150_valid : valid b149 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b150_check : check atlasARows b149 b150 = true := by
  decide +kernel

private theorem b150_step :
    matrixRepresentation generatorA * decode b149 = decode b150 :=
  sound atlasARows b149 b150 b150_valid b150_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b151_valid : valid b150 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b151_check : check atlasBRows b150 b151 = true := by
  decide +kernel

private theorem b151_step :
    matrixRepresentation generatorB * decode b150 = decode b151 :=
  sound atlasBRows b150 b151 b151_valid b151_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b152_valid : valid b151 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b152_check : check atlasARows b151 b152 = true := by
  decide +kernel

private theorem b152_step :
    matrixRepresentation generatorA * decode b151 = decode b152 :=
  sound atlasARows b151 b152 b152_valid b152_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b153_valid : valid b152 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b153_check : check atlasBRows b152 b153 = true := by
  decide +kernel

private theorem b153_step :
    matrixRepresentation generatorB * decode b152 = decode b153 :=
  sound atlasBRows b152 b153 b153_valid b153_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b154_valid : valid b153 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b154_check : check atlasARows b153 b154 = true := by
  decide +kernel

private theorem b154_step :
    matrixRepresentation generatorA * decode b153 = decode b154 :=
  sound atlasARows b153 b154 b154_valid b154_check

private theorem b_word21 :
    matrixRepresentation wordB * decode b147 = decode b154 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b148_step, b149_step, b150_step, b151_step, b152_step, b153_step, b154_step]

public theorem b_power22 :
    matrixRepresentation (wordB ^ 22) * decode b0 = decode b154 := by
  exact power_step wordB 21 _ _ _ b_power21 b_word21

end Lyons.OrderCertificate.PlaneTransport
