module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport22

/-!
# Lyons plane transport through wordB, step 24

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 24 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b162_valid : valid b161 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b162_check : check atlasBRows b161 b162 = true := by
  decide +kernel

private theorem b162_step :
    matrixRepresentation generatorB * decode b161 = decode b162 :=
  sound atlasBRows b161 b162 b162_valid b162_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b163_valid : valid b162 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b163_check : check atlasBRows b162 b163 = true := by
  decide +kernel

private theorem b163_step :
    matrixRepresentation generatorB * decode b162 = decode b163 :=
  sound atlasBRows b162 b163 b163_valid b163_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b164_valid : valid b163 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b164_check : check atlasARows b163 b164 = true := by
  decide +kernel

private theorem b164_step :
    matrixRepresentation generatorA * decode b163 = decode b164 :=
  sound atlasARows b163 b164 b164_valid b164_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b165_valid : valid b164 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b165_check : check atlasBRows b164 b165 = true := by
  decide +kernel

private theorem b165_step :
    matrixRepresentation generatorB * decode b164 = decode b165 :=
  sound atlasBRows b164 b165 b165_valid b165_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b166_valid : valid b165 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b166_check : check atlasARows b165 b166 = true := by
  decide +kernel

private theorem b166_step :
    matrixRepresentation generatorA * decode b165 = decode b166 :=
  sound atlasARows b165 b166 b166_valid b166_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b167_valid : valid b166 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b167_check : check atlasBRows b166 b167 = true := by
  decide +kernel

private theorem b167_step :
    matrixRepresentation generatorB * decode b166 = decode b167 :=
  sound atlasBRows b166 b167 b167_valid b167_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b168_valid : valid b167 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b168_check : check atlasARows b167 b168 = true := by
  decide +kernel

private theorem b168_step :
    matrixRepresentation generatorA * decode b167 = decode b168 :=
  sound atlasARows b167 b168 b168_valid b168_check

private theorem b_word23 :
    matrixRepresentation wordB * decode b161 = decode b168 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b162_step, b163_step, b164_step, b165_step, b166_step, b167_step, b168_step]

public theorem b_power24 :
    matrixRepresentation (wordB ^ 24) * decode b0 = decode b168 := by
  exact power_step wordB 23 _ _ _ b_power23 b_word23

end Lyons.OrderCertificate.PlaneTransport
