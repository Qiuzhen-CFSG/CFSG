module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Evaluation

/-!
Relator checks for the marked Held coset certificate. The seven source
relations, the definitions of the marked involutions, and cyclic rotations
are algebraic. The seventeen additional identities are checked against the
literal degree-2058 ATLAS permutations in bounded kernel computations.
Reproduce with `IndexBound/Source/generate_relators.py`.
-/

public section
namespace Held.Realization.IndexCertificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_0 : checkIdentity (relatorFin 90) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_1 : checkIdentity (relatorFin 90) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_2 : checkIdentity (relatorFin 90) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_3 : checkIdentity (relatorFin 90) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_4 : checkIdentity (relatorFin 90) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_5 : checkIdentity (relatorFin 90) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_6 : checkIdentity (relatorFin 90) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_7 : checkIdentity (relatorFin 90) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_8 : checkIdentity (relatorFin 90) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_9 : checkIdentity (relatorFin 90) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_10 : checkIdentity (relatorFin 90) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_11 : checkIdentity (relatorFin 90) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_12 : checkIdentity (relatorFin 90) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_13 : checkIdentity (relatorFin 90) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_14 : checkIdentity (relatorFin 90) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_15 : checkIdentity (relatorFin 90) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_90_16 : checkIdentity (relatorFin 90) 2048 128 = true := by
  decide +kernel

theorem relator_90 : eval generator (relatorFin 90) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_90_0
    | 1 => block_90_1
    | 2 => block_90_2
    | 3 => block_90_3
    | 4 => block_90_4
    | 5 => block_90_5
    | 6 => block_90_6
    | 7 => block_90_7
    | 8 => block_90_8
    | 9 => block_90_9
    | 10 => block_90_10
    | 11 => block_90_11
    | 12 => block_90_12
    | 13 => block_90_13
    | 14 => block_90_14
    | 15 => block_90_15
    | 16 => block_90_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
