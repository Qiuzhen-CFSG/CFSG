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
private theorem block_83_0 : checkIdentity (relatorFin 83) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_1 : checkIdentity (relatorFin 83) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_2 : checkIdentity (relatorFin 83) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_3 : checkIdentity (relatorFin 83) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_4 : checkIdentity (relatorFin 83) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_5 : checkIdentity (relatorFin 83) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_6 : checkIdentity (relatorFin 83) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_7 : checkIdentity (relatorFin 83) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_8 : checkIdentity (relatorFin 83) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_9 : checkIdentity (relatorFin 83) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_10 : checkIdentity (relatorFin 83) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_11 : checkIdentity (relatorFin 83) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_12 : checkIdentity (relatorFin 83) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_13 : checkIdentity (relatorFin 83) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_14 : checkIdentity (relatorFin 83) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_15 : checkIdentity (relatorFin 83) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_83_16 : checkIdentity (relatorFin 83) 2048 128 = true := by
  decide +kernel

theorem relator_83 : eval generator (relatorFin 83) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_83_0
    | 1 => block_83_1
    | 2 => block_83_2
    | 3 => block_83_3
    | 4 => block_83_4
    | 5 => block_83_5
    | 6 => block_83_6
    | 7 => block_83_7
    | 8 => block_83_8
    | 9 => block_83_9
    | 10 => block_83_10
    | 11 => block_83_11
    | 12 => block_83_12
    | 13 => block_83_13
    | 14 => block_83_14
    | 15 => block_83_15
    | 16 => block_83_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
