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
private theorem block_81_0 : checkIdentity (relatorFin 81) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_1 : checkIdentity (relatorFin 81) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_2 : checkIdentity (relatorFin 81) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_3 : checkIdentity (relatorFin 81) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_4 : checkIdentity (relatorFin 81) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_5 : checkIdentity (relatorFin 81) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_6 : checkIdentity (relatorFin 81) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_7 : checkIdentity (relatorFin 81) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_8 : checkIdentity (relatorFin 81) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_9 : checkIdentity (relatorFin 81) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_10 : checkIdentity (relatorFin 81) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_11 : checkIdentity (relatorFin 81) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_12 : checkIdentity (relatorFin 81) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_13 : checkIdentity (relatorFin 81) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_14 : checkIdentity (relatorFin 81) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_15 : checkIdentity (relatorFin 81) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_81_16 : checkIdentity (relatorFin 81) 2048 128 = true := by
  decide +kernel

theorem relator_81 : eval generator (relatorFin 81) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_81_0
    | 1 => block_81_1
    | 2 => block_81_2
    | 3 => block_81_3
    | 4 => block_81_4
    | 5 => block_81_5
    | 6 => block_81_6
    | 7 => block_81_7
    | 8 => block_81_8
    | 9 => block_81_9
    | 10 => block_81_10
    | 11 => block_81_11
    | 12 => block_81_12
    | 13 => block_81_13
    | 14 => block_81_14
    | 15 => block_81_15
    | 16 => block_81_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
