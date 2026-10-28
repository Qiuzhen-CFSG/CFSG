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
private theorem block_92_0 : checkIdentity (relatorFin 92) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_1 : checkIdentity (relatorFin 92) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_2 : checkIdentity (relatorFin 92) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_3 : checkIdentity (relatorFin 92) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_4 : checkIdentity (relatorFin 92) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_5 : checkIdentity (relatorFin 92) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_6 : checkIdentity (relatorFin 92) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_7 : checkIdentity (relatorFin 92) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_8 : checkIdentity (relatorFin 92) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_9 : checkIdentity (relatorFin 92) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_10 : checkIdentity (relatorFin 92) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_11 : checkIdentity (relatorFin 92) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_12 : checkIdentity (relatorFin 92) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_13 : checkIdentity (relatorFin 92) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_14 : checkIdentity (relatorFin 92) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_15 : checkIdentity (relatorFin 92) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_92_16 : checkIdentity (relatorFin 92) 2048 128 = true := by
  decide +kernel

theorem relator_92 : eval generator (relatorFin 92) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_92_0
    | 1 => block_92_1
    | 2 => block_92_2
    | 3 => block_92_3
    | 4 => block_92_4
    | 5 => block_92_5
    | 6 => block_92_6
    | 7 => block_92_7
    | 8 => block_92_8
    | 9 => block_92_9
    | 10 => block_92_10
    | 11 => block_92_11
    | 12 => block_92_12
    | 13 => block_92_13
    | 14 => block_92_14
    | 15 => block_92_15
    | 16 => block_92_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
