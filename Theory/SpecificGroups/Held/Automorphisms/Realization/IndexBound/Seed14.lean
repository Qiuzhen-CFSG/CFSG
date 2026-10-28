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
private theorem block_95_0 : checkIdentity (relatorFin 95) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_1 : checkIdentity (relatorFin 95) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_2 : checkIdentity (relatorFin 95) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_3 : checkIdentity (relatorFin 95) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_4 : checkIdentity (relatorFin 95) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_5 : checkIdentity (relatorFin 95) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_6 : checkIdentity (relatorFin 95) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_7 : checkIdentity (relatorFin 95) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_8 : checkIdentity (relatorFin 95) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_9 : checkIdentity (relatorFin 95) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_10 : checkIdentity (relatorFin 95) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_11 : checkIdentity (relatorFin 95) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_12 : checkIdentity (relatorFin 95) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_13 : checkIdentity (relatorFin 95) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_14 : checkIdentity (relatorFin 95) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_15 : checkIdentity (relatorFin 95) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_95_16 : checkIdentity (relatorFin 95) 2048 128 = true := by
  decide +kernel

theorem relator_95 : eval generator (relatorFin 95) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_95_0
    | 1 => block_95_1
    | 2 => block_95_2
    | 3 => block_95_3
    | 4 => block_95_4
    | 5 => block_95_5
    | 6 => block_95_6
    | 7 => block_95_7
    | 8 => block_95_8
    | 9 => block_95_9
    | 10 => block_95_10
    | 11 => block_95_11
    | 12 => block_95_12
    | 13 => block_95_13
    | 14 => block_95_14
    | 15 => block_95_15
    | 16 => block_95_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
