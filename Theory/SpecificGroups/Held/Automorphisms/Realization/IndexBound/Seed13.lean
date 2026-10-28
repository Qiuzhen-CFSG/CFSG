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
private theorem block_94_0 : checkIdentity (relatorFin 94) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_1 : checkIdentity (relatorFin 94) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_2 : checkIdentity (relatorFin 94) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_3 : checkIdentity (relatorFin 94) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_4 : checkIdentity (relatorFin 94) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_5 : checkIdentity (relatorFin 94) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_6 : checkIdentity (relatorFin 94) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_7 : checkIdentity (relatorFin 94) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_8 : checkIdentity (relatorFin 94) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_9 : checkIdentity (relatorFin 94) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_10 : checkIdentity (relatorFin 94) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_11 : checkIdentity (relatorFin 94) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_12 : checkIdentity (relatorFin 94) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_13 : checkIdentity (relatorFin 94) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_14 : checkIdentity (relatorFin 94) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_15 : checkIdentity (relatorFin 94) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_94_16 : checkIdentity (relatorFin 94) 2048 128 = true := by
  decide +kernel

theorem relator_94 : eval generator (relatorFin 94) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_94_0
    | 1 => block_94_1
    | 2 => block_94_2
    | 3 => block_94_3
    | 4 => block_94_4
    | 5 => block_94_5
    | 6 => block_94_6
    | 7 => block_94_7
    | 8 => block_94_8
    | 9 => block_94_9
    | 10 => block_94_10
    | 11 => block_94_11
    | 12 => block_94_12
    | 13 => block_94_13
    | 14 => block_94_14
    | 15 => block_94_15
    | 16 => block_94_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
