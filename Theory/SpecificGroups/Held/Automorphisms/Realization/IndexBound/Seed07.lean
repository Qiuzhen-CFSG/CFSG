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
private theorem block_88_0 : checkIdentity (relatorFin 88) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_1 : checkIdentity (relatorFin 88) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_2 : checkIdentity (relatorFin 88) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_3 : checkIdentity (relatorFin 88) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_4 : checkIdentity (relatorFin 88) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_5 : checkIdentity (relatorFin 88) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_6 : checkIdentity (relatorFin 88) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_7 : checkIdentity (relatorFin 88) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_8 : checkIdentity (relatorFin 88) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_9 : checkIdentity (relatorFin 88) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_10 : checkIdentity (relatorFin 88) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_11 : checkIdentity (relatorFin 88) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_12 : checkIdentity (relatorFin 88) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_13 : checkIdentity (relatorFin 88) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_14 : checkIdentity (relatorFin 88) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_15 : checkIdentity (relatorFin 88) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_88_16 : checkIdentity (relatorFin 88) 2048 128 = true := by
  decide +kernel

theorem relator_88 : eval generator (relatorFin 88) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_88_0
    | 1 => block_88_1
    | 2 => block_88_2
    | 3 => block_88_3
    | 4 => block_88_4
    | 5 => block_88_5
    | 6 => block_88_6
    | 7 => block_88_7
    | 8 => block_88_8
    | 9 => block_88_9
    | 10 => block_88_10
    | 11 => block_88_11
    | 12 => block_88_12
    | 13 => block_88_13
    | 14 => block_88_14
    | 15 => block_88_15
    | 16 => block_88_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
