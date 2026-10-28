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
private theorem block_84_0 : checkIdentity (relatorFin 84) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_1 : checkIdentity (relatorFin 84) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_2 : checkIdentity (relatorFin 84) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_3 : checkIdentity (relatorFin 84) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_4 : checkIdentity (relatorFin 84) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_5 : checkIdentity (relatorFin 84) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_6 : checkIdentity (relatorFin 84) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_7 : checkIdentity (relatorFin 84) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_8 : checkIdentity (relatorFin 84) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_9 : checkIdentity (relatorFin 84) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_10 : checkIdentity (relatorFin 84) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_11 : checkIdentity (relatorFin 84) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_12 : checkIdentity (relatorFin 84) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_13 : checkIdentity (relatorFin 84) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_14 : checkIdentity (relatorFin 84) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_15 : checkIdentity (relatorFin 84) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_84_16 : checkIdentity (relatorFin 84) 2048 128 = true := by
  decide +kernel

theorem relator_84 : eval generator (relatorFin 84) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_84_0
    | 1 => block_84_1
    | 2 => block_84_2
    | 3 => block_84_3
    | 4 => block_84_4
    | 5 => block_84_5
    | 6 => block_84_6
    | 7 => block_84_7
    | 8 => block_84_8
    | 9 => block_84_9
    | 10 => block_84_10
    | 11 => block_84_11
    | 12 => block_84_12
    | 13 => block_84_13
    | 14 => block_84_14
    | 15 => block_84_15
    | 16 => block_84_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
