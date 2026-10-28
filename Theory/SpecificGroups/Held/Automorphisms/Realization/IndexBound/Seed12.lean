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
private theorem block_93_0 : checkIdentity (relatorFin 93) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_1 : checkIdentity (relatorFin 93) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_2 : checkIdentity (relatorFin 93) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_3 : checkIdentity (relatorFin 93) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_4 : checkIdentity (relatorFin 93) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_5 : checkIdentity (relatorFin 93) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_6 : checkIdentity (relatorFin 93) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_7 : checkIdentity (relatorFin 93) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_8 : checkIdentity (relatorFin 93) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_9 : checkIdentity (relatorFin 93) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_10 : checkIdentity (relatorFin 93) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_11 : checkIdentity (relatorFin 93) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_12 : checkIdentity (relatorFin 93) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_13 : checkIdentity (relatorFin 93) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_14 : checkIdentity (relatorFin 93) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_15 : checkIdentity (relatorFin 93) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_93_16 : checkIdentity (relatorFin 93) 2048 128 = true := by
  decide +kernel

theorem relator_93 : eval generator (relatorFin 93) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_93_0
    | 1 => block_93_1
    | 2 => block_93_2
    | 3 => block_93_3
    | 4 => block_93_4
    | 5 => block_93_5
    | 6 => block_93_6
    | 7 => block_93_7
    | 8 => block_93_8
    | 9 => block_93_9
    | 10 => block_93_10
    | 11 => block_93_11
    | 12 => block_93_12
    | 13 => block_93_13
    | 14 => block_93_14
    | 15 => block_93_15
    | 16 => block_93_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
