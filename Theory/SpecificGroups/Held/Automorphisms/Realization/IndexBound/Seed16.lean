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
private theorem block_97_0 : checkIdentity (relatorFin 97) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_1 : checkIdentity (relatorFin 97) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_2 : checkIdentity (relatorFin 97) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_3 : checkIdentity (relatorFin 97) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_4 : checkIdentity (relatorFin 97) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_5 : checkIdentity (relatorFin 97) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_6 : checkIdentity (relatorFin 97) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_7 : checkIdentity (relatorFin 97) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_8 : checkIdentity (relatorFin 97) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_9 : checkIdentity (relatorFin 97) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_10 : checkIdentity (relatorFin 97) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_11 : checkIdentity (relatorFin 97) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_12 : checkIdentity (relatorFin 97) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_13 : checkIdentity (relatorFin 97) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_14 : checkIdentity (relatorFin 97) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_15 : checkIdentity (relatorFin 97) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_97_16 : checkIdentity (relatorFin 97) 2048 128 = true := by
  decide +kernel

theorem relator_97 : eval generator (relatorFin 97) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_97_0
    | 1 => block_97_1
    | 2 => block_97_2
    | 3 => block_97_3
    | 4 => block_97_4
    | 5 => block_97_5
    | 6 => block_97_6
    | 7 => block_97_7
    | 8 => block_97_8
    | 9 => block_97_9
    | 10 => block_97_10
    | 11 => block_97_11
    | 12 => block_97_12
    | 13 => block_97_13
    | 14 => block_97_14
    | 15 => block_97_15
    | 16 => block_97_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
