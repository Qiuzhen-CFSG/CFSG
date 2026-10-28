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
private theorem block_85_0 : checkIdentity (relatorFin 85) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_1 : checkIdentity (relatorFin 85) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_2 : checkIdentity (relatorFin 85) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_3 : checkIdentity (relatorFin 85) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_4 : checkIdentity (relatorFin 85) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_5 : checkIdentity (relatorFin 85) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_6 : checkIdentity (relatorFin 85) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_7 : checkIdentity (relatorFin 85) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_8 : checkIdentity (relatorFin 85) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_9 : checkIdentity (relatorFin 85) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_10 : checkIdentity (relatorFin 85) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_11 : checkIdentity (relatorFin 85) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_12 : checkIdentity (relatorFin 85) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_13 : checkIdentity (relatorFin 85) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_14 : checkIdentity (relatorFin 85) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_15 : checkIdentity (relatorFin 85) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_85_16 : checkIdentity (relatorFin 85) 2048 128 = true := by
  decide +kernel

theorem relator_85 : eval generator (relatorFin 85) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_85_0
    | 1 => block_85_1
    | 2 => block_85_2
    | 3 => block_85_3
    | 4 => block_85_4
    | 5 => block_85_5
    | 6 => block_85_6
    | 7 => block_85_7
    | 8 => block_85_8
    | 9 => block_85_9
    | 10 => block_85_10
    | 11 => block_85_11
    | 12 => block_85_12
    | 13 => block_85_13
    | 14 => block_85_14
    | 15 => block_85_15
    | 16 => block_85_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
