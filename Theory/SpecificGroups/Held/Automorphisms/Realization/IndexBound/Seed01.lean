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
private theorem block_82_0 : checkIdentity (relatorFin 82) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_1 : checkIdentity (relatorFin 82) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_2 : checkIdentity (relatorFin 82) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_3 : checkIdentity (relatorFin 82) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_4 : checkIdentity (relatorFin 82) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_5 : checkIdentity (relatorFin 82) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_6 : checkIdentity (relatorFin 82) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_7 : checkIdentity (relatorFin 82) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_8 : checkIdentity (relatorFin 82) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_9 : checkIdentity (relatorFin 82) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_10 : checkIdentity (relatorFin 82) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_11 : checkIdentity (relatorFin 82) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_12 : checkIdentity (relatorFin 82) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_13 : checkIdentity (relatorFin 82) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_14 : checkIdentity (relatorFin 82) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_15 : checkIdentity (relatorFin 82) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_82_16 : checkIdentity (relatorFin 82) 2048 128 = true := by
  decide +kernel

theorem relator_82 : eval generator (relatorFin 82) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_82_0
    | 1 => block_82_1
    | 2 => block_82_2
    | 3 => block_82_3
    | 4 => block_82_4
    | 5 => block_82_5
    | 6 => block_82_6
    | 7 => block_82_7
    | 8 => block_82_8
    | 9 => block_82_9
    | 10 => block_82_10
    | 11 => block_82_11
    | 12 => block_82_12
    | 13 => block_82_13
    | 14 => block_82_14
    | 15 => block_82_15
    | 16 => block_82_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
