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
private theorem block_91_0 : checkIdentity (relatorFin 91) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_1 : checkIdentity (relatorFin 91) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_2 : checkIdentity (relatorFin 91) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_3 : checkIdentity (relatorFin 91) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_4 : checkIdentity (relatorFin 91) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_5 : checkIdentity (relatorFin 91) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_6 : checkIdentity (relatorFin 91) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_7 : checkIdentity (relatorFin 91) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_8 : checkIdentity (relatorFin 91) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_9 : checkIdentity (relatorFin 91) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_10 : checkIdentity (relatorFin 91) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_11 : checkIdentity (relatorFin 91) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_12 : checkIdentity (relatorFin 91) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_13 : checkIdentity (relatorFin 91) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_14 : checkIdentity (relatorFin 91) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_15 : checkIdentity (relatorFin 91) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_91_16 : checkIdentity (relatorFin 91) 2048 128 = true := by
  decide +kernel

theorem relator_91 : eval generator (relatorFin 91) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_91_0
    | 1 => block_91_1
    | 2 => block_91_2
    | 3 => block_91_3
    | 4 => block_91_4
    | 5 => block_91_5
    | 6 => block_91_6
    | 7 => block_91_7
    | 8 => block_91_8
    | 9 => block_91_9
    | 10 => block_91_10
    | 11 => block_91_11
    | 12 => block_91_12
    | 13 => block_91_13
    | 14 => block_91_14
    | 15 => block_91_15
    | 16 => block_91_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
