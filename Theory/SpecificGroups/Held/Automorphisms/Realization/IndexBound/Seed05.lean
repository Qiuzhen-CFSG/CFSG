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
private theorem block_86_0 : checkIdentity (relatorFin 86) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_1 : checkIdentity (relatorFin 86) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_2 : checkIdentity (relatorFin 86) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_3 : checkIdentity (relatorFin 86) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_4 : checkIdentity (relatorFin 86) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_5 : checkIdentity (relatorFin 86) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_6 : checkIdentity (relatorFin 86) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_7 : checkIdentity (relatorFin 86) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_8 : checkIdentity (relatorFin 86) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_9 : checkIdentity (relatorFin 86) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_10 : checkIdentity (relatorFin 86) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_11 : checkIdentity (relatorFin 86) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_12 : checkIdentity (relatorFin 86) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_13 : checkIdentity (relatorFin 86) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_14 : checkIdentity (relatorFin 86) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_15 : checkIdentity (relatorFin 86) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_86_16 : checkIdentity (relatorFin 86) 2048 128 = true := by
  decide +kernel

theorem relator_86 : eval generator (relatorFin 86) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_86_0
    | 1 => block_86_1
    | 2 => block_86_2
    | 3 => block_86_3
    | 4 => block_86_4
    | 5 => block_86_5
    | 6 => block_86_6
    | 7 => block_86_7
    | 8 => block_86_8
    | 9 => block_86_9
    | 10 => block_86_10
    | 11 => block_86_11
    | 12 => block_86_12
    | 13 => block_86_13
    | 14 => block_86_14
    | 15 => block_86_15
    | 16 => block_86_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
