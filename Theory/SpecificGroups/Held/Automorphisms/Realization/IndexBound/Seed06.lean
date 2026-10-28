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
private theorem block_87_0 : checkIdentity (relatorFin 87) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_1 : checkIdentity (relatorFin 87) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_2 : checkIdentity (relatorFin 87) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_3 : checkIdentity (relatorFin 87) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_4 : checkIdentity (relatorFin 87) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_5 : checkIdentity (relatorFin 87) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_6 : checkIdentity (relatorFin 87) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_7 : checkIdentity (relatorFin 87) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_8 : checkIdentity (relatorFin 87) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_9 : checkIdentity (relatorFin 87) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_10 : checkIdentity (relatorFin 87) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_11 : checkIdentity (relatorFin 87) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_12 : checkIdentity (relatorFin 87) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_13 : checkIdentity (relatorFin 87) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_14 : checkIdentity (relatorFin 87) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_15 : checkIdentity (relatorFin 87) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_87_16 : checkIdentity (relatorFin 87) 2048 128 = true := by
  decide +kernel

theorem relator_87 : eval generator (relatorFin 87) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_87_0
    | 1 => block_87_1
    | 2 => block_87_2
    | 3 => block_87_3
    | 4 => block_87_4
    | 5 => block_87_5
    | 6 => block_87_6
    | 7 => block_87_7
    | 8 => block_87_8
    | 9 => block_87_9
    | 10 => block_87_10
    | 11 => block_87_11
    | 12 => block_87_12
    | 13 => block_87_13
    | 14 => block_87_14
    | 15 => block_87_15
    | 16 => block_87_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
