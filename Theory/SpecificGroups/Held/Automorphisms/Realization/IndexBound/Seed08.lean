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
private theorem block_89_0 : checkIdentity (relatorFin 89) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_1 : checkIdentity (relatorFin 89) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_2 : checkIdentity (relatorFin 89) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_3 : checkIdentity (relatorFin 89) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_4 : checkIdentity (relatorFin 89) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_5 : checkIdentity (relatorFin 89) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_6 : checkIdentity (relatorFin 89) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_7 : checkIdentity (relatorFin 89) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_8 : checkIdentity (relatorFin 89) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_9 : checkIdentity (relatorFin 89) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_10 : checkIdentity (relatorFin 89) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_11 : checkIdentity (relatorFin 89) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_12 : checkIdentity (relatorFin 89) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_13 : checkIdentity (relatorFin 89) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_14 : checkIdentity (relatorFin 89) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_15 : checkIdentity (relatorFin 89) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_89_16 : checkIdentity (relatorFin 89) 2048 128 = true := by
  decide +kernel

theorem relator_89 : eval generator (relatorFin 89) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_89_0
    | 1 => block_89_1
    | 2 => block_89_2
    | 3 => block_89_3
    | 4 => block_89_4
    | 5 => block_89_5
    | 6 => block_89_6
    | 7 => block_89_7
    | 8 => block_89_8
    | 9 => block_89_9
    | 10 => block_89_10
    | 11 => block_89_11
    | 12 => block_89_12
    | 13 => block_89_13
    | 14 => block_89_14
    | 15 => block_89_15
    | 16 => block_89_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
