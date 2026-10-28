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
private theorem block_96_0 : checkIdentity (relatorFin 96) 0 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_1 : checkIdentity (relatorFin 96) 128 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_2 : checkIdentity (relatorFin 96) 256 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_3 : checkIdentity (relatorFin 96) 384 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_4 : checkIdentity (relatorFin 96) 512 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_5 : checkIdentity (relatorFin 96) 640 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_6 : checkIdentity (relatorFin 96) 768 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_7 : checkIdentity (relatorFin 96) 896 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_8 : checkIdentity (relatorFin 96) 1024 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_9 : checkIdentity (relatorFin 96) 1152 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_10 : checkIdentity (relatorFin 96) 1280 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_11 : checkIdentity (relatorFin 96) 1408 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_12 : checkIdentity (relatorFin 96) 1536 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_13 : checkIdentity (relatorFin 96) 1664 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_14 : checkIdentity (relatorFin 96) 1792 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_15 : checkIdentity (relatorFin 96) 1920 128 = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem block_96_16 : checkIdentity (relatorFin 96) 2048 128 = true := by
  decide +kernel

theorem relator_96 : eval generator (relatorFin 96) = 1 :=
  relator_of_blocks _ fun q => match q with
    | 0 => block_96_0
    | 1 => block_96_1
    | 2 => block_96_2
    | 3 => block_96_3
    | 4 => block_96_4
    | 5 => block_96_5
    | 6 => block_96_6
    | 7 => block_96_7
    | 8 => block_96_8
    | 9 => block_96_9
    | 10 => block_96_10
    | 11 => block_96_11
    | 12 => block_96_12
    | 13 => block_96_13
    | 14 => block_96_14
    | 15 => block_96_15
    | 16 => block_96_16
    | ⟨n + 17, h⟩ => by omega

end Held.Realization.IndexCertificate
