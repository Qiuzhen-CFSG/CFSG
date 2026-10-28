module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity.Words

/-!
# Kernel checks of the rigidity recovery words

These finite pointwise identities use packed permutations and the literal
ATLAS word programs. Generation transports them into the actual group and
applies the certified three-point base. Discovery and provenance are in
`CandidateRigidity/source/`; no result of the discovery program is assumed.
-/

namespace Tits.MinimumIndexThirteen.CandidateRigidity.WordChecks
open Theory.GroupTheory Atlas1600OrderCertificate
set_option Elab.async false

@[expose] public def recoveryWord : Fin 2 → Fin 4 → Fin 2 → List (Fin 8) :=
  ![![![[7],
    [3, 4, 6, 3, 0, 2, 4, 4, 2, 4]],
    ![[0, 6, 6, 0, 0, 0, 6, 7, 2, 4, 3, 4, 6, 4, 5, 6, 4, 4, 7, 6, 4, 4, 4, 6, 7, 6, 4, 2, 0, 0],
    [3]],
    ![[6, 6, 4, 6, 6, 0, 6, 4, 6, 4, 4, 2, 0, 6, 6, 7, 7, 0, 0, 3],
    [0, 6, 4, 6, 4, 4, 2, 4, 4, 6, 7, 4, 6, 6, 7, 7, 5, 7, 6, 0, 6, 4, 6, 6, 6, 4, 4, 3, 3, 4, 2, 4]],
    ![[2, 2, 0, 2, 2, 0, 6, 4, 6, 4, 4, 6, 4, 2, 0, 0, 6, 4, 3, 6, 0, 7, 7],
    [7, 7, 4, 2, 7, 0, 2, 4, 4, 6, 0, 2, 0, 0, 2, 0, 2, 4, 6, 6, 4, 6, 6]]],
    ![![[7],
    [2, 7, 2, 0, 7, 0, 7, 4, 4, 7, 0, 2, 4, 7, 4, 4, 7, 0, 6, 4, 6, 4, 6, 0]],
    ![[6, 6, 4, 7, 0, 6, 7, 2, 4, 3, 4, 4, 3, 2, 7, 2, 0, 2, 0, 2, 4, 7, 0, 7, 4, 3, 6, 7],
    [3]],
    ![[6, 6, 7, 4, 4, 2, 4, 3, 6, 7, 6],
    [4, 2, 4, 4, 3, 3, 4, 2, 7, 0, 7, 6, 3, 3, 3]],
    ![[6, 6, 4, 3, 6, 4, 3, 2, 3, 4, 2, 0, 0, 3, 6, 4, 6, 3, 2],
    [6, 6, 6, 7, 2, 7, 6, 7, 6, 7, 0, 0, 3, 4, 2, 2, 4, 3, 6, 3]]]]


set_option maxRecDepth 20000 in
public theorem recovery_table : ∀ (i : Fin 2) (j : Fin 4) (k : Fin 2) (p : Fin 3),
    evalWord (inputs (program L0G0 L0G1 (i.castLE (by decide)))
      (packedRepresentative i ⟨j.val + 2, by omega⟩))
      (recoveryWord i j k) (p.castLE (by decide)) =
    L0Gen (k.castLE (by decide)) (p.castLE (by decide)) := by
  apply allFin₃
  decide +kernel

@[expose] public def perfectWord : Fin 2 → List (Fin 8) :=
  ![[2, 2, 0, 6, 4, 2, 2, 0, 6, 4, 4, 4, 4, 4, 4],
    [0, 6, 6, 4, 4, 2, 4, 4, 4, 4]]


set_option maxRecDepth 20000 in
public theorem perfect_table : ∀ (k : Fin 2) (p : Fin 3),
    evalWord (inputs (program L0G0 L0G1 2) 1) (perfectWord k)
      (p.castLE (by decide)) =
    ![(program L0G0 L0G1 2).1, (program L0G0 L0G1 2).2] k
      (p.castLE (by decide)) := by
  apply allFin₂
  decide +kernel

end Tits.MinimumIndexThirteen.CandidateRigidity.WordChecks
