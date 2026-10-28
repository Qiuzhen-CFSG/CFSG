module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity.DoubleCosetCover.PairMaps

/-!
# Packed point maps of the literal core generators

The constants are candidate point maps obtained by evaluating the original
ATLAS max1 and max2 programs, with inverse point maps for the left action.
Every equality is checked on all 1600 points in the sibling checking module.
Source authors: R. A. Wilson, R. A. Parker and J. N. Bray; see
`MinimumIndex/source/README.md`. Discovery code is in `DoubleCosetCover/source/`.
-/

namespace Tits.MinimumIndexThirteen.CandidateRigidity.CoreCover
open Theory.GroupTheory Atlas1600OrderCertificate

@[expose] public def compactPair (i : Fin 2) : Equiv.Perm (Fin 1600) × Equiv.Perm (Fin 1600) :=
  (![pairX0, pairX1] i, pairY)

private theorem program_snd_eq {G : Type*} [Group G] (a b : G) (i : Fin 2) :
    (program a b (i.castLE (by decide))).2 = (program a b 0).2 := by
  fin_cases i <;> rfl

public theorem compactPair_eq (i : Fin 2) :
    compactPair i = program L0G0 L0G1 (i.castLE (by decide)) := by
  apply Prod.ext
  · change ![pairX0, pairX1] i = (program L0G0 L0G1 (i.castLE (by decide))).1
    fin_cases i
    · exact pairX0_eq
    · exact pairX1_eq
  · change pairY = (program L0G0 L0G1 (i.castLE (by decide))).2
    rw [program_snd_eq]
    exact pairY_eq

@[expose] public def compactSignedCore (i : Fin 2) : Fin 6 → Equiv.Perm (Fin 1600) :=
  let c := seeds (compactPair i)
  ![c 0, c 1, c 2, (c 0)⁻¹, (c 1)⁻¹, (c 2)⁻¹]

public theorem compactSignedCore_eq (i : Fin 2) (k : Fin 6) :
    compactSignedCore i k = (signedCore i k).val := by
  rw [compactSignedCore, compactPair_eq]
  exact packedSignedCore_eq i k

end Tits.MinimumIndexThirteen.CandidateRigidity.CoreCover
