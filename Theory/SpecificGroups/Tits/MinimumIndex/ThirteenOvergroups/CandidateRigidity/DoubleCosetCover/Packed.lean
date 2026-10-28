module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity.DoubleCosetCover.CompactPair

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

set_option Elab.async false

set_option maxRecDepth 20000 in
private theorem coreMap0_checked : ∀ (k : Fin 6) (p : Fin 1600),
    coreMap 0 k p = compactSignedCore 0 k p := by
  apply allFin₂
  decide +kernel

set_option maxRecDepth 20000 in
private theorem coreMap1_checked : ∀ (k : Fin 6) (p : Fin 1600),
    coreMap 1 k p = compactSignedCore 1 k p := by
  apply allFin₂
  decide +kernel

public theorem coreMap_eq (i : Fin 2) (k : Fin 6) (p : Fin 1600) :
    coreMap i k p = (signedCore i k).val p := by
  rw [← compactSignedCore_eq]
  fin_cases i
  · exact coreMap0_checked k p
  · exact coreMap1_checked k p

end Tits.MinimumIndexThirteen.CandidateRigidity.CoreCover
