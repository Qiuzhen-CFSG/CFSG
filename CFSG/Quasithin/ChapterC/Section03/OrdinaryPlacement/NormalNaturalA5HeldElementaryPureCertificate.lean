module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryPureChecker

/-! Checked pure-subgroup placement certificates for every native clique. -/
@[expose] public section
namespace Held.OrdinaryElementary.NativeCoverage

def purePossible (k : Fin 34) : Finset (Fin 192) :=
  Finset.univ.filter (fun v => (candidateMask k).testBit v.val=true ∧ marked v≠true)

private def pureCertificate : Fin 34 → PureTree
  | 0 => .impossible
  | 1 => .impossible
  | 2 => .impossible
  | 3 => .impossible
  | 4 => .impossible
  | 5 => .impossible
  | 6 => .impossible
  | 7 => .impossible
  | 8 => .impossible
  | 9 => .impossible
  | 10 => .impossible
  | 11 => .impossible
  | 12 => .impossible
  | 13 => (.covered 0)
  | 14 => (.covered 1)
  | 15 => .impossible
  | 16 => .impossible
  | 17 => .impossible
  | 18 => .impossible
  | 19 => .impossible
  | 20 => .impossible
  | 21 => .impossible
  | 22 => .impossible
  | 23 => .impossible
  | 24 => (.covered 2)
  | 25 => (.covered 3)
  | 26 => (.covered 4)
  | 27 => (.covered 5)
  | 28 => (.branch 25 (.branch 26 (.branch 27 (.branch 29 (.branch 31 (.branch 34 (.branch 36 .impossible .impossible) .impossible) .impossible) .impossible) .impossible) .impossible) (.branch 26 .impossible .impossible))
  | 29 => (.branch 28 (.branch 30 (.branch 32 (.branch 33 (.branch 35 (.branch 38 (.branch 39 .impossible .impossible) .impossible) .impossible) .impossible) .impossible) .impossible) (.branch 30 .impossible .impossible))
  | 30 => (.branch 99 (.branch 102 (.branch 104 (.branch 105 (.branch 107 (.branch 109 (.branch 110 .impossible .impossible) .impossible) .impossible) .impossible) .impossible) .impossible) (.branch 102 .impossible .impossible))
  | 31 => (.branch 97 (.branch 98 (.branch 100 (.branch 101 (.branch 103 (.branch 106 (.branch 108 .impossible .impossible) .impossible) .impossible) .impossible) .impossible) .impossible) (.branch 98 .impossible .impossible))
  | 32 => (.covered 6)
  | _ => (.covered 7)

set_option maxRecDepth 16384 in
private theorem pureCertificate_checked : ∀k : Fin 34,
    pureCheck (pureCertificate k) {0} (purePossible k)=true := by
  decide +kernel

/-- Product-closed pure sixteen-sets lie in one of eight explicit masks. -/
theorem pure_candidate_coverage (k : Fin 34) (s : Finset (Fin 192))
    (hs : s.card=16) (h0 : 0∈s) (hu : s⊆purePossible k)
    (hcomm : ∀v∈s,∀w∈s,compatible v w=true)
    (hcoset : ∀v w,w∈s → compatible v w=true →
      (productVertex v w∈s ↔ v∈s)) : ∃j : Fin 8,s⊆pureTargetSet j := by
  exact pureCheck_sound (pureCertificate k) {0} (purePossible k) s
    (pureCertificate_checked k) (by simpa only [Finset.singleton_subset_iff]) hu hs hcomm hcoset

end Held.OrdinaryElementary.NativeCoverage
