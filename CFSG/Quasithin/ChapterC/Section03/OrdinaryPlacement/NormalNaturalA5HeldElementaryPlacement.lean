module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryPureCoverage
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryCoreMasks
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryPureConjugators

/-!
# Native Held pure-sixteen placement

Actual elementary subgroups are reduced by the checked pure-vertex coverage.
The six exceptional masks have normalizer order prime to five by literal Held
conjugators; the two remaining masks are the actual marked local cores.
Source: Aschbacher--Smith 12.7.5, printed p.840.
-/
public section
open Subgroup
namespace Held.OrdinaryElementary
open NativeCoverage LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates.MaximalNormalizerCatalogue
open RankSixCertificate
open LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
/-- A pure elementary sixteen-subgroup whose normalizer has order divisible
by five lies in a genuine conjugate of a native elementary local core. -/
theorem pure_sixteen_le_conjugate_core_of_le (E : Subgroup He)
    [IsElementaryAbelian 2 E] (hE : Nat.card E=16)
    (hpure : ∀x:E,¬IsConj a (x:He))
    (h5 : 5∣Nat.card (normalizer (E:Set He))) (hEP : E≤representative) :
    ∃i : Bool,∃g : He,E≤(ambientWordCore i).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨j,hj⟩ := pure_sixteen_mask_of_le E hE hpure hEP
  by_cases hs : j.val<6
  · have hex : pureTarget j=13 ∨ pureTarget j=14 ∨ pureTarget j=24 ∨
        pureTarget j=25 ∨ pureTarget j=26 ∨ pureTarget j=27 := by
      have hd : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (pure_exception_not_five E hE (pureTarget j) hex hj h5).elim
  · have hd : j=6 ∨ j=7 := by omega
    rcases hd with rfl | rfl
    · exact ⟨true,conjugator (index 0),native_core_mask_le 0 E hj⟩
    · exact ⟨false,conjugator (index 1),native_core_mask_le 1 E hj⟩

end Held.OrdinaryElementary
