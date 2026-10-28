module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction.Schreier.Data
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue.Enumeration
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup

/-!
# Reducing literal HS Schreier membership to shared permutation images

Word codes decrease along their published predecessors. Induction therefore
identifies the candidate packed point maps with the actual word representatives.
An edge comparison then identifies the Schreier element with its specified row
of the original two-subgroup catalogue. The final corollary uses precisely the
universal norm module. Finite recurrence and edge checks remain explicit here.

Source: GM02 Proposition 5.1, HS case; Aschbacher--Smith K.4, printed p.457.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction
namespace SchreierData
open _root_.Sporadic.LeechRelated.HS
open _root_.Sporadic.LeechRelated.HS.EvenLocalCandidates

/-- The original carrier's inclusion into its degree-100 permutation group.
An explicit homomorphism avoids coercion inference through the catalogue alias. -/
def carrierPermutation (g : KnownSimple.SporadicName.hs.Carrier) : Equiv.Perm (Fin 100) :=
  _root_.Sporadic.LeechRelated.HS.generated.subtype g

/-- The packed generator maps are the original carrier generators. The private
FiveSubgroup implementation is used only to reuse its checked point tables. -/
theorem generator_point (s : Fin 2) (x : Fin 100) :
    carrierPermutation (generator s) x = letterPoint s x := by
  fin_cases s
  · change _root_.Sporadic.LeechRelated.HS.generatorA x = _
    rw [← FiveSubgroup.aPerm_eq_generator]
    rfl
  · change _root_.Sporadic.LeechRelated.HS.generatorB x = _
    rw [← FiveSubgroup.bPerm_eq_generator]
    rfl

/-- Each nonroot word has the stated shorter predecessor. -/
def PredecessorCodes : Prop := ∀ i : Tables.Index, i ≠ 0 →
  2 ≤ Tables.wordCode i ∧
    Tables.wordCode (predecessor i) = Tables.wordCode i / 2

/-- One generator application computes each nonroot candidate word image. -/
def ImageRecurrence : Prop := ∀ (i : Tables.Index) (x : Fin 100), i ≠ 0 →
  imagePoint i x = letterPoint (lastLetter i) (imagePoint (predecessor i) x)

/-- A literal edge, expressed without an inverse or a repeated full word. -/
def EdgeComparisons : Prop := ∀ (s : Fin 2) (i : Tables.Index) (x : Fin 100),
  letterPoint s (imagePoint i x) =
    imagePoint (Tables.transition s i) (SylowCatalogueData.point (subgroupRow s i) x)

theorem imagePoint_zero (x : Fin 100) : imagePoint 0 x = x := by
  revert x
  apply SylowCatalogueData.allFin
  decide +kernel

private theorem decodeWord_step (n : ℕ) (hn : 2 ≤ n) :
    decodeWord n = ⟨n % 2, Nat.mod_lt _ (by decide)⟩ :: decodeWord (n / 2) := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n => rw [decodeWord]

/-- The predecessor equality holds in the actual HS carrier. -/
theorem representative_predecessor (hc : PredecessorCodes)
    (i : Tables.Index) (hi : i ≠ 0) :
    representative i = generator (lastLetter i) * representative (predecessor i) := by
  unfold representative
  rw [decodeWord_step _ (hc i hi).1]
  simp only [List.map_cons, List.prod_cons, (hc i hi).2]
  rfl

/-- Shared predecessor images determine the entire literal word, by induction
on its positive binary code. No presentation-completeness input is needed. -/
theorem representative_point_of_recurrence (hc : PredecessorCodes) (hr : ImageRecurrence)
    (i : Tables.Index) (x : Fin 100) :
    carrierPermutation (representative i) x = imagePoint i x := by
  induction i using (measure Tables.wordCode).wf.induction with
  | h i ih =>
    by_cases hi : i = 0
    · subst i
      have hz : representative 0 = 1 := by
        simp [representative, wordCode_zero, decodeWord]
      rw [hz]
      exact (imagePoint_zero x).symm
    · rw [representative_predecessor hc i hi]
      change carrierPermutation (generator (lastLetter i))
        (carrierPermutation (representative (predecessor i)) x) = _
      have hlt : Tables.wordCode (predecessor i) < Tables.wordCode i := by
        rw [(hc i hi).2]
        exact Nat.div_lt_self (by have := (hc i hi).1; omega) (by decide)
      rw [ih (predecessor i) hlt, generator_point]
      exact (hr i x hi).symm

/-- The specified catalogue row, with the literal catalogue carrier as its
explicit type so group rewriting preserves the caller's instance. -/
def subgroupElement (s : Fin 2) (i : Tables.Index) : KnownSimple.SporadicName.hs.Carrier :=
  SylowCatalogueData.element (subgroupRow s i)

/-- The packed edge comparison identifies its exact subgroup catalogue row. -/
theorem schreier_eq_of_images
    (hp : ∀ (i : Tables.Index) (x : Fin 100),
      carrierPermutation (representative i) x = imagePoint i x)
    (he : EdgeComparisons) (s : Fin 2) (i : Tables.Index) :
    (representative (Tables.transition s i))⁻¹ * generator s * representative i =
      subgroupElement s i := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change carrierPermutation (generator s) (carrierPermutation (representative i) x) =
    carrierPermutation (representative (Tables.transition s i))
      ((SylowCatalogueData.element (subgroupRow s i) : Equiv.Perm (Fin 100)) x)
  rw [hp, generator_point, SylowCatalogueData.element_point, hp]
  exact he s i x

/-- The original subgroup membership follows from the two finite families. -/
theorem schreierCondition_of_checks (hc : PredecessorCodes) (hr : ImageRecurrence)
    (he : EdgeComparisons) : SchreierCondition := by
  intro s i
  rw [schreier_eq_of_images (representative_point_of_recurrence hc hr) he s i]
  exact SylowCatalogueData.element_mem (subgroupRow s i)

/-- Actual universal-module consumer, retaining precisely the finite checks
that still have to be supplied. This is not the unconditional table bound. -/
theorem universal_finrank_le_of_checks (hc : PredecessorCodes) (hr : ImageRecurrence)
    (he : EdgeComparisons) :
    Module.finrank (ZMod 2) CosetNormModule ≤
      Module.finrank (ZMod 2) (NormQuotient Tables.transition) :=
  universal_finrank_le (schreierCondition_of_checks hc hr he)

end SchreierData
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction
