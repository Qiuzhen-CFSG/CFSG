module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Parameters.Minimum
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Parameters.Setup
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Parameters.Strict
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero

/-!
# Exterior parameters and their literal weak-closure consumers

The full normalizer action identifies the actual automizer of the original
chosen module with SL₅(2). The involution calculation gives m=3. Hyperplane
centralizer control discharges the seven-exclusion premise in E.6.3, giving
r≥3 and s=3 without a Held-center assumption. The small-corank exterior
calculation and E.6.12--13 then exclude equality r=3.

The resulting source parameters are applied to the existing zeroth
weak-closure and point-control consumers, retaining their original quotient
maps and chosen module. Structural1222At remains the earlier input owned by
qt-d-1222-source; the original G₃,G₆ containments and the point-core input
belong to qt-d-1251-local. The outer fusion and classification assembly stays
with qt-d-1251-fusion-parameters-zero and qt-d-1251-fusion.

Source: Aschbacher--Smith, 12.5.6--7 and 12.5.9, printed pp.819--821.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- Original Lemma 12.5.6, on exactly the elementary abelian structure of D.
Only the authorized earlier structural and local containment inputs remain. -/
theorem SylowExteriorMarking.source_parameters (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M) :
    let := D.elementary
    (3 : ℕ∞) < globalR V ∧ localM V = 3 ∧ globalS V = 3 := by
  let := D.elementary
  exact ⟨s.three_lt_globalR h structural hG₃ hG₆, s.localM_eq_three h,
    (s.three_le_globalR_and_globalS_eq_three h structural hG₃).2⟩

/-- The source parameters discharge both numerical premises of 12.5.7. -/
theorem zero_clauses_of_source_parameters (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G) ∧
      0 < globalW V (T : Subgroup G) ∧
      normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ s.marking.M := by
  obtain ⟨hr, _, hs⟩ := s.source_parameters h structural hG₃ hG₆
  exact zero_clauses_of_parameters s h structural hG₆ hr hs

/-- Apply original 12.5.6--7 to the literal point-control input of the exterior
classification. The independent point-core input remains with the local owner. -/
theorem pointControl_of_source_parameters (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2) : PointControl s.marking := by
  obtain ⟨hw, _, hn⟩ := zero_clauses_of_source_parameters s h structural hG₃ hG₆
  exact pointControl_of_source_weakClosure s h structural hcore hw hn

/-- The completed full-automizer calculation removes the independent s premise
from the original zeroth weak-closure consumer. The r bound remains explicit. -/
theorem zero_clauses_of_strict_corank (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hr : (3 : ℕ∞) < globalR V) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G) ∧
      0 < globalW V (T : Subgroup G) ∧
      normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ s.marking.M := by
  let := D.elementary
  have hs : globalS V = 3 := by
    rw [globalS, s.localM_eq_three h]
    exact min_eq_right hr.le
  exact zero_clauses_of_parameters s h structural hG₆ hr hs

/-- The actual point-control input of the terminal exterior classification
now retains only the strict corank and earlier point-core inputs. -/
theorem pointControl_of_strict_corank (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hr : (3 : ℕ∞) < globalR V)
    (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2) : PointControl s.marking := by
  obtain ⟨hw, _, hn⟩ := zero_clauses_of_strict_corank s h structural hG₆ hr
  exact pointControl_of_source_weakClosure s h structural hcore hw hn

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
