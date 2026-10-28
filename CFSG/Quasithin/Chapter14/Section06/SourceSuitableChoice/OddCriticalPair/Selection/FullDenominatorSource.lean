module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.FullDenominator
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.Critical

/-!
# The returned line on the original 14.6.13 setup

The original rank-two hypotheses supply F.9 with Vplus = V, the critical
length bound, and commutativity of intersecting plane conjugates. Applying
the full-denominator construction retains the same H, M and Mc. The original
critical-endpoint escape then puts the inverse conjugator outside Mc.

This discharges the earlier-source premises of the line-geometry branch;
recognition of the orthogonal module remains with the 14.6.13 assembly.
Source: Aschbacher--Smith, 14.6.13, first proof paragraph, printed p.1031.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.SourceCompletion
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))

include hG hempty hM hunique hmany hcard e hab hH

/-- The full-right-denominator branch of the original 14.6.13 setup supplies
an inverse endpoint outside the same Mc, with the literal line action on
U = ⟨(localModule T M)^H⟩. The original H, M and Mc are unchanged. -/
theorem source_rankTwo_returned_line_of_full
    (c : CriticalPair (sourceResidual M Mc) (T : Subgroup G) H (localModule T M))
    (hfull : Source.Dgamma (c.Ugamma (localModule T M))
      (conjugateSpanBy (localModule T M) H) (centralInvolutions T) =
        c.Ugamma (localModule T M)) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let h : D.Hypothesis :=
      source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    ∃ i : h.CriticalEndpoint, i.representative = (c.gb : G) ∧
      ∃ t : ReturnedLineAction H (conjugateSpanBy (localModule T M) H)
          (centralInvolutions T),
        t.g = i.representative⁻¹ ∧ t.g ∉ Mc := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let h : D.Hypothesis :=
    source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  change ∃ i : h.CriticalEndpoint, i.representative = (c.gb : G) ∧
    ∃ t : ReturnedLineAction D.H D.UH D.V₁, t.g = i.representative⁻¹ ∧ t.g ∉ Mc
  obtain ⟨hb,_,_⟩ :=
    source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab H hH
  have hbc : 3 ≤ c.path.length := by
    rw [c.length_eq,f9_criticalDistance_eq D h]
    exact hb
  obtain ⟨i,hi,t,ht⟩ := full_endpoint D h rfl c hbc
    (source_rankTwo_intersecting_conjugates_commute hG T hempty hM hunique hmany hcard e hab)
    hfull
  refine ⟨i,hi,t,ht,?_⟩
  rw [ht,inv_mem_iff]
  exact source_rankTwo_critical_not_mem_Mc hG T hempty hM hunique hmany hcard e hab H hH i

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
