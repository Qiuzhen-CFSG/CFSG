module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.PreparedSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicNoncommutingCatalogue

/-!
# Intrinsic noncommuting conclusion at the prepared source branch

The intrinsic Chapter 7 catalogue now discharges the complete reduced
noncommuting conclusion from `HypothesisF11` itself.  This bridge applies it to
the exact selected-factor source branch, retaining the original preparation,
input, Sylow containment and perfect-factor hypotheses in the public contract.
No actor-model or nonsolvability callback is inserted here.

Source: DGS, *Groups and Graphs* (1985), Chapters 6--7, pp.118--131.
-/

public noncomputable section
open Subgroup
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Prepared
open Chapter6.Source.RankOneGeneric DGS85.Reduction NoncommutingProfile
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H)
local notation "F" => reducedFamily ![L,R] (Global.sourceS L H)
include d h hTH

/-- The exact selected-factor source branch with the intrinsic noncommuting
catalogue applied directly.  All original source hypotheses remain explicit. -/
theorem noncommuting_source_conclusion_of_intrinsic (hp : Group.IsPerfect R)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    (b F = 1 ∨ b F = 2) ∧
    EqualFieldNaturalCenters (graphLocalGroup F v) (Z F v) (Q F v)
      (graphLocalGroup F w) (Z F w) (Q F w) ∧
    Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
    Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) := by
  let _ := hp
  exact Reduction.reduced_intrinsic_noncommuting_conclusion
    (d.hypothesisF11 h hTH) hc hne

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Prepared
