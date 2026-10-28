module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NonElementaryMarkedProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryMarkedConsumers

/-!
# Both commuting-edge branches at the original chosen-factor consumer

Split on the literal full-Borel quotient S₀/Q_beta. The elementary branch
constructs the U₄ profile; the nonelementary branch constructs the complete
U₅ profile and uses the proved all-fields recognition. Nonsolvability of
the prepared parabolics supplies the local catalogues and identifies each
actor with its original starred endpoint. Chapter 15 then restores the
original pair and the entire original Borel, including its odd part.

The full KnownSimple Chapter 12 application uses the same arbitrary selected
perfect factor. Only the marked split quotient and rotation order four
remain Chapter 14 inputs. This does not prove their construction or the
unrestricted solvable order-144 source branch.
Source: DGS (1985), (11.7)--(11.8), pp.174--177, Theorem D and (15.2),
pp.224,226--228; Aschbacher--Smith F.1.12 and 12.2.2.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingOneProfile
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- Restore the original pair from its literal nonelementary commuting-edge
branch. No U₅ profile, factor marking or comparison is an input. -/
theorem comparison_of_commuting_one_nonElementary
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false)
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true))
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false),
      Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)⁆ = ⊥)
    (hne : letI := QuadrangleStructure.original_core_normal_in_sylow (L := ![L,R]) (S := reducedSylow ![L,R] (sourceS L H)) 1
      ¬ IsElementaryAbelian 2 (reducedSylow ![L,R] (sourceS L H) ⧸
        ((parabolic ![L,R] (reducedSylow ![L,R] (sourceS L H)) 1).pCoreIn 2).subgroupOf
          (reducedSylow ![L,R] (sourceS L H))))
    (quot : MarkedQuotient P)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) quot.standardAmalgam)
    (split : SplitData quot.tits) (hrot : rotationOrder quot = 4) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  obtain ⟨m,hm,⟨c⟩⟩ := original_nonsolvable_nonElementary_reduced_comparison
    (d.hypothesisF11 h hTH) hc hb hcomm (d.parabolics_not_solvable h hp) hne quot e split hrot
  exact d.concreteComparison_of_reduced_alternatives h hTH hp
    (.unitaryFive (2^m) (Nat.prime_two.isPrimePow.pow (Nat.ne_of_gt hm))
      (even_two.pow_of_ne_zero (Nat.ne_of_gt hm)) c.model false ⟨c.comparison⟩)

/-- Both source branches give the original comparison on the same selected
factor, without an elementary-quotient or profile-selection premise. -/
theorem comparison_of_commuting_one
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false)
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true))
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false),
      Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)⁆ = ⊥)
    (quot : MarkedQuotient P)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) quot.standardAmalgam)
    (split : SplitData quot.tits) (hrot : rotationOrder quot = 4) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  have row := original_nonsolvable_commuting_one_marked_row
    (d.hypothesisF11 h hTH) hc hb hcomm (d.parabolics_not_solvable h hp) quot e split hrot
  exact d.concreteComparison_of_reduced_alternatives h hTH hp
    (UnitarySource.Combined.reduced_alternative_of_five_source (d.hypothesisF11 h hTH)
      quot e split hrot (UnitaryFiveSource.five_source_theorem quot e split) row)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingOneProfile
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
  (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
    (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false)
    (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true))
  (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1)
  (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false),
    Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true)⁆ = ⊥)
  (hne : letI := QuadrangleStructure.original_core_normal_in_sylow (L := ![L,R]) (S := reducedSylow ![L,R] (Global.sourceS L H)) 1
    ¬ IsElementaryAbelian 2 (reducedSylow ![L,R] (Global.sourceS L H) ⧸
      ((parabolic ![L,R] (reducedSylow ![L,R] (Global.sourceS L H)) 1).pCoreIn 2).subgroupOf
        (reducedSylow ![L,R] (Global.sourceS L H))))
  {P : Fin 2 → Subgroup X} (quot : MarkedQuotient P)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) quot.standardAmalgam)
  (split : SplitData quot.tits) (hrot : rotationOrder quot = 4)

include D h hmany hn hpsl hH d hp hc hb hcomm hne e split hrot in
/-- The full KnownSimple chosen-module consumer on the same selected perfect
factor. No source profile or local actor marking remains as an extra input. -/
theorem rankOne_comparison_of_commuting_one_nonElementary :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.comparison_of_commuting_one_nonElementary
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp
    hc hb hcomm hne quot e split hrot

omit hne in
include D h hmany hn hpsl hH d hp hc hb hcomm e split hrot in
/-- The full KnownSimple chosen-module consumer needs neither a local
catalogue nor a Chapter 11 row selection on the commuting distance-one branch. -/
theorem rankOne_comparison_of_commuting_one :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.comparison_of_commuting_one
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp
    hc hb hcomm quot e split hrot

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
