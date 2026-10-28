module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CenterPowerSections
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed

/-!
# The whole-center power sections in the original nonblock configuration

The original chosen module and constrained configuration supply the genuine
nonbinary MS-pair and C_Q(K)=1. At field four its natural omega branch now
also identifies the whole U/Φ(U), where U=Z(Q), as natural at exactly the same
full SL₃ marking. The doubled omega branch is retained without discarding
central attachments or possible higher exponent of U. A second application
reduces the natural-omega case to the whole natural center or its canonical
homocyclic Ω₂(U), with both natural sections at the same marking.

This discharges the power-section step from the original source input.
The identification U=Ω₁(U), the nonabelian Q/U model, and full C.1.34 remain
with the intrinsic classifier. The denominator here is Φ(U), not Φ(Q).
Source: Aschbacher–Smith original 4.3.8–10, pp.616–617, and C.1.34,
pp.136–137. No Hypothesis1223 or classification callback is assumed.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.CenterPowerSections
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
include D hf hn hF e

/-- The original configuration has the same natural marking on the bottom
and top elementary sections of its entire center, or doubled central omega. -/
theorem source_center_section_alternatives (hfour : Nat.card F = 4) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      (HasSectionModel (K c)
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c))
        ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
        HasSectionModel (K c) (U c) (frattiniIn (U c))
          (linearThreeActor mark) (specialLinearNatural 3)) ∨
      HasSectionModel (K c)
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c))
        ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := by
  let hm := msPair_of_quotient c D hf n (by omega) hF e
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  simpa only [ms_commutator_eq,
    show Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (Q c) = U c from rfl] using
    ChapterC.LinearThreeMS.NonbinarySource.CenterPowerSections.center_section_alternatives
      hm hn hfixed hfour

/-- The original nonblock input supplies the complete center-reconstruction
reduction, retaining a possible canonical homocyclic four-torsion subgroup. -/
theorem source_center_reconstruction_alternatives (hfour : Nat.card F = 4) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∨
      HasSectionModel (K c)
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c))
        ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) ∨
      (HasSectionModel (K c)
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c))
        ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
        let Y := (omega (U c) (p := 2) 2).map (U c).subtype
        (K c ⊔ c.I.pCoreIn 2) ≤ normalizer (Y : Set G) ∧
          Nonempty (Y ≃* StandardHomocyclicCover (Fin (3*n)) 4) ∧
          HasSectionModel (K c) Y
            (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c))
            (linearThreeActor mark) (specialLinearNatural 3)) := by
  let hm := msPair_of_quotient c D hf n (by omega) hF e
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  let P (X : Subgroup G) : Prop :=
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      HasSectionModel (K c) (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn X) ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∨
      HasSectionModel (K c)
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn X)
        ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) ∨
      (HasSectionModel (K c)
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn X)
        ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
        let Y := (omega (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn X) (p := 2) 2).map (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn X).subtype
        (K c ⊔ c.I.pCoreIn 2) ≤ normalizer (Y : Set G) ∧
          Nonempty (Y ≃* StandardHomocyclicCover (Fin (3*n)) 4) ∧
          HasSectionModel (K c) Y
            (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn X)
            (linearThreeActor mark) (specialLinearNatural 3))
  have ht : P (msQ (K c) (c.I.pCoreIn 2)) :=
    ChapterC.LinearThreeMS.NonbinarySource.CenterPowerSections.center_reconstruction_alternatives
      hm hn hfixed hfour
  have ht' : P (Q c) := Eq.mp (congrArg P (ms_commutator_eq c)) ht
  simpa only [P,U,Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn] using ht'

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.CenterPowerSections
