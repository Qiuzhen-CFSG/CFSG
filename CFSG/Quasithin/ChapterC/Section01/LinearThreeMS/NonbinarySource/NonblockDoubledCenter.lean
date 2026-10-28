module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.DoubledCenter
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockCenterFourExclusion

/-!
# Whole-center models in the original constrained nonblock configuration

Apply the doubled central-omega exponent obstruction to the original
MS-pair from its full SL₃ quotient. The supplied marking is unchanged,
including at field four. Both branches of the nonabelian field-four
reduction now have models of the entire center, which is elementary;
the natural branch also retains its containment in Q' and Φ(Q).

The doubled nonabelian exclusion and the common-marking upper/Frattini
sections remain unproved. No Hypothesis1223, whole-core classification,
strong-offender premise or injective-cover premise is added here.
Source: Aschbacher–Smith original 4.3.8–10, printed pp.616–617, and C.1.34,
pp.136–137. The original c, chosen module, field and full quotient are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.DoubledCenter
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
include D hf hn hF e
local notation "O" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c)

/-- The original doubled-omega branch is the entire doubled natural center,
at the same full quotient marking, over every nonbinary coefficient field. -/
theorem source_doubled_center
    (mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) O ⊥ (linearThreeActor mark)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) :
    U c=O ∧ HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := by
  let hp := msPair_of_quotient c D hf n (by omega) hF e
  have hm' : HasSectionModel (K c)
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
        (msQ (K c) (c.I.pCoreIn 2))) ⊥ (linearThreeActor mark)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := by
    simpa only [ms_commutator_eq] using hm
  have he : U c=O := by
    simpa only [ms_commutator_eq,
      show Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
        (Q c) = U c from rfl] using
      ChapterC.LinearThreeMS.NonbinarySource.DoubledCenter.center_eq_omega hp hn mark hm'
  exact ⟨he,he.symm ▸ hm⟩

/-- Both field-four nonabelian alternatives now describe the whole center.
The natural branch lies in the derived and Frattini subgroups; the doubled
branch retains its complete center, without asserting that Q is abelian. -/
theorem source_nonabelian_center_models
    (hfour : Nat.card F=4) (hna : ¬ IsMulCommutative (Q c)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      U c=O ∧ ⁅U c,K c⁆ = U c ∧ U c ⊓ centralizer (K c : Set G) = ⊥ ∧
      ((HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
        U c ≤ ⁅Q c,Q c⁆ ∧ U c ≤ frattiniIn (Q c)) ∨
      HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) := by
  obtain ⟨mark,hmove,hfixed,hm | hm⟩ :=
    CenterFourExclusion.source_nonabelian_center_alternatives c D hf n hn hF e hfour hna
  · have hZ : U c=O := by
      let hp := msPair_of_quotient c D hf n (by omega) hF e
      have hU : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
          (Q c)=U c := rfl
      have hcenter := ChapterC.LinearThreeMS.NonbinarySource.NaturalCenter.center_eq_initial
        hp hn mark (by simpa only [ms_commutator_eq,hU] using hm.1)
      have hinit : initialMoved (K c) (c.I.pCoreIn 2) ≤ O := by
        simpa only [ms_commutator_eq] using
          (CentralSections.initialMoved_le_omegaCenter (K := K c) (R := c.I.pCoreIn 2))
      apply le_antisymm _ (map_mono (map_subtype_le _))
      calc
        U c = initialMoved (K c) (c.I.pCoreIn 2) := by
          simpa only [ms_commutator_eq,hU] using hcenter
        _ ≤ O := hinit
    exact ⟨mark,hZ,hmove,hfixed,Or.inl hm⟩
  · obtain ⟨he,hd⟩ := source_doubled_center c D hf n hn hF e mark hm
    exact ⟨mark,he,hmove,hfixed,Or.inr hd⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.DoubledCenter
