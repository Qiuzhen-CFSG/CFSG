module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CenterFourExclusion
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockNaturalOmegaCore

/-!
# The original nonblock center without a homocyclic lift

The original constrained configuration supplies its genuine MS-pair, full
SL₃ quotient and whole-omega alternatives. The intrinsic diagonal-torus
obstruction proves that its natural central omega is the entire natural
center at the same marking, for every nonbinary degree. In the nonabelian
branch this center lies in both Q' and Φ(Q). No quotient scalar is required.

The resulting alternatives retain the doubled whole central omega. They
exclude the previously retained canonical C₄^(3n) lift, without assuming
Hypothesis1223, a trivial covering kernel or an upper-section model. The
doubled nonabelian branch and the doubled-dual Q/Z(Q) reconstruction remain.
Source: Aschbacher–Smith original 4.3.8–10, printed pp.616–617, and C.1.34,
pp.136–137. The literal source groups and the supplied field are unchanged.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.CenterFourExclusion
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

/-- At every nonbinary degree, the natural whole central omega in the
original configuration is its entire center, at the supplied marking. -/
theorem source_center_eq_omega
    (mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) O ⊥ (linearThreeActor mark) (specialLinearNatural 3)) :
    U c=O := by
  let hp := msPair_of_quotient c D hf n (by omega) hF e
  have hm' : HasSectionModel (K c)
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
        (msQ (K c) (c.I.pCoreIn 2))) ⊥ (linearThreeActor mark) (specialLinearNatural 3) := by
    simpa only [ms_commutator_eq] using hm
  simpa only [ms_commutator_eq,
    show Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
      (Q c) = U c from rfl] using
    ChapterC.LinearThreeMS.NonbinarySource.CenterFourExclusion.center_eq_omega hp hn mark hm'

/-- The original natural-omega branch has the entire natural center at the
same marking for every nonbinary field, including odd degree. -/
theorem source_center_natural
    (mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) O ⊥ (linearThreeActor mark) (specialLinearNatural 3)) :
    HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark) (specialLinearNatural 3) := by
  exact (source_center_eq_omega c D hf n hn hF e mark hm).symm ▸ hm

/-- The original nonabelian natural-omega branch has natural whole center
inside both Q' and Φ(Q), at every nonbinary degree and the original marking. -/
theorem source_natural_center_layers
    (mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) O ⊥ (linearThreeActor mark) (specialLinearNatural 3))
    (hna : ¬ IsMulCommutative (Q c)) :
    HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
      U c ≤ ⁅Q c,Q c⁆ ∧ U c ≤ frattiniIn (Q c) := by
  have he := source_center_eq_omega c D hf n hn hF e mark hm
  exact ⟨source_center_natural c D hf n hn hF e mark hm,
    he.symm ▸ (NaturalOmegaCore.source_natural_omega_layers c D hf n hn hF e mark hm hna).2⟩

-- Retain the original named field-size argument for compatibility.
set_option linter.unusedVariables false in
/-- Compatibility with the original field-four natural-center application. -/
theorem source_center_natural_of_omega
    (mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) O ⊥ (linearThreeActor mark) (specialLinearNatural 3))
    (hfour : Nat.card F=4) :
    HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark) (specialLinearNatural 3) := by
  exact source_center_natural c D hf n hn hF e mark hm

/-- The original nonabelian field-four center is natural inside Q' and Φ(Q),
or its whole central omega is doubled natural. The canonical four-lift is
excluded without changing the source configuration or the common marking. -/
theorem source_nonabelian_center_alternatives
    (hfour : Nat.card F=4) (hna : ¬ IsMulCommutative (Q c)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      ⁅U c,K c⁆ = U c ∧ U c ⊓ centralizer (K c : Set G) = ⊥ ∧
      ((HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
        U c ≤ ⁅Q c,Q c⁆ ∧ U c ≤ frattiniIn (Q c)) ∨
      HasSectionModel (K c) O ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) := by
  obtain ⟨mark,hmove,hfixed,hm | hm | hm⟩ :=
    NaturalOmegaCore.source_nonabelian_center_alternatives c D hf n hn hF e hfour hna
  · exact ⟨mark,hmove,hfixed,Or.inl hm⟩
  · exact ⟨mark,hmove,hfixed,Or.inr hm⟩
  · obtain ⟨hm,hderived,hPhi,_⟩ := hm
    have hc := source_center_natural_of_omega c D hf n hn hF e mark hm hfour
    let hp := msPair_of_quotient c D hf n (by omega) hF e
    have hZU : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
        (Q c) = U c := rfl
    have hinit := NaturalCenter.center_eq_initial hp hn mark
      (by simpa only [ms_commutator_eq,hZU] using hc)
    rw [ms_commutator_eq] at hinit
    have ho := (NaturalOmegaCore.source_natural_omega_layers c D hf n hn hF e mark hm hna).1
    have hue : U c=O := hinit.trans ho.symm
    exact ⟨mark,hmove,hfixed,Or.inl ⟨hc,hue ▸ hderived,hue ▸ hPhi⟩⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.CenterFourExclusion
