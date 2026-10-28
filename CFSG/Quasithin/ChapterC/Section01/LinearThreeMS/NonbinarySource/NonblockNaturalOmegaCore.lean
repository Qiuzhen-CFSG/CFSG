module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NaturalOmegaCore
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockOmegaSplitFour
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CenterPowerSections

/-!
# Original nonblock normal layers and whole-center movement

The genuine nonblock MS-pair and its chosen module supply the field-four
whole-omega alternatives. The intrinsic fixed-point calculation gives an
actual element of the original component fixing only the identity of U=Z(Q).
In every nonbinary degree, a natural whole central omega equals the original
initial moved subgroup and, for nonabelian Q, lies in Q' and Φ(Q).

At field four these facts sharpen the existing center reconstruction at one
common full SL₃ marking. The whole natural center lies in both characteristic
layers. The remaining alternatives retain the doubled whole omega or the
canonical Ω₂(U) of type C₄^(3n), together with the natural bottom layer in
Q' and Φ(Q). In all branches [U,K]=U and C_U(K)=1. Neither the upper sections
nor the exponent-four obstruction is discharged by this reduction.

No ambient Hypothesis1223, new classification callback, or equivariant
complement is assumed. The original constrained hypothesis, field and quotient
map are retained throughout. Source: Aschbacher–Smith original 4.3.8–10,
printed pp.616–617, and C.1.34, pp.136–137.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.NaturalOmegaCore
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

/-- The original field-four source has an actual component element fixing
only the identity in its entire center. This uses the whole-omega alternatives
at one marking, including their possible doubled branch. -/
theorem source_center_fixedFree (hfour : Nat.card F = 4) :
    ∃ k : K c, U c ⊓ centralizer ({(k : G)} : Set G) = ⊥ := by
  obtain ⟨mark,hm⟩ := OmegaSplitFour.source_omega_section_models c D hf n hn hF e hfour
  have hp : IsPGroup 2 (Q c) := by
    rw [←ms_commutator_eq c]
    exact (isPGroup_pCoreIn 2 (K c ⊔ c.I.pCoreIn 2)).to_le msQ_le_joinCore
  exact ChapterC.LinearThreeMS.NonbinarySource.NaturalOmegaCore.exists_center_fixedFree hp mark hm

omit [CharP F 2] in
/-- At every nonbinary degree, a natural whole central omega in the original
configuration is its initial moved subgroup. In the nonabelian branch it lies
in both the actual derived subgroup and the actual Frattini subgroup. -/
theorem source_natural_omega_layers
    (mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) O ⊥ (linearThreeActor mark) (specialLinearNatural 3))
    (hna : ¬ IsMulCommutative (Q c)) :
    O = initialMoved (K c) (c.I.pCoreIn 2) ∧
      O ≤ ⁅Q c,Q c⁆ ∧ O ≤ frattiniIn (Q c) := by
  let hp := msPair_of_quotient c D hf n (by omega) hF e
  have hm' : HasSectionModel (K c)
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
        (msQ (K c) (c.I.pCoreIn 2))) ⊥ (linearThreeActor mark) (specialLinearNatural 3) := by
    simpa only [ms_commutator_eq] using hm
  have ho := ChapterC.LinearThreeMS.NonbinarySource.NaturalOmegaCore.omega_eq_initial hp hn mark hm'
  have hl := ChapterC.LinearThreeMS.NonbinarySource.NaturalOmegaCore.initial_le_derived_and_frattini
    hp hn mark hm' ((ms_commutator_eq c).symm ▸ hna)
  rw [ms_commutator_eq] at ho hl
  exact ⟨ho,ho ▸ hl⟩

/-- The actual nonabelian field-four input has a natural whole center inside
Q' and Φ(Q), doubled central omega, or its canonical homocyclic four-lift.
The lift branch retains the entire natural omega inside both characteristic
layers, and all section models share the same full SL₃ marking. -/
theorem source_nonabelian_center_alternatives
    (hfour : Nat.card F = 4) (hna : ¬ IsMulCommutative (Q c)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      ⁅U c,K c⁆ = U c ∧ U c ⊓ centralizer (K c : Set G) = ⊥ ∧
      (
      (HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
        U c ≤ ⁅Q c,Q c⁆ ∧ U c ≤ frattiniIn (Q c)) ∨
      HasSectionModel (K c) O ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) ∨
      (HasSectionModel (K c) O ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
        O ≤ ⁅Q c,Q c⁆ ∧ O ≤ frattiniIn (Q c) ∧
        let Y := (omega (U c) (p := 2) 2).map (U c).subtype
        (K c ⊔ c.I.pCoreIn 2) ≤ normalizer (Y : Set G) ∧
          Nonempty (Y ≃* StandardHomocyclicCover (Fin (3*n)) 4) ∧
          HasSectionModel (K c) Y O (linearThreeActor mark) (specialLinearNatural 3))) := by
  obtain ⟨mark,hm⟩ := OmegaSplitFour.source_omega_section_models c D hf n hn hF e hfour
  let hp := msPair_of_quotient c D hf n (by omega) hF e
  have hQp : IsPGroup 2 (Q c) := by
    rw [←ms_commutator_eq c]
    exact (isPGroup_pCoreIn 2 (K c ⊔ c.I.pCoreIn 2)).to_le msQ_le_joinCore
  have hKQ : K c ≤ normalizer (Q c : Set G) := by
    rw [←ms_commutator_eq c]
    exact (le_sup_left : K c ≤ K c ⊔ c.I.pCoreIn 2).trans
      (CentralSections.join_normalizes_core hp hn)
  have hmove := ChapterC.LinearThreeMS.NonbinarySource.NaturalOmegaCore.center_moved_of_omega_models
    hQp hKQ mark hm
  refine ⟨mark,hmove.1,hmove.2,?_⟩
  rcases hm with hm | hm
  · have hl := (source_natural_omega_layers c D hf n hn hF e mark hm hna).2
    have hm' : HasSectionModel (K c)
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
          (msQ (K c) (c.I.pCoreIn 2))) ⊥ (linearThreeActor mark) (specialLinearNatural 3) := by
      simpa only [ms_commutator_eq] using hm
    have he := ChapterC.LinearThreeMS.NonbinarySource.CenterPowerSections.center_natural_or_four_lift
      hp hn mark hm'
    rw [ms_commutator_eq] at he
    rcases he with hcenter | hlift
    · have hinit := NaturalCenter.center_eq_initial hp hn mark
        (by simpa only [ms_commutator_eq] using hcenter)
      rw [ms_commutator_eq] at hinit
      have ho := (source_natural_omega_layers c D hf n hn hF e mark hm hna).1
      have hue : U c = O := hinit.trans ho.symm
      exact Or.inl ⟨hcenter,hue ▸ hl⟩
    · exact Or.inr (Or.inr ⟨hm,hl.1,hl.2,hlift⟩)
  · exact Or.inr (Or.inl hm)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.NaturalOmegaCore
