module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralDerivedSections
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockDoubledCenter

/-!
# Marked central flags in the original nonabelian nonblock core

At field four, the genuine original configuration supplies natural or doubled
models of its entire center. In the natural branch that center lies in Q'
and Φ(Q). In the doubled branch the relative normal-subgroup intersection
argument constructs an actual natural central subgroup B in both layers,
with Z(Q)/B natural at the very same full SL₃ marking.

Thus the original nonabelian input has a natural central bottom layer with
no whole-core classification premise. B is normal in Q and normalized by K;
no invariance under the entire radical is asserted. The doubled nonabelian
exclusion and the doubled-dual upper section remain unproved, as does the
full arbitrary-degree C.1.34 classification.

Source: Aschbacher–Smith original 4.3.8–10, printed pp.616–617, and C.1.34,
pp.136–137. The original c, chosen module D, constrained hf, coefficient field
and full quotient are retained. No Hypothesis1223 is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.CentralDerivedSections
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

/-- The literal doubled-omega branch supplies a natural central subgroup in
Q' and Φ(Q), with natural quotient in U, at the same marking for every n>1. -/
theorem source_doubled_derived_flag
    (mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) O ⊥ (linearThreeActor mark)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (hna : ¬ IsMulCommutative (Q c)) :
    ∃ B : Subgroup G, B ≤ U c ∧ B ≤ ⁅Q c,Q c⁆ ∧ B ≤ frattiniIn (Q c) ∧
      HasSectionModel (K c) B ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
      HasSectionModel (K c) (U c) B (linearThreeActor mark) (specialLinearNatural 3) := by
  let hp := msPair_of_quotient c D hf n (by omega) hF e
  have hQ : IsPGroup 2 (Q c) := by
    rw [←ms_commutator_eq c]
    exact (isPGroup_pCoreIn 2 (K c ⊔ c.I.pCoreIn 2)).to_le msQ_le_joinCore
  have hKQ : K c ≤ normalizer (Q c : Set G) := by
    rw [←ms_commutator_eq c]
    exact (le_sup_left : K c ≤ K c ⊔ c.I.pCoreIn 2).trans
      (CentralSections.join_normalizes_core hp hn)
  exact ChapterC.LinearThreeMS.NonbinarySource.CentralDerivedSections.exists_derived_central_flag
    hQ hKQ mark (DoubledCenter.source_doubled_center c D hf n hn hF e mark hm).2 hna

/-- The actual field-four nonabelian source admits a natural central bottom
layer inside both characteristic layers. It is the whole center or has
natural quotient in the doubled center, with one common full quotient marking. -/
theorem source_nonabelian_central_flag
    (hfour : Nat.card F=4) (hna : ¬ IsMulCommutative (Q c)) :
    ∃ (mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) (B : Subgroup G),
      U c=O ∧ ⁅U c,K c⁆=U c ∧ U c ⊓ centralizer (K c : Set G)=⊥ ∧
      B ≤ U c ∧ B ≤ ⁅Q c,Q c⁆ ∧ B ≤ frattiniIn (Q c) ∧
      Q c ≤ normalizer (B : Set G) ∧
      HasSectionModel (K c) B ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
      (B=U c ∨
        (HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark)
          ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) ∧
          HasSectionModel (K c) (U c) B (linearThreeActor mark) (specialLinearNatural 3))) := by
  obtain ⟨mark,hU,hmoved,hfixed,hm | hm⟩ :=
    DoubledCenter.source_nonabelian_center_models c D hf n hn hF e hfour hna
  · exact ⟨mark,U c,hU,hmoved,hfixed,le_rfl,hm.2.1,hm.2.2,
      (Q c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (Q c) (center (Q c))),
      hm.1,Or.inl rfl⟩
  · have hmo : HasSectionModel (K c) O ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := hU ▸ hm
    obtain ⟨B,hBU,hBD,hBP,hB,hquot⟩ := source_doubled_derived_flag c D hf n hn hF e mark hmo hna
    have hQB : Q c ≤ normalizer (B : Set G) := by
      apply le_normalizer_iff.mpr
      intro q hq b hb
      obtain ⟨z,hz,he⟩ := hBU hb
      have hc : q*b=b*q := he ▸ congrArg (Q c).subtype (mem_center_iff.mp hz ⟨q,hq⟩)
      simpa only [hc,mul_inv_cancel_right] using hb
    exact ⟨mark,B,hU,hmoved,hfixed,hBU,hBD,hBP,hQB,hB,Or.inr ⟨hm,hquot⟩⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.CentralDerivedSections
