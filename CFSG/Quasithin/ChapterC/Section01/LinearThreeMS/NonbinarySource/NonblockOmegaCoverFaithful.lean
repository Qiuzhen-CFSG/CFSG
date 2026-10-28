module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.OmegaCoverFaithful
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed

/-!
# Faithful component marking in the original nonblock configuration

Apply the intrinsic central-omega faithfulness theorem to the actual
MS pair from the original configuration, chosen module and constrained
fitting hypothesis. InitialFixed supplies C_Q(K)=1. Consequently O₂(K)
centralizes the whole Ω₁(Z(Q)), even at field four, and the component image
on that whole layer is isomorphic to the originally supplied full SL₃.
The marking commutes with the literal original quotient map.

No Hypothesis1223, whole-section model or splitting premise is added.
Recognition of the entire center and the upper sections remains with
the nonbinary C.1.34 source assembly.
Source: Aschbacher–Smith C.1.34 and original 4.3.8–10, printed
pp.136–137,616–617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.OmegaCoverFaithful
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))

include D hf hn hF e in
/-- The original nonblock component's two-core centralizes the whole central
omega of its actual commutator Q, including the field-four case. -/
theorem source_componentCore_centralizes_omega :
    (K c).pCoreIn 2 ≤ centralizer
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
        (Q c) : Set G) := by
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  simpa only [ms_commutator_eq] using
    ChapterC.LinearThreeMS.NonbinarySource.OmegaCoverFaithful.componentCore_centralizes_omega
      (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed

/-- The literal original action component is the full marked SL₃, with
compatibility on every original representative and no extra ambient premise. -/
theorem source_faithful_marking :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let J := (K c ⊔ c.I.pCoreIn 2 : Subgroup G)
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    let q := QuotientGroup.mk' (centralizer (E : Set J))
    let B := (q.comp ((K c).subgroupOf J).subtype).range
    ∃ b : B ≃* SL(3,F), ∀ k : (K c).subgroupOf J,
      b ((q.comp ((K c).subgroupOf J).subtype).rangeRestrict k) =
        linearThreeActor e ⟨k,k.property⟩ := by
  let hm := msPair_of_quotient c D hf n (by omega) hF e
  let := CentralSections.coreOmegaLayer_normal hm hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ⟨ChapterC.LinearThreeMS.NonbinarySource.OmegaCoverFaithful.omegaEquiv hm hn hfixed e,
    ChapterC.LinearThreeMS.NonbinarySource.OmegaCoverFaithful.omegaEquiv_apply hm hn hfixed e⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.OmegaCoverFaithful
