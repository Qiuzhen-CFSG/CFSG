module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.ConstituentSections
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed

/-!
# Actual natural central constituents in the original nonblock configuration

The original 4.3.8--10 hypotheses give C_Q(K)=1. Each Irr⁺ subspace of
the full central omega therefore yields a literal natural subgroup of Q,
with centralizer exactly O₂(K), natural order, and a section model whose
marking differs from the supplied full quotient marking by a displayed
SL₃ automorphism. Such a subgroup exists, including at field four.

The applications retain c, ChosenModule D, hf, the original field, and the
full quotient equivalence. They do not identify one constituent with the
whole center or assert a common natural/dual marking for all sections.
Those reconstruction steps and the full C.1.34 assembly remain open.
Source: Aschbacher--Smith C.1.34 and original 4.3.8--10,
printed pp.136--137,616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.ConstituentSections
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))

/-- Every constituent of the original whole central omega is an actual natural
subgroup, with its complete kernel and relation to the supplied marking. -/
theorem source_constituent_sections :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let J := (K c ⊔ c.I.pCoreIn 2 : Subgroup G)
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let q := QuotientGroup.mk' (centralizer (E : Set J))
    let B := (q.comp ((K c).subgroupOf J).subtype).range
    let rho := CentralSections.coreOmegaRepresentation hm hn
    ∀ (I : Submodule (ZMod 2) (Additive E)), IsIrrPlus rho B I →
      let U := ChapterC.LinearThreeMS.NonbinarySource.ConstituentSections.subgroup I
      U ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c) ∧
      Nat.card U = Nat.card F ^ 3 ∧
      (centralizer (U : Set G)).subgroupOf (K c) = pCore 2 (K c) ∧
      ∃ α : SL(3,F) ≃* SL(3,F),
        HasSectionModel (K c) U ⊥ (linearThreeActor (e.trans α)) (specialLinearNatural 3) := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  dsimp only
  intro I hI
  refine ⟨?_,ChapterC.LinearThreeMS.NonbinarySource.ConstituentSections.subgroup_card
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed e I hI,
    ChapterC.LinearThreeMS.NonbinarySource.ConstituentSections.subgroup_centralizer
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed e I hI,
    ChapterC.LinearThreeMS.NonbinarySource.ConstituentSections.irrPlus_section_model
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed e I hI⟩
  simpa only [ms_commutator_eq] using
    ChapterC.LinearThreeMS.NonbinarySource.ConstituentSections.subgroup_le_omegaCenter I

include D hf hn hF in
/-- The original nonblock hypotheses supply a concrete natural subgroup of
Ω₁(Z(Q)), including at field four, without an assumed section model. -/
theorem source_exists_natural_subgroup :
    ∃ U : Subgroup G,
      U ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c) ∧
      Nat.card U = Nat.card F ^ 3 ∧
      (centralizer (U : Set G)).subgroupOf (K c) = pCore 2 (K c) ∧
      ∃ α : SL(3,F) ≃* SL(3,F),
        HasSectionModel (K c) U ⊥ (linearThreeActor (e.trans α)) (specialLinearNatural 3) := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  simpa only [ms_commutator_eq] using
    ChapterC.LinearThreeMS.NonbinarySource.ConstituentSections.exists_natural_subgroup
      (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed e

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.ConstituentSections
