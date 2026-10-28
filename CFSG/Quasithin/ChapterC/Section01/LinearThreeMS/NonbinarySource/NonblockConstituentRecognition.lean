module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.ConstituentRecognition
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed

/-!
# Natural central constituents in the original nonblock configuration

The original 4.3.8--10 hypotheses discharge C_Q(K)=1. In the restriction
of the actual source Sylow intersection to KR, a maximum elementary
subgroup supplies one minimal offender preserving every Irr⁺ central
section. Each section's faithful component image is natural over the
supplied field. An actual constituent exists and has order |F|³ and
binary dimension 3n.

All applications retain c, the chosen module, the constrained hypothesis,
field size and full quotient marking. The whole covering kernel is retained;
whole-section reconstruction and a common marking remain necessary for
C.1.34 and the final nonblock MSData construction.
Source: Aschbacher--Smith C.1.34 and original 4.3.8--10,
printed pp.136--137,616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.ConstituentRecognition
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))

/-- The source's actual Sylow intersection supplies one minimal offender
preserving every Irr⁺ section; each section's faithful component image is
natural over the original field, including field four. -/
theorem source_irrPlus_local_natural :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let J := (K c ⊔ c.I.pCoreIn 2 : Subgroup G)
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let q := QuotientGroup.mk' (centralizer (E : Set J))
    let B := (q.comp ((K c).subgroupOf J).subtype).range
    let rho := CentralSections.coreOmegaRepresentation hm hn
    ∃ A ∈ elementaryAbelianMaxSubgroups ((S c).subgroupOf J), ∃ X ≤ A.map q,
      IsMinimalBestOffender rho X ∧
      ∀ (I : Submodule (ZMod 2) (Additive E)) (_hI : IsIrrPlus rho B I),
        ChapterC.LinearThreeMS.NonbinarySource.ConstituentRecognition.HasNaturalCentralSection
          rho B X I
          (ChapterC.LinearThreeMS.NonbinarySource.ConstituentRecognition.coefficientField hm hn) := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.ConstituentRecognition.irrPlus_local_natural
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed e _
    (comap_mono (c.core_sylow.le.trans inf_le_left))

/-- Every actual Irr⁺ subspace of the original whole central omega has the
natural order and dimension, without an assumed constituent model. -/
theorem source_irrPlus_card_finrank :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let J := (K c ⊔ c.I.pCoreIn 2 : Subgroup G)
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let q := QuotientGroup.mk' (centralizer (E : Set J))
    let B := (q.comp ((K c).subgroupOf J).subtype).range
    let rho := CentralSections.coreOmegaRepresentation hm hn
    ∀ (I : Submodule (ZMod 2) (Additive E)), IsIrrPlus rho B I →
      Nat.card I = Nat.card F ^ 3 ∧ Module.finrank (ZMod 2) I = 3*n := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.ConstituentRecognition.irrPlus_card_finrank
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed e

/-- An actual noncentral constituent of the original whole central omega,
with the source natural order and binary dimension. -/
theorem source_exists_irrPlus :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let J := (K c ⊔ c.I.pCoreIn 2 : Subgroup G)
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let q := QuotientGroup.mk' (centralizer (E : Set J))
    let B := (q.comp ((K c).subgroupOf J).subtype).range
    let rho := CentralSections.coreOmegaRepresentation hm hn
    ∃ I : Submodule (ZMod 2) (Additive E), IsIrrPlus rho B I ∧
      Nat.card I = Nat.card F ^ 3 ∧ Module.finrank (ZMod 2) I = 3*n := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  obtain ⟨I,hI⟩ := ChapterC.LinearThreeMS.NonbinarySource.ConstituentRecognition.exists_irrPlus
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  exact ⟨I,hI,source_irrPlus_card_finrank c D hf n hn hF e I hI⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.ConstituentRecognition
