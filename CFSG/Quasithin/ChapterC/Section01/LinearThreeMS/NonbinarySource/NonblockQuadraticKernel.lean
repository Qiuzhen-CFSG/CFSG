module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.QuadraticKernel
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed

/-!
# Quadratic offenders on the original nonblock whole central omega

The original 4.3.8--10 configuration supplies C_Q(K)=1 in both initial
module alternatives. At field four, quadratic offenders inside the whole
central-omega covering component therefore inject into the literal initial
action and the supplied full SL₃ marking. Their orders are at most sixteen.
Every component offender has a minimal quadratic replacement with these
properties. No whole-center model or vanishing covering kernel is assumed.

These are the actual source applications of QuadraticKernel. Recognition
of the whole center and upper Frattini sections is still required to finish
the nonblock classification. Source: Aschbacher--Smith C.1.34 and4.3.8--10,
printed pp.136--137,616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.QuadraticKernel
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))

/-- The original field-four component's quadratic offenders inject into the
literal initial central-omega action. -/
theorem source_quadratic_offender_initial_injective (hfour : Nat.card F = 4) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let q := QuotientGroup.mk' (centralizer (E : Set (K c ⊔ c.I.pCoreIn 2 : Subgroup G)))
    ∀ A, A ≤ (q.comp ((K c).subgroupOf (K c ⊔ c.I.pCoreIn 2)).subtype).range →
      IsOffender (CentralSections.coreOmegaRepresentation hm hn) A →
      IsQuadratic (CentralSections.coreOmegaRepresentation hm hn) A →
      Function.Injective ((NoncoreOffenders.toInitial hm hn E
        (CentralSections.coreOmegaLayer_centralizer_le hm hn)).comp A.subtype) := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.QuadraticKernel.field_four_quadratic_offender_initial_injective
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfour hfixed e

/-- These bounds concern the original whole-section offender, retaining
its full covering actor before applying the injective marked projection. -/
theorem source_quadratic_offender_bounds (hfour : Nat.card F = 4) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let q := QuotientGroup.mk' (centralizer (E : Set (K c ⊔ c.I.pCoreIn 2 : Subgroup G)))
    ∀ A, A ≤ (q.comp ((K c).subgroupOf (K c ⊔ c.I.pCoreIn 2)).subtype).range →
      IsOffender (CentralSections.coreOmegaRepresentation hm hn) A →
      IsQuadratic (CentralSections.coreOmegaRepresentation hm hn) A →
      Nat.card A ≤ 16 ∧ rank A ≤ 4 ∧
        fixedCodim (CentralSections.coreOmegaRepresentation hm hn) A ≤ 4 := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.QuadraticKernel.field_four_quadratic_offender_bounds
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfour hfixed e

/-- Quadratic replacement on the original covering component retains an
injective initial image and the field-four order bound. -/
theorem source_component_offender_replacement (hfour : Nat.card F = 4) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let q := QuotientGroup.mk' (centralizer (E : Set (K c ⊔ c.I.pCoreIn 2 : Subgroup G)))
    let rho := CentralSections.coreOmegaRepresentation hm hn
    ∀ A, A ≤ (q.comp ((K c).subgroupOf (K c ⊔ c.I.pCoreIn 2)).subtype).range →
      IsOffender rho A →
      ∃ B ≤ A, IsMinimalBestOffender rho B ∧ IsQuadratic rho B ∧
        weight rho A ≤ weight rho B ∧ Nat.card B ≤ 16 ∧
        Function.Injective ((NoncoreOffenders.toInitial hm hn E
          (CentralSections.coreOmegaLayer_centralizer_le hm hn)).comp B.subtype) := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.QuadraticKernel.field_four_component_offender_replacement
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfour hfixed e


/-- On the original whole central omega, every component offender gives
an FF action on each actual invariant Irr⁺ central section. -/
theorem source_component_irrPlus_isFF (hfour : Nat.card F = 4) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let q := QuotientGroup.mk' (centralizer (E : Set (K c ⊔ c.I.pCoreIn 2 : Subgroup G)))
    let rho := CentralSections.coreOmegaRepresentation hm hn
    let B := (q.comp ((K c).subgroupOf (K c ⊔ c.I.pCoreIn 2)).subtype).range
    ∀ A, A ≤ B → IsOffender rho A →
      ∀ (I : Submodule (ZMod 2) (Additive E)) (hI : IsIrrPlus rho B I),
      IsFFModule (imageRepresentation
        (centralSectionRepresentation rho B B I hI.choose B.le_normalizer)) := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.QuadraticKernel.field_four_component_irrPlus_isFF
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfour hfixed e

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.QuadraticKernel
