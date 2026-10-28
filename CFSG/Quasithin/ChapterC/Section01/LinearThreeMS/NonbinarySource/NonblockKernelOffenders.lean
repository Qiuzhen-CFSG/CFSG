module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.KernelOffenders
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed

/-!
# Exceptional-kernel offenders in the original nonblock configuration

For the component and radical selected in original 4.3.8--10, the checked
initial-layer argument gives C_Q(K)=1 in both source alternatives. Thus the
actual component image on the entire central omega of Q has zero fixed space.
At field four, no offender can lie in the image of the intrinsic component
two-core, and every component offender survives on the initial action.

The applications retain the original configuration, chosen module, constrained
hypothesis and full quotient marking. They supply the fixed-space premise of
`KernelOffenders`; they do not assume a model for the whole center or erase the
exceptional covering kernel. Whole-section recognition remains required for
the C.1.34 classification and its original 4.3.8--10 assembly.
Source: Aschbacher--Smith C.1.34, pp.136--137, and 4.3.8--10, pp.616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.KernelOffenders
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))

/-- The original component fixes no vector on the whole central omega. -/
theorem source_coreOmega_fixedSpace_eq_bot :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let q := QuotientGroup.mk' (centralizer (E : Set (K c ⊔ c.I.pCoreIn 2 : Subgroup G)))
    fixedSpace (CentralSections.coreOmegaRepresentation hm hn)
      (q.comp ((K c).subgroupOf (K c ⊔ c.I.pCoreIn 2)).subtype).range = ⊥ := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.KernelOffenders.omega_fixedSpace_eq_bot
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed

/-- At field four the image of the intrinsic component two-core contains no offender. -/
theorem source_field_four_no_core_offender (hfour : Nat.card F = 4) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let q := QuotientGroup.mk' (centralizer (E : Set (K c ⊔ c.I.pCoreIn 2 : Subgroup G)))
    ∀ A, A ≤ (((K c).subgroupOf (K c ⊔ c.I.pCoreIn 2)).pCoreIn 2).map q →
      ¬ IsOffender (CentralSections.coreOmegaRepresentation hm hn) A := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.KernelOffenders.field_four_no_core_offender
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfour hfixed e

/-- Every offender in the original covering component has nontrivial initial image. -/
theorem source_field_four_component_offender_initial_ne_bot (hfour : Nat.card F = 4) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let q := QuotientGroup.mk' (centralizer (E : Set (K c ⊔ c.I.pCoreIn 2 : Subgroup G)))
    ∀ A, A ≤ (q.comp ((K c).subgroupOf (K c ⊔ c.I.pCoreIn 2)).subtype).range →
      IsOffender (CentralSections.coreOmegaRepresentation hm hn) A →
      A.map (NoncoreOffenders.toInitial hm hn E
        (CentralSections.coreOmegaLayer_centralizer_le hm hn)) ≠ ⊥ := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.KernelOffenders.field_four_component_offender_initial_ne_bot
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfour hfixed e

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.KernelOffenders
