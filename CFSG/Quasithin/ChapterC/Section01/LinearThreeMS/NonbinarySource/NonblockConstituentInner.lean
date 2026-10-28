module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.ConstituentInner
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed

/-!
# Inner offenders in the original nonblock configuration

The original 4.3.8--10 hypotheses give C_Q(K)=1. The same maximum
elementary subgroup of the actual Sylow intersection now supplies a
minimal quadratic offender whose initial image lies in the full SL₃
component. Upstairs the offender is contained in the component times
the whole-action two-core; the latter is retained, including at field four.
Its original weight, movement, injectivity and order bound are preserved.

This removes the outer-action possibility for the selected offender on
this literal consumer. It does not kill the remaining action kernel or
recognize the whole central and upper sections needed for C.1.34/MSData.
No Hypothesis1223 or additional module premise is used.
Source: Aschbacher--Smith B.1.5, K.3.2, C.1.34 and original 4.3.8--10,
printed pp.69--70,454--456,136--137,616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.ConstituentInner
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))

/-- The actual Sylow intersection supplies an offender in the component
modulo the exact whole-action two-core, with faithful full initial image. -/
theorem source_exists_component_mod_core_offender :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let J := (K c ⊔ c.I.pCoreIn 2 : Subgroup G)
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let H := J ⧸ centralizer (E : Set J)
    let q := QuotientGroup.mk' (centralizer (E : Set J))
    let B := (q.comp ((K c).subgroupOf J).subtype).range
    let rho := CentralSections.coreOmegaRepresentation hm hn
    let f := NoncoreOffenders.toInitial hm hn E (CentralSections.coreOmegaLayer_centralizer_le hm hn)
    ∃ A ∈ elementaryAbelianMaxSubgroups ((S c).subgroupOf J), ∃ X ≤ A.map q,
      IsMinimalBestOffender rho X ∧ IsQuadratic rho X ∧
      weight rho X = weight rho (A.map q) ∧ ⁅B,X⁆ = B ∧
      X ⊓ centralizer (B : Set H) = ⊥ ∧ Function.Injective (f.comp X.subtype) ∧
      X ≤ B ⊔ pCore 2 H ∧ X.map f ≤ centralOmegaComponent (K c) (c.I.pCoreIn 2) ∧
      Nat.card X ≤ 2^(2*n) ∧ rank X ≤ 2*n ∧ fixedCodim rho X ≤ 2*n := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.ConstituentInner.exists_minimal_component_mod_core_offender
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed _
    (comap_mono (c.core_sylow.le.trans inf_le_left))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.ConstituentInner
