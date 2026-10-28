module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.MovingOffenders
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed

/-!
# Existing moving offenders in the original nonblock configuration

Original 4.3.8--10 supplies C_Q(K)=1 in both initial module branches.
The maximum elementary subgroup is chosen in the restriction of the actual
source Sylow S=T intersect H to KR. Its whole central-omega image contains
a quadratic best offender of the same weight that moves the covering
component, has trivial intersection with its centralizer, and injects into
the literal initial action. No offender-existence hypothesis is assumed.

Every whole-actor invariant Irr⁺ central section therefore inherits an FF
action. These results include field four, retain the entire covering kernel,
and use the original c, chosen module, constrained hypothesis, field size
and full quotient marking. They do not establish containment of the
constructed offender in the component, triviality of the covering kernel,
or the remaining whole-section models of C.1.34.
Source: Aschbacher--Smith C.1.34 and original 4.3.8--10,
printed pp.136--137,616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.MovingOffenders
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))

/-- The actual source Sylow intersection supplies a quadratic best offender
moving the whole covering component, faithful on the literal initial action. -/
theorem source_exists_quadratic_moving_offender :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let J := (K c ⊔ c.I.pCoreIn 2 : Subgroup G)
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let H := J ⧸ centralizer (E : Set J)
    let q := QuotientGroup.mk' (centralizer (E : Set J))
    let B := (q.comp ((K c).subgroupOf J).subtype).range
    let rho := CentralSections.coreOmegaRepresentation hm hn
    ∃ A ∈ elementaryAbelianMaxSubgroups ((S c).subgroupOf J), ∃ X ≤ A.map q,
      IsBestOffender rho X ∧ IsQuadratic rho X ∧
      weight rho X = weight rho (A.map q) ∧
      (¬ X ≤ centralizer (B : Set H)) ∧
      X ⊓ centralizer (B : Set H) = ⊥ ∧
      Function.Injective ((NoncoreOffenders.toInitial hm hn E
        (CentralSections.coreOmegaLayer_centralizer_le hm hn)).comp X.subtype) := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.MovingOffenders.exists_quadratic_moving_offender
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed _
    (comap_mono (c.core_sylow.le.trans inf_le_left))

/-- Every whole-actor invariant Irr⁺ central section in the original
configuration has an FF action; no offender-existence premise is left. -/
theorem source_invariant_irrPlus_isFF :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let J := (K c ⊔ c.I.pCoreIn 2 : Subgroup G)
    let E := CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := CentralSections.coreOmegaLayer_normal hm hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let H := J ⧸ centralizer (E : Set J)
    let q := QuotientGroup.mk' (centralizer (E : Set J))
    let B := (q.comp ((K c).subgroupOf J).subtype).range
    let rho := CentralSections.coreOmegaRepresentation hm hn
    ∀ (I : Submodule (ZMod 2) (Additive E)) (_hI : IsIrrPlus rho B I)
      (hHI : (⊤ : Subgroup H) ≤ subspaceStabilizer rho I),
      IsFFModule (imageRepresentation
        (centralSectionRepresentation rho B ⊤ I hHI (by
          let := component_normal hm hn
          have hb : B.Normal := by
            dsimp only [B]
            rw [MonoidHom.range_comp,range_subtype]
            exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
          exact (normalizer_eq_top_iff.mpr hb).ge))) := by
  let := CentralSections.coreOmegaLayer_normal
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using
      (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.MovingOffenders.invariant_irrPlus_isFF
    (msPair_of_quotient c D hf n (by omega) hF e) hn hfixed

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.MovingOffenders
