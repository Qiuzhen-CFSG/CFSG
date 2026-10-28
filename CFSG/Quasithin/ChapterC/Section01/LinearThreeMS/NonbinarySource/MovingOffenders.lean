module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.QuadraticKernel
public import Theory.Representation.BinaryOffender.MovingReplacement

/-!
# Quadratic offenders moving the whole central-omega component

Assume C_Q(K)=1. MS3 supplies a maximum elementary subgroup A of any
specified overgroup of R, offending on both the whole central omega and
the initial action. Its nontrivial initial image cannot centralize the
initial generalized Fitting subgroup. Timmesfeld's displacement-centralizer
replacement therefore remains a best offender moving the whole covering
component, with exactly the original weight.

The component fixes no vector, so the quadratic displacement argument
makes the replacement disjoint from its centralizer. The entire kernel
of the initial projection is the two-core and centralizes that component;
hence the projection is injective on the constructed offender. Every
whole-actor invariant Irr⁺ central section consequently has an FF action.

These are existence statements at every nonbinary field, including four.
They retain the complete covering kernel and the original radical overgroup.
They do not place the constructed offender inside the component, eliminate
the covering kernel, or recognize the whole central and Frattini sections.
The companion NonblockMovingOffenders supplies C_Q(K)=1 from original
4.3.8--10 and specializes to its actual Sylow intersection.
Source: Aschbacher--Smith B.1.4--5 and C.1.34, pp.68--70,136--137;
GLS2, Theorem 26.23(i), and the component commutator dichotomy.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.MovingOffenders
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "E" => CentralSections.coreOmegaLayer (K := K) (R := R)
variable [hEN : Subgroup.Normal (CentralSections.coreOmegaLayer (K := K) (R := R))]
local instance omega_elementary : IsElementaryAbelian 2 E :=
  CentralSections.coreOmegaLayer_elementary
local notation "H" => (J ⧸ centralizer (E : Set J))
local notation "q" => (QuotientGroup.mk' (centralizer (E : Set J)) : J →* H)
local notation "B" => MonoidHom.range ((MonoidHom.comp q (Subgroup.subtype L)) : L →* H)
local notation "rho" => CentralSections.coreOmegaRepresentation h hn
local notation "f" => NoncoreOffenders.toInitial h hn E
  (CentralSections.coreOmegaLayer_centralizer_le h hn)

include h hn

/-- An actual maximum elementary subgroup of every original radical overgroup
contains, on the whole central omega, a quadratic best offender moving the
covering component and injecting into the literal initial action. -/
theorem exists_quadratic_moving_offender
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (S : Subgroup J) (hRS : R.subgroupOf J ≤ S) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, ∃ D ≤ A.map q,
      IsBestOffender rho D ∧ IsQuadratic rho D ∧
      weight rho D = weight rho (A.map q) ∧
      (¬ D ≤ centralizer (B : Set H)) ∧
      D ⊓ centralizer (B : Set H) = ⊥ ∧
      Function.Injective ((f).comp D.subtype) := by
  let := component_normal h hn
  let : (B).Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := (KernelOffenders.omegaCover h hn (Classical.choice h.model)).isQuasisimple
  let := centralOmegaComponent_normal h hn
  let := centralOmegaComponent_quasisimple h hn
  have hfit : generalizedFitting (CentralOmegaActor K R) = (B).map f := by
    rw [MonoidHom.range_comp,range_subtype,NoncoreOffenders.toInitial_component]
    exact generalizedFitting_eq_of_quasisimple_two_quotient _
      (centralOmega_outer_isTwoGroup h hn) (centralOmega_quotient_core_eq_bot h hn)
  obtain ⟨A,hA,_,hbest,_,hinit⟩ := NoncoreOffenders.coreOmega_bestOffenders h hn S hRS
  let : IsElementaryAbelian 2 (A.map q) := hbest.1.2
  have hnon : ¬ A.map q ≤ centralizer (B : Set H) := by
    apply elementary_not_centralizing_of_reduced_image B f hfit
      (centralOmega_quotient_core_eq_bot h hn) (A.map q)
    have he : (f).comp q = centralOmegaProjection K R := by
      ext j
      exact NoncoreOffenders.toInitial_apply h hn E
        (CentralSections.coreOmegaLayer_centralizer_le h hn) j
    rw [map_map,he]
    exact hinit.1.1
  let D := displacementCentralizer rho (A.map q)
  obtain ⟨hD,hquad,hm⟩ := hbest.quadratic_replacement_moving_component rho B (A.map q)
    (CentralSections.coreOmegaRepresentation_injective h hn)
    (KernelOffenders.omega_fixedSpace_eq_bot h hn hfixed) hnon
  have hdis : D ⊓ centralizer (B : Set H) = ⊥ :=
    quadratic_inf_centralizer_eq_bot_of_component rho B D
      (CentralSections.coreOmegaRepresentation_injective h hn)
      (KernelOffenders.omega_fixedSpace_eq_bot h hn hfixed) hm hquad
  refine ⟨A,hA,D,displacementCentralizer_le rho _,hD,hquad,
    (hbest.displacementCentralizer_equalWeightLE rho).2,hm,hdis,?_⟩
  have hcomp : IsComponent H B := ⟨(inferInstance : (B).Normal).isSubnormal,inferInstance⟩
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  have hcore : pCore 2 H ≤ centralizer (B : Set H) :=
    le_centralizer_iff.mp (hcomp.le_centralizer_of_solvable_normal (pCore 2 H))
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro d hd
  apply Subtype.ext
  apply hdis.le
  refine ⟨d.property,hcore ?_⟩
  rw [←NoncoreOffenders.toInitial_kernel h hn E
    (CentralSections.coreOmegaLayer_centralizer_le h hn)]
  exact hd

/-- The existence theorem supplies an FF action on every whole-actor invariant
Irr⁺ central section, without an assumed component offender. -/
theorem invariant_irrPlus_isFF
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (I : Submodule (ZMod 2) (Additive E)) (hI : IsIrrPlus rho B I)
    (hHI : (⊤ : Subgroup H) ≤ subspaceStabilizer rho I) :
    IsFFModule (imageRepresentation
      (centralSectionRepresentation rho B ⊤ I hHI (by
        let := component_normal h hn
        have hb : (B).Normal := by
          rw [MonoidHom.range_comp,range_subtype]
          exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
        exact (normalizer_eq_top_iff.mpr hb).ge))) := by
  let := component_normal h hn
  let : (B).Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := (KernelOffenders.omegaCover h hn (Classical.choice h.model)).isQuasisimple
  obtain ⟨A,_,D,_,hD,_,_,_,hdis,_⟩ :=
    exists_quadratic_moving_offender h hn hfixed (R.subgroupOf J) le_rfl
  exact centralSection_isFFModule_of_offender rho B D ⊤ hD le_top le_top
    (disjoint_iff.mpr hdis) I hI hHI (by rw [normalizer_eq_top])

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.MovingOffenders
