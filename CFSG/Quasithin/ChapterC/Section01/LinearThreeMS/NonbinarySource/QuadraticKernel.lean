module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.KernelOffenders
public import Theory.Representation.BinaryOffender.QuadraticCentralizer
public import Theory.Representation.BinaryOffender.Replacement
public import Theory.Representation.BinaryOffender.QuasisimpleCentralSection
public import Theory.Representation.SL3DoubledNaturalOffenders.TensorAllFields

/-!
# Faithful quadratic offenders in the whole central-omega component

At field four with C_Q(K)=1, an elementary component subgroup centralizing
that component lies in the full exceptional covering kernel, so it is not
an offender. A quadratic offender consequently generates the component by
commutators. The displacement lemma then makes its intersection with the
component centralizer trivial. Thus both the supplied full SL₃ marking and
the literal projection to the initial action are injective on this offender.
The original offender has order at most sixteen and fixed codimension at
most four. Thompson replacement supplies such a subgroup inside every
component offender, without decreasing its weight.

The companion NonblockQuadraticKernel supplies the fixed-factor premise
from the original4.3.8--10 configuration. These results strengthen survival
to injectivity; they do not assert that the full covering kernel is trivial
or that the whole central and Frattini sections have been recognized.
Source: Aschbacher--Smith B.1.4--5,C.1.34, pp.68--70,136--137.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.QuadraticKernel
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open KernelOffenders
universe u
variable {G : Type u} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "N" => pCore 2 (K ⊔ R : Subgroup G)
local notation "E" => CentralSections.coreOmegaLayer (K := K) (R := R)
variable [hEN : Subgroup.Normal (CentralSections.coreOmegaLayer (K := K) (R := R))]
local instance omega_elementary : IsElementaryAbelian 2 E :=
  CentralSections.coreOmegaLayer_elementary
local notation "q" => (QuotientGroup.mk' (centralizer (E : Set J)) : J →* (J ⧸ centralizer (E : Set J)))
local notation "B" => MonoidHom.range ((MonoidHom.comp q (Subgroup.subtype L)) : L →* (J ⧸ centralizer (E : Set J)))
local notation "rho" => CentralSections.coreOmegaRepresentation h hn

private theorem elementary_centralizing_le_kernel
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (A : Subgroup (J ⧸ centralizer (E : Set J))) [IsElementaryAbelian 2 A]
    (hAB : A ≤ B) (hAC : A ≤ centralizer (B : Set (J ⧸ centralizer (E : Set J)))) :
    A ≤ (omegaCover h hn e).toMonoidHom.ker.map (B).subtype := by
  let f := omegaCover h hn e
  intro a ha
  let z : B := ⟨a,hAB ha⟩
  have hz : z ∈ center B := mem_center_iff.mpr (fun b => Subtype.ext (hAC ha b b.property))
  have hfz : f.toMonoidHom z ∈ center SL(3,F) := by
    change z ∈ (center SL(3,F)).comap f.toMonoidHom
    rwa [f.comap_center]
  have htwo : f.toMonoidHom z ^ 2 = 1 := by
    rw [←map_pow, show z^2=1 from Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a ha (p := 2)),map_one]
  have hthree : f.toMonoidHom z ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp
    (((center SL(3,F)).orderOf_dvd_natCard hfz).trans (Matrix.SL3.card_center_dvd_three F))
  have he : f.toMonoidHom z = 1 := by
    calc
      _ = f.toMonoidHom z ^ 3 := by rw [pow_succ,htwo,one_mul]
      _ = 1 := hthree
  exact ⟨z,he,rfl⟩

include h hn

/-- A field-four component offender cannot centralize the covering component. -/
theorem field_four_component_offender_not_centralizing
    (hfour : Nat.card F = 4)
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (A : Subgroup (J ⧸ centralizer (E : Set J)))
    (hAB : A ≤ B) (hA : IsOffender rho A) :
    ¬ A ≤ centralizer (B : Set (J ⧸ centralizer (E : Set J))) := by
  let : IsElementaryAbelian 2 A := hA.1.2
  intro hc
  exact field_four_no_kernel_offender h hn hfour hfixed e A
    (elementary_centralizing_le_kernel h hn e A hAB hc) hA

/-- Quadratic component offenders have trivial intersection with the full
component centralizer, including the exceptional even covering kernel. -/
theorem field_four_quadratic_offender_disjoint
    (hfour : Nat.card F = 4)
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (A : Subgroup (J ⧸ centralizer (E : Set J)))
    (hAB : A ≤ B) (hA : IsOffender rho A) (hqA : IsQuadratic rho A) :
    A ⊓ centralizer (B : Set (J ⧸ centralizer (E : Set J))) = ⊥ := by
  let := component_normal h hn
  let : (B).Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := (omegaCover h hn e).isQuasisimple
  exact quadratic_inf_centralizer_eq_bot_of_component rho B A
    (CentralSections.coreOmegaRepresentation_injective h hn)
    (omega_fixedSpace_eq_bot h hn hfixed)
    (field_four_component_offender_not_centralizing h hn hfour hfixed e A hAB hA) hqA

/-- The full marked SL₃ projection is injective on each quadratic component offender. -/
theorem field_four_quadratic_offender_mark_injective
    (hfour : Nat.card F = 4)
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (A : Subgroup (J ⧸ centralizer (E : Set J)))
    (hAB : A ≤ B) (hA : IsOffender rho A) (hqA : IsQuadratic rho A) :
    Function.Injective ((omegaCover h hn e).toMonoidHom.comp (inclusion hAB)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  apply Subtype.ext
  apply (field_four_quadratic_offender_disjoint h hn hfour hfixed e A hAB hA hqA).le
  refine ⟨a.property,?_⟩
  have hz := (omegaCover h hn e).ker_le_center ha
  intro b hb
  exact congrArg (B).subtype (mem_center_iff.mp hz ⟨b,hb⟩)

/-- Quadratic component offenders inject into the literal initial action,
not just into an abstractly isomorphic linear group. -/
theorem field_four_quadratic_offender_initial_injective
    (hfour : Nat.card F = 4)
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (A : Subgroup (J ⧸ centralizer (E : Set J)))
    (hAB : A ≤ B) (hA : IsOffender rho A) (hqA : IsQuadratic rho A) :
    Function.Injective ((NoncoreOffenders.toInitial h hn E
      (CentralSections.coreOmegaLayer_centralizer_le h hn)).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have haB : a.val ∈ (L).map q := by
    simpa only [MonoidHom.range_comp,range_subtype] using hAB a.property
  obtain ⟨k,hk,hka⟩ := haB
  let kk : L := ⟨k,hk⟩
  have hzero : centralOmegaProjection K R k = 1 := by
    rw [←NoncoreOffenders.toInitial_apply h hn E
      (CentralSections.coreOmegaLayer_centralizer_le h hn),hka]
    exact ha
  have hkN : k ∈ N := (centralOmega_kernel_eq_core h hn).le
    ((QuotientGroup.eq_one_iff k).mp hzero)
  have hkL : kk ∈ pCore 2 L := by
    rw [pCore_subnormal_eq_comap 2 h.component.2.subnormal]
    exact hkN
  have hkq : QuotientGroup.mk' (pCore 2 L) kk = 1 :=
    (QuotientGroup.eq_one_iff kk).mpr hkL
  have hfzero : (omegaCover h hn e).toMonoidHom
      (((q).comp (L).subtype).rangeRestrict kk) = 1 := by
    rw [omegaCover_apply]
    change joinQuotientEquiv (R := R) e (QuotientGroup.mk' (pCore 2 L) kk) = 1
    rw [hkq,map_one]
  have hinc : inclusion hAB a = ((q).comp (L).subtype).rangeRestrict kk :=
    Subtype.ext hka.symm
  apply field_four_quadratic_offender_mark_injective h hn hfour hfixed e A hAB hA hqA
  change (omegaCover h hn e).toMonoidHom (inclusion hAB a) =
    (omegaCover h hn e).toMonoidHom (inclusion hAB 1)
  rw [hinc,hfzero,map_one,map_one]

/-- The field-four quotient bound now applies to the original offender:
its order is at most sixteen and its binary fixed codimension at most four. -/
theorem field_four_quadratic_offender_bounds
    (hfour : Nat.card F = 4)
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (A : Subgroup (J ⧸ centralizer (E : Set J)))
    (hAB : A ≤ B) (hA : IsOffender rho A) (hqA : IsQuadratic rho A) :
    Nat.card A ≤ 16 ∧ rank A ≤ 4 ∧ fixedCodim rho A ≤ 4 := by
  let : IsElementaryAbelian 2 A := hA.1.2
  let f := (omegaCover h hn e).toMonoidHom.comp (inclusion hAB)
  have hi : Function.Injective f :=
    field_four_quadratic_offender_mark_injective h hn hfour hfixed e A hAB hA hqA
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hb := SL3DoubledNaturalOffenders.AllFields.natural_elementary_card_le
    (by simpa using hfour : Nat.card F = 2^2) (by decide) f.range
  have he := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
  have hcard : Nat.card A ≤ 16 := by
    rw [he]
    simpa [hfour] using hb
  have hr : rank A ≤ 4 := (Nat.log_mono_right hcard).trans (by decide : Nat.log 2 16 ≤ 4)
  exact ⟨hcard,hr,hA.2.trans hr⟩

/-- Every component offender contains a quadratic minimal best offender
that injects into the original initial action and the supplied full SL₃. -/
theorem field_four_component_offender_replacement
    (hfour : Nat.card F = 4)
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (A : Subgroup (J ⧸ centralizer (E : Set J)))
    (hAB : A ≤ B) (hA : IsOffender rho A) :
    ∃ D ≤ A, IsMinimalBestOffender rho D ∧ IsQuadratic rho D ∧
      weight rho A ≤ weight rho D ∧ Nat.card D ≤ 16 ∧
      Function.Injective ((NoncoreOffenders.toInitial h hn E
        (CentralSections.coreOmegaLayer_centralizer_le h hn)).comp D.subtype) := by
  obtain ⟨D,hDA,hD,hqD,hw⟩ := hA.exists_quadratic_minimalBestOffender rho
  exact ⟨D,hDA,hD,hqD,hw,
    (field_four_quadratic_offender_bounds h hn hfour hfixed e D (hDA.trans hAB)
      (hD.1.isOffender rho) hqD).1,
    field_four_quadratic_offender_initial_injective h hn hfour hfixed e D (hDA.trans hAB)
      (hD.1.isOffender rho) hqD⟩


/-- Every component offender supplies an FF action on each actual invariant
Irr⁺ central section. The centralizer-disjointness premise is discharged here,
without assuming that the covering component has trivial two-core. -/
theorem field_four_component_irrPlus_isFF
    (hfour : Nat.card F = 4)
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (A : Subgroup (J ⧸ centralizer (E : Set J)))
    (hAB : A ≤ B) (hA : IsOffender rho A)
    (I : Submodule (ZMod 2) (Additive E)) (hI : IsIrrPlus rho B I) :
    IsFFModule (imageRepresentation
      (centralSectionRepresentation rho B B I hI.choose (B).le_normalizer)) := by
  obtain ⟨D,hDA,hD,hqD,_⟩ := hA.exists_quadratic_minimalBestOffender rho
  let := (omegaCover h hn e).isQuasisimple
  have hd := field_four_quadratic_offender_disjoint h hn hfour hfixed e D
    (hDA.trans hAB) (hD.1.isOffender rho) hqD
  exact centralSection_isFFModule_of_offender rho B D B hD.1 le_rfl (hDA.trans hAB)
    (disjoint_iff.mpr hd) I hI hI.choose (B).le_normalizer

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.QuadraticKernel
