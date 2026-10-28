module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralSections
public import Theory.Representation.NormalElementaryQuotient.BestOffender
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import Theory.GroupTheory.PCoreSurjective
public import Theory.Representation.BinaryOffender.QuasisimpleNoncore

/-!
# Whole-section offenders surviving the initial action

MS3 forces the elementary Thompson subgroup of every overgroup of R in
KR outside O₂(KR). Choose a maximum elementary subgroup A witnessing
this escape. On any normal elementary E ≤ O₂(KR) whose centralizer lies
in O₂(KR), the same A gives a best offender on E and on the original
Ω₁(Z(O₂(KR))). Its image on E escapes the actual action two-core.

The quotient map from the E-action to the initial action has exactly the
E-action's two-core as kernel and preserves the original component image.
When Q=[O₂(KR),K] centralizes E, that component is a perfect central
SL₃ cover. The surviving offender forces this whole covering component
into the E-action's best-offender subgroup. In particular this applies to
E=Ω₁(Z(Q)), even for nonabelian Q, and to E=Q when Q is abelian.

These statements include field four. They do not kill the exceptional
covering kernel or the whole action's normal two-subgroup. Recognition
of the entire central/Frattini sections and the Sylow radical inequalities
remain required for C.1.34. NonblockMSClassification and PointApplication
use the results on their original groups, radicals and Sylow overgroups.
Source: Aschbacher--Smith B.2.4--5 and C.1.34, pp.75--76, 136--137;
Meierfrankenfeld--Stellmacher (1993), the initial analysis in Section 3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.NoncoreOffenders
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "T" => R.subgroupOf (K ⊔ R)
local notation "N" => pCore 2 (K ⊔ R : Subgroup G)

include h hn

omit [CharP F 2] in
/-- MS3 excludes the two-core for the Thompson subgroup of every original radical overgroup. -/
theorem thompson_overgroup_not_le_core (S : Subgroup J) (hTS : T ≤ S) :
    ¬ elementaryAbelianMaxJ S ≤ N := by
  intro hs
  have ht : elementaryAbelianMaxJ S ≤ T := hs.trans (join_oddIndex h hn).twoCore_le
  have he := elementaryAbelianMaxJ_eq_of_intermediate S T ht hTS
  apply (join_characteristic h).thompson_not_le_core
    (join_oddIndex h hn).isPGroup (radical_ne_bot h hn) (join_oddIndex h hn).twoCore_le
  rwa [he]

omit [CharP F 2] in
/-- A maximum elementary subgroup of the specified overgroup escapes the original two-core. -/
theorem exists_maximum_outside_core (S : Subgroup J) (hTS : T ≤ S) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, ¬ A ≤ N := by
  by_contra! he
  exact thompson_overgroup_not_le_core h hn S hTS (sSup_le he)

variable (E : Subgroup (K ⊔ R : Subgroup G)) [E.Normal] [IsElementaryAbelian 2 E]
local notation "q" => QuotientGroup.mk' (centralizer (E : Set J))
local notation "rho" => NormalElementaryQuotient.representation E q
  (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

include h hn in
/-- The same maximum elementary subgroup is best on the whole section and the initial layer; its whole-section image escapes the actual two-core. -/
theorem simultaneous_bestOffenders (hEN : E ≤ N)
    (hCE : centralizer (E : Set J) ≤ N) (S : Subgroup J) (hTS : T ≤ S) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S,
      (¬ A ≤ N) ∧ IsBestOffender rho (A.map q) ∧
      (¬ A.map q ≤ pCore 2 (J ⧸ centralizer (E : Set J))) ∧
      IsBestOffender (centralOmegaRepresentation K R) (A.map (centralOmegaProjection K R)) := by
  obtain ⟨A,hA,hAN⟩ := exists_maximum_outside_core h hn S hTS
  have hNS : N ≤ S := (join_oddIndex h hn).twoCore_le.trans hTS
  have hqker : IsPGroup 2 (q).ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.of_injective (inclusion hCE) (inclusion_injective hCE)
  refine ⟨A,hA,hAN,?_,?_,?_⟩
  · apply NormalElementaryQuotient.maxElementary_isBestOffender E q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) S A (hEN.trans hNS) hA
    intro hz
    have hc := (map_eq_bot_iff A).mp hz
    rw [QuotientGroup.ker_mk'] at hc
    exact hAN (hc.trans hCE)
  · intro hc
    apply hAN
    have he := map_le_iff_le_comap.mp hc
    rwa [(q).comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hqker] at he
  · unfold centralOmegaRepresentation
    apply NormalElementaryQuotient.maxElementary_isBestOffender _ _
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) S A
      ((map_subtype_le _).trans hNS) hA
    intro hz
    have hc := (map_eq_bot_iff A).mp hz
    rw [QuotientGroup.ker_mk'] at hc
    change A ≤ centralOmegaKernel K R at hc
    exact hAN (hc.trans_eq (centralOmega_kernel_eq_core h hn))

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.NoncoreOffenders



namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.NoncoreOffenders
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "T" => R.subgroupOf (K ⊔ R)
local notation "N" => pCore 2 (K ⊔ R : Subgroup G)
variable (E : Subgroup (K ⊔ R : Subgroup G)) [E.Normal] [IsElementaryAbelian 2 E]
local notation "q" => QuotientGroup.mk' (centralizer (E : Set J))
local notation "rho" => NormalElementaryQuotient.representation E q
  (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
variable (hCE : centralizer (E : Set (K ⊔ R : Subgroup G)) ≤ pCore 2 (K ⊔ R : Subgroup G))

/-- The literal whole-section action projects onto the already classified initial action. -/
def toInitial : (J ⧸ centralizer (E : Set J)) →* CentralOmegaActor K R :=
  QuotientGroup.lift _ (centralOmegaProjection K R) (by
    change centralizer (E : Set J) ≤ (QuotientGroup.mk' (centralOmegaKernel K R)).ker
    rw [QuotientGroup.ker_mk',centralOmega_kernel_eq_core h hn]
    exact hCE)

omit [IsElementaryAbelian 2 E] in
/-- The comparison retains every original group representative. -/
theorem toInitial_apply (j : J) :
    toInitial h hn E hCE (q j) = centralOmegaProjection K R j := by
  unfold toInitial
  rfl

omit [IsElementaryAbelian 2 E] in
/-- Every element of the initial actor lifts to the whole-section actor. -/
theorem toInitial_surjective : Function.Surjective (toInitial h hn E hCE) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (QuotientGroup.mk'_surjective _) _

omit [IsElementaryAbelian 2 E] in
/-- The comparison sends the original component image onto the initial component image. -/
theorem toInitial_component : ((L).map q).map (toInitial h hn E hCE) = centralOmegaComponent K R := by
  rw [map_map]
  rfl

omit [IsElementaryAbelian 2 E] in
/-- The kernel of comparison is exactly the whole-section actor's two-core. -/
theorem toInitial_kernel : (toInitial h hn E hCE).ker = pCore 2 (J ⧸ centralizer (E : Set J)) := by
  apply comap_injective (QuotientGroup.mk'_surjective (centralizer (E : Set J)))
  have he : (toInitial h hn E hCE).ker.comap q = N := by
    change (QuotientGroup.mk' (centralOmegaKernel K R)).ker = N
    rw [QuotientGroup.ker_mk']
    exact centralOmega_kernel_eq_core h hn
  rw [he]
  symm
  apply (q).comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _)
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup.of_injective (inclusion hCE) (inclusion_injective hCE)

include h hn hCE

omit hn [CharP F 2] [IsElementaryAbelian 2 E] in
/-- A section centralized by Q retains a quasisimple covering component, also at field four. -/
theorem section_component_quasisimple (hQE : ⁅N,L⁆ ≤ centralizer (E : Set J)) :
    IsQuasisimple ((L).map q) := by
  let := h.component.2.perfect
  let : IsQuasisimple SL(3,F) := {
    toIsPerfect := Atlas.sl_perfect 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }
  let c := Matrix.SL3.CommutatorCentralCover.cover L N
    (joinQuotientEquiv (R := R) (Classical.choice h.model)) q
    (pCore_subnormal_eq_comap 2 h.component.2.subnormal).symm
    (by rwa [QuotientGroup.ker_mk']) (by rwa [QuotientGroup.ker_mk'])
  have hc := c.isQuasisimple
  rwa [MonoidHom.range_comp,range_subtype] at hc

/-- The entire covering component lies in the whole-section best-offender subgroup. -/
theorem section_component_le_offenders (hEN : E ≤ N)
    (hQE : ⁅N,L⁆ ≤ centralizer (E : Set J)) :
    (L).map q ≤ offenderSubgroup rho := by
  let := component_normal h hn
  let : ((L).map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := section_component_quasisimple h E hCE hQE
  let := centralOmegaComponent_normal h hn
  let := centralOmegaComponent_quasisimple h hn
  have hfit : generalizedFitting (CentralOmegaActor K R) = ((L).map q).map (toInitial h hn E hCE) := by
    rw [toInitial_component]
    exact generalizedFitting_eq_of_quasisimple_two_quotient _
      (centralOmega_outer_isTwoGroup h hn) (centralOmega_quotient_core_eq_bot h hn)
  obtain ⟨A,hA,hAN,hAE,hAP,hAI⟩ := simultaneous_bestOffenders h hn E hEN hCE T le_rfl
  apply component_le_offenderSubgroup_of_reduced_image rho ((L).map q)
    (toInitial h hn E hCE) (toInitial_surjective h hn E hCE) hfit
    (centralOmega_quotient_core_eq_bot h hn) (A.map q) hAE
  rw [map_map]
  exact hAI.1.1
end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.NoncoreOffenders


namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.NoncoreOffenders
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "T" => R.subgroupOf (K ⊔ R)
local notation "N" => pCore 2 (K ⊔ R : Subgroup G)
local notation "Q" => (⁅pCore 2 (K ⊔ R : Subgroup G),K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G))
local notation "E" => CentralSections.coreOmegaLayer (K := K) (R := R)

omit [Finite G] in
private theorem core_centralizes_coreOmega : Q ≤ centralizer (E : Set J) := by
  intro x hx z hz
  apply Subtype.ext
  have hx' : (x : G) ∈ msQ K R :=
    (commutator_map_eq_msQ (K := K) (R := R)) ▸ mem_map_of_mem (J).subtype hx
  have hz' : (z : G) ∈ SourceInterface.omegaCenterIn (msQ K R) := by
    change z ∈ E at hz
    rw [CentralSections.coreOmegaLayer_eq] at hz
    exact hz
  exact (((mem_omegaCenterIn_iff (msQ K R) (z : G)).mp hz').2.1 (x : G) hx').symm

include h hn

/-- The actual central omega of Q and the initial layer share a maximum elementary best offender escaping both two-cores. -/
theorem coreOmega_bestOffenders (S : Subgroup J) (hTS : T ≤ S) :
    letI := CentralSections.coreOmegaLayer_normal h hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K) (R := R)
    ∃ A ∈ elementaryAbelianMaxSubgroups S,
      (¬ A ≤ N) ∧
      IsBestOffender (CentralSections.coreOmegaRepresentation h hn)
        (A.map (QuotientGroup.mk' (centralizer (E : Set J)))) ∧
      (¬ A.map (QuotientGroup.mk' (centralizer (E : Set J))) ≤
        pCore 2 (J ⧸ centralizer (E : Set J))) ∧
      IsBestOffender (centralOmegaRepresentation K R) (A.map (centralOmegaProjection K R)) := by
  let := CentralSections.coreOmegaLayer_normal h hn
  let := CentralSections.coreOmegaLayer_elementary (K := K) (R := R)
  rw [CentralSections.coreOmegaRepresentation_eq]
  exact simultaneous_bestOffenders h hn E (CentralSections.coreOmegaLayer_le_core (K := K) (R := R))
    (CentralSections.coreOmegaLayer_centralizer_le h hn) S hTS

/-- Even for nonabelian Q, its entire central-omega offender group contains the original covering component. -/
theorem coreOmega_component_le_offenders :
    letI := CentralSections.coreOmegaLayer_normal h hn
    letI := CentralSections.coreOmegaLayer_elementary (K := K) (R := R)
    (L).map (QuotientGroup.mk' (centralizer (E : Set J))) ≤
      offenderSubgroup (CentralSections.coreOmegaRepresentation h hn) := by
  let := CentralSections.coreOmegaLayer_normal h hn
  let := CentralSections.coreOmegaLayer_elementary (K := K) (R := R)
  rw [CentralSections.coreOmegaRepresentation_eq]
  exact section_component_le_offenders h hn E
    (CentralSections.coreOmegaLayer_centralizer_le h hn) (CentralSections.coreOmegaLayer_le_core (K := K) (R := R)) core_centralizes_coreOmega

/-- An abelian whole core has a maximum elementary best offender with nontrivial initial image, also at field four. -/
theorem abelian_core_bestOffenders (hc : IsMulCommutative (msQ K R))
    (S : Subgroup J) (hTS : T ≤ S) :
    letI := component_normal h hn
    letI := abelian_joinCore_elementary h hn hc
    ∃ A ∈ elementaryAbelianMaxSubgroups S,
      (¬ A ≤ N) ∧ IsBestOffender (wholeCoreRepresentation h hn hc)
        (A.map (QuotientGroup.mk' (centralizer (Q : Set J)))) ∧
      (¬ A.map (QuotientGroup.mk' (centralizer (Q : Set J))) ≤
        pCore 2 (J ⧸ centralizer (Q : Set J))) ∧
      IsBestOffender (centralOmegaRepresentation K R) (A.map (centralOmegaProjection K R)) := by
  let := component_normal h hn
  let := abelian_joinCore_elementary h hn hc
  rw [wholeCoreRepresentation_eq]
  exact simultaneous_bestOffenders h hn Q (commutator_le_left _ _)
    (wholeCore_join_centralizer_le h hn) S hTS

/-- The abelian whole-core offender group contains the entire original covering component at every nonbinary field. -/
theorem abelian_core_component_le_offenders (hc : IsMulCommutative (msQ K R)) :
    letI := component_normal h hn
    letI := abelian_joinCore_elementary h hn hc
    (L).map (QuotientGroup.mk' (centralizer (Q : Set J))) ≤
      offenderSubgroup (wholeCoreRepresentation h hn hc) := by
  let := component_normal h hn
  let := abelian_joinCore_elementary h hn hc
  rw [wholeCoreRepresentation_eq]
  exact section_component_le_offenders h hn Q (wholeCore_join_centralizer_le h hn)
    (commutator_le_left _ _) (le_centralizer_iff_isMulCommutative.mpr inferInstance)
end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.NoncoreOffenders
