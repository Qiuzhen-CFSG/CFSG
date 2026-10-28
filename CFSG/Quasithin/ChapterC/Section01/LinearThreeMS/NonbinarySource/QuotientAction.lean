module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.InitialAction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleKernel
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.Quasithin.NormalTwoQuotient

/-!
# The faithful central-omega action of a nonbinary MS-pair

Form the literal action of KR on Ω₁(Z(O₂(KR))) through its centralizer
quotient. The surviving component is quasisimple, the actor has trivial
two-core, and the quotient by that component is a two-group. Theorem A
transfers the SQTK bound to the semisimple component section. The genuine
FF action then satisfies the complete B.5.1 conclusion on its offender
subgroup.

The original component core quotient maps onto this action component.
Its projective marking is compatible with the original projection; no
identification of the full centralizer kernel is assumed here.
Source: Aschbacher--Smith B.5.1, C.1.31--34, printed pp.135--137;
MS93, the initial module analysis in Sections 2--3.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open MSCentralOrbit ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "T" => R.subgroupOf (K ⊔ R)

abbrev centralOmegaLayer (K R : Subgroup G) := Subgroup.omegaCenterIn (pCore 2 (K ⊔ R : Subgroup G))
abbrev centralOmegaKernel (K R : Subgroup G) := centralizer (centralOmegaLayer K R : Set (K ⊔ R : Subgroup G))
abbrev CentralOmegaActor (K R : Subgroup G) := (K ⊔ R : Subgroup G) ⧸ centralOmegaKernel K R
abbrev centralOmegaProjection (K R : Subgroup G) : (K ⊔ R : Subgroup G) →* CentralOmegaActor K R :=
  QuotientGroup.mk' _
abbrev centralOmegaComponent (K R : Subgroup G) : Subgroup (CentralOmegaActor K R) :=
  (K.subgroupOf (K ⊔ R)).map (centralOmegaProjection K R)
def centralOmegaRepresentation (K R : Subgroup G) :
    Representation (ZMod 2) (CentralOmegaActor K R) (Additive (centralOmegaLayer K R)) :=
  NormalElementaryQuotient.representation (centralOmegaLayer K R) (centralOmegaProjection K R)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

omit h hn [Finite G] [Finite F] in
theorem core_le_centralOmegaKernel : pCore 2 J ≤ centralOmegaKernel K R := by
  intro z hz w hw
  exact (((mem_omegaCenterIn_iff _ _).mp hw).2.1 z hz).symm

include h hn

theorem component_not_le_centralOmegaKernel : ¬ L ≤ centralOmegaKernel K R := by
  intro hc
  apply component_not_centralizes_omegaOrbit L T (join_oddIndex h hn).isPGroup
    (radical_ne_bot h hn) (join_product h hn) (join_characteristic h)
  exact hc.trans (centralizer_le (omegaOrbit_le_centralOmega T
    (join_oddIndex h hn).twoCore_le (core_selfCentralizing h)))

theorem centralOmega_quotient_core_eq_bot : pCore 2 (CentralOmegaActor K R) = ⊥ := by
  let := component_normal h hn
  let := join_quotient_quasisimple h
  exact (QuasisimpleKernel.normal_kernel_structure L T (centralOmegaKernel K R)
    h.component.2 (join_oddIndex h hn).isPGroup
    (by rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])
    core_le_centralOmegaKernel (component_not_le_centralOmegaKernel h hn)).2

theorem centralOmegaComponent_ne_bot : centralOmegaComponent K R ≠ ⊥ := by
  intro hz
  apply component_not_le_centralOmegaKernel h hn
  simpa only [centralOmegaComponent,centralOmegaProjection,Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk'] using hz

theorem centralOmegaComponent_quasisimple : IsQuasisimple (centralOmegaComponent K R) := by
  apply (h.component.2.isComponent_map_of_twoCore_killed (join_quotient_quasisimple h)
    (centralOmegaProjection K R) (QuotientGroup.mk'_surjective _) _
    (centralOmegaComponent_ne_bot h hn)).2
  rw [centralOmegaProjection,QuotientGroup.ker_mk']
  exact (pCoreIn_le_of_subnormal 2 h.component.2.subnormal).trans core_le_centralOmegaKernel

theorem centralOmegaComponent_normal : (centralOmegaComponent K R).Normal := by
  let := component_normal h hn
  exact Normal.map inferInstance (centralOmegaProjection K R) (QuotientGroup.mk'_surjective _)

theorem centralOmega_outer_isTwoGroup :
    letI := centralOmegaComponent_normal h hn
    IsPGroup 2 (CentralOmegaActor K R ⧸ centralOmegaComponent K R) := by
  let := centralOmegaComponent_normal h hn
  apply isPGroup_quotient_of_sup_eq_top (centralOmegaComponent K R)
    ((T).map (centralOmegaProjection K R)) ((join_oddIndex h hn).isPGroup.map _)
  rw [centralOmegaComponent,← Subgroup.map_sup,
    ← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem centralOmegaComponent_sqtk : IsSQTK KnownSimple.IsKnownSimple (centralOmegaComponent K R) := by
  let := centralOmegaComponent_quasisimple h hn
  have hs : ChapterA.Section02.IsSemisimple (centralOmegaComponent K R) := by
    apply top_unique
    apply le_sSup
    exact ⟨(inferInstance : (⊤ : Subgroup (centralOmegaComponent K R)).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  let f := (centralOmegaProjection K R).subgroupMap L
  have hk := h.sqtk.subgroup L
  exact ⟨ChapterA.Section02.TheoremA.stronglyQuasithin_section
    ChapterA.Section02.theoremA_knownSimple hk.stronglyQuasithin hk.isKGroup
    (ChapterA.Section02.IsSectionOf.of_surjective f ((centralOmegaProjection K R).subgroupMap_surjective L)) hs,
    hk.isKGroup.of_surjective f ((centralOmegaProjection K R).subgroupMap_surjective L)⟩

theorem centralOmega_source_conclusion :
    centralOmegaComponent K R ≤ offenderSubgroup (centralOmegaRepresentation K R) ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((centralOmegaRepresentation K R).comp (offenderSubgroup (centralOmegaRepresentation K R)).subtype)
      ((centralOmegaComponent K R).subgroupOf (offenderSubgroup (centralOmegaRepresentation K R)))) := by
  let := centralOmegaComponent_normal h hn
  let := centralOmegaComponent_quasisimple h hn
  exact ChapterB.QuasisimpleSource.SourceCompletion.ff_quasisimple_source_conclusion
    (centralOmegaRepresentation K R) (centralOmegaComponent K R)
    (centralOmega_outer_isTwoGroup h hn) (centralOmega_quotient_core_eq_bot h hn)
    (centralOmegaComponent_sqtk h hn)
    (NormalElementaryQuotient.representation_injective _ _ _ _) (centralOmega_isFF h hn)

omit hn in
theorem centralOmegaCoreMap_kernel :
    pCore 2 L ≤ ((centralOmegaProjection K R).subgroupMap L).ker := by
  rw [ker_subgroupMap,centralOmegaProjection,QuotientGroup.ker_mk']
  intro k hk
  exact core_le_centralOmegaKernel
    (pCoreIn_le_of_subnormal 2 h.component.2.subnormal (mem_map_of_mem (L).subtype hk))

def centralOmegaCoreMap : (L ⧸ pCore 2 L) →* centralOmegaComponent K R :=
  QuotientGroup.lift _ ((centralOmegaProjection K R).subgroupMap L)
    (centralOmegaCoreMap_kernel h)

omit hn in
theorem centralOmegaCoreMap_surjective : Function.Surjective (centralOmegaCoreMap h) :=
  QuotientGroup.lift_surjective_of_surjective _ _
    ((centralOmegaProjection K R).subgroupMap_surjective L) _

omit hn in
theorem centralOmegaCoreMap_mk (k : L) :
    centralOmegaCoreMap h (QuotientGroup.mk' _ k) =
      (centralOmegaProjection K R).subgroupMap L k := rfl

def centralOmegaProjectiveEquiv
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    centralOmegaComponent K R ⧸ center (centralOmegaComponent K R) ≃* PSL(3,F) := by
  let := join_quotient_quasisimple h
  let := centralOmegaComponent_quasisimple h hn
  let : IsSimpleGroup (centralOmegaComponent K R ⧸ center (centralOmegaComponent K R)) :=
    IsQuasisimple.simple
  let : Nontrivial (centralOmegaComponent K R) :=
    (QuotientGroup.mk'_surjective (center (centralOmegaComponent K R))).nontrivial
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Nontrivial SL(3,F) := (Matrix.PSL3.projection_surjective F).nontrivial
  exact (IsQuasisimple.centralQuotientEquiv (centralOmegaCoreMap h)
    (centralOmegaCoreMap_surjective h)).symm.trans
    (IsQuasisimple.centralQuotientEquiv (joinQuotientEquiv (R := R) e).toMonoidHom
      (joinQuotientEquiv (R := R) e).surjective)

theorem centralOmegaProjectiveEquiv_mk
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (k : L) :
    centralOmegaProjectiveEquiv h hn e
      (QuotientGroup.mk' _ ((centralOmegaProjection K R).subgroupMap L k)) =
      Matrix.PSL3.projection F (e (QuotientGroup.mk' _ ⟨k,k.property⟩)) := by
  let := join_quotient_quasisimple h
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Nontrivial SL(3,F) := (Matrix.PSL3.projection_surjective F).nontrivial
  let : Nontrivial (centralOmegaComponent K R) := (nontrivial_iff_ne_bot _).mpr (centralOmegaComponent_ne_bot h hn)
  change centralOmegaProjectiveEquiv h hn e
    (QuotientGroup.mk' _ (centralOmegaCoreMap h (QuotientGroup.mk' _ k))) = _
  unfold centralOmegaProjectiveEquiv
  rw [MulEquiv.trans_apply,← IsQuasisimple.centralQuotientEquiv_mk
    (centralOmegaCoreMap h) (centralOmegaCoreMap_surjective h) (QuotientGroup.mk' _ k),
    MulEquiv.symm_apply_apply]
  exact IsQuasisimple.centralQuotientEquiv_mk (joinQuotientEquiv (R := R) e).toMonoidHom
    (joinQuotientEquiv (R := R) e).surjective (QuotientGroup.mk' _ k)


theorem centralOmega_actor_sqtk : IsSQTK KnownSimple.IsKnownSimple (CentralOmegaActor K R) := by
  let := centralOmegaComponent_normal h hn
  refine ⟨?_,h.sqtk.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_le_of_normal_two_quotient (centralOmegaComponent K R)
    (centralOmega_outer_isTwoGroup h hn) p ho).trans
      ((centralOmegaComponent_sqtk h hn).stronglyQuasithin p hp ho)

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
