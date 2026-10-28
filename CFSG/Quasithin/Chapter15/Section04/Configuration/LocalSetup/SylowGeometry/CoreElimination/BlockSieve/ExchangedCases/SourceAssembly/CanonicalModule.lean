module
public import CFSG.Quasithin.ChapterC.Section02.CanonicalModule
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.RankOneGeometry

/-!
# The canonical module in the actual rank-one source branch

The constructed Sylow subgroup and characteristic-normalizer control force
the canonical Sylow-center span into the original omega-core module, with
identical centralizer kernel. The same local group has characteristic two
and its original perfect component is its two-residual. These are the
literal geometric inputs of the canonical-module block-recognition theorem.
The original B.5 moved-section comparison remains a separate action step.
Source: Aschbacher–Smith C.2.7(3)(a), pp.146–147; 15.4.20, p.1164.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
open SL3Geometry.SourceCases ChapterB.QuasisimpleSource
universe u
private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (A ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (A ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ N) inferInstance

variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}


theorem source_canonical_module_kernel
    (h : Input d i j H U K) (L : Subgroup H)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) L)
    (hr : IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (L ⊔ (sourceRadical d U).subgroupOf H)))
    [IsSimpleGroup (starComponent L ((sourceRadical d U).subgroupOf H))]
    [Group.IsPerfect (starComponent L ((sourceRadical d U).subgroupOf H))]
    (P : Sylow 2 (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H))
    (hP : (P : Subgroup _) = ((sourceRadical d U).subgroupOf H).subgroupOf
      (L ⊔ (sourceRadical d U).subgroupOf H)) :
    let D := L ⊔ (sourceRadical d U).subgroupOf H
    let W := normalClosure (omegaOneCenterAmbient (P : Subgroup D) : Set D)
    W ≤ omegaCoreModule D ∧ centralizer (W : Set D) = pCore 2 D := by
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  let C := starComponent L R
  let M := d.M₁.subgroupOf H
  have hk : starKernel L R = pCore 2 D :=
    (h.local_module_comparison L hc.normalized hr).2.2.2.2
  have hcontrol : (R.subgroupOf D).characteristicNormalizerClosure ≤ M.subgroupOf D :=
    characteristicNormalizerClosure_subgroupOf_le le_sup_right hc.characteristic_control
  have hout : ¬ L.subgroupOf D ≤ M.subgroupOf D := by
    intro he
    apply hc.outside
    intro l hl
    exact he (show (⟨l,(show L ≤ D from le_sup_left) hl⟩ : D) ∈ L.subgroupOf D from hl)
  let : (L.subgroupOf D).Normal := hc.local_normal
  let : C.Normal := (inferInstance : (L.subgroupOf D).Normal).map
    (starProjection L R) (QuotientGroup.mk'_surjective _)
  have hgen : C ⊔ starRadical L R = ⊤ := by
    change (L.subgroupOf D).map (starProjection L R) ⊔
      (R.subgroupOf D).map (starProjection L R) = ⊤
    rw [← Subgroup.map_sup, ← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hquot : IsPGroup 2 (Star L R ⧸ C) :=
    isPGroup_quotient_of_sup_eq_top C (starRadical L R)
      (hr.isPGroup.map (starProjection L R)) hgen
  have hco := source_component_core_offenders_of_local_radical h L KnownSimple.IsKnownSimple hc hr
  have hC : centralizer (C : Set (Star L R)) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient C (Group.IsPerfect.not_isMulCommutative C)
      hquot hco.1.2.2.2
  have hne : (P : Subgroup D) ≠ ⊥ := hP ▸ hr.1
  have hpcontrol : (P : Subgroup D).characteristicNormalizerClosure ≤ M.subgroupOf D :=
    hP ▸ hcontrol
  refine ⟨ChapterC.canonical_span_le_omega_of_kernel P hk, ?_⟩
  exact ChapterC.canonical_span_kernel_of_simple_component P hne hk
    (M.subgroupOf D) (L.subgroupOf D) hpcontrol hout
    (starProjection L R) (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans hk) C rfl hC

/-- The original selected rank-one row supplies the canonical module,
characteristic two and the same perfect residual, with no new local geometry. -/
theorem source_selected_rankOne_canonicalModule
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H))
    (F : BinaryField)
    (e : starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H) ≃* SL(2,F.Carrier))
    (S : Sylow 2 (starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)))
    (hS : (S : Subgroup _).map
      (starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subtype =
      starThompson (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)) :
    let L := K₁.subgroupOf H
    let R := (sourceRadical d U).subgroupOf H
    let D := L ⊔ R
    ∃ P : Sylow 2 D, (P : Subgroup D) = R.subgroupOf D ∧
      ChapterB.IsMinimalParabolicOver P ⊤ ∧
      (let W := normalClosure (omegaOneCenterAmbient (P : Subgroup D) : Set D)
       W ≤ omegaCoreModule D ∧ centralizer (W : Set D) = pCore 2 D) ∧
      generalizedFitting D = pCore 2 D ∧ pResidual 2 D = L.subgroupOf D := by
  let L := K₁.subgroupOf H
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  have hr := source_local_radical h s hc.normalized
  let eq := SL3Geometry.source_componentStarEquiv h s hc.normalized hr
  let := hc.quasisimple
  let : IsQuasisimple (K₁ ⧸ pCore 2 K₁) :=
    IsQuasisimple.of_mulEquiv s.internalQuotientEquiv.symm
  let : IsSimpleGroup (K₁ ⧸ pCore 2 K₁) :=
    EmbeddingReduction.swapped_model_simple inferInstance s.model
  let : IsQuasisimple (starComponent L R) := IsQuasisimple.of_mulEquiv eq
  let : IsSimpleGroup (starComponent L R) := eq.symm.isSimpleGroup
  obtain ⟨P,hP,hmin⟩ := source_rankOne_minimalParabolic h s hc F e S hS
  refine ⟨P,hP,hmin,source_canonical_module_kernel h L hc hr P hP,?_,?_⟩
  · have hk : starKernel L R = pCore 2 D :=
      (h.local_module_comparison L hc.normalized hr).2.2.2.2
    exact generalizedFitting_eq_pCore_of_selfCentralizing 2
      ((centralizer_le (show omegaCoreModule D ≤ pCore 2 D from
        fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)).trans hk.le)
  · let : (L.subgroupOf D).Normal := hc.local_normal
    let : Group.IsPerfect (L.subgroupOf D) := (hc.component.subgroupOf le_sup_left).perfect
    apply pResidual_eq_of_isPPerfect_sup (L.subgroupOf D) (R.subgroupOf D)
      perfect_twoPerfect hr.isPGroup
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
