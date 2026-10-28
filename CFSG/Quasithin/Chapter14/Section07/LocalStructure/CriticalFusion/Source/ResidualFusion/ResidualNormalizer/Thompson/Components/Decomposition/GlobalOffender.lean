module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Decomposition.OffenderSource.Normality
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.ThreeRank
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneComparison
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product

/-!
# The global offender action in the residual-normalizer argument

The offender subgroup of the faithful action of Y/O₂(Y) on E is normal,
hence has trivial two-core. Its genuine SQTK cover is inherited from Y.
The complete B.5 theorem therefore applies to this global subgroup. Each
original component of J(Y) lies in it: local best offenders map to global
best offenders, and the component image remains normal and quasisimple.

The original three-rank bound leaves only a single quasisimple generalized
Fitting subgroup or S₃. A nontrivial perfect component excludes S₃, and its
containment in F* identifies the component with F*. Thus the full B.5 module
conclusion applies to each original component with the literal quotient
maps retained. No smaller local actor is assumed to have trivial two-core.

The remaining comparison with the earlier 14.3.4(3) module constituents is
separate; the group classification alone does not assert that comparison.
Source: Aschbacher–Smith, 14.7.67(4), printed pp.1070–1071, and B.5.1.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ResidualNormalizer
open Chapter14.Section04.LargerDimension.LocalAction.Components
open ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

def residualGlobalOffender (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    let := (d.residualSpan_reduced hs).elementary
    Subgroup (Y L F ⧸ pCore 2 (Y L F)) := by
  let := (d.residualSpan_reduced hs).elementary
  exact offenderSubgroup (d.residualRepresentation hs)

def residualGlobalAction (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    let := (d.residualSpan_reduced hs).elementary
    Representation (ZMod 2) (d.residualGlobalOffender hs)
      (Additive ((E F).subgroupOf (Y L F))) := by
  let := (d.residualSpan_reduced hs).elementary
  exact (d.residualRepresentation hs).comp (d.residualGlobalOffender hs).subtype

theorem residualGlobalOffender_twoCore (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    pCore 2 (d.residualGlobalOffender hs) = ⊥ := by
  let := (d.residualSpan_reduced hs).elementary
  let Q := d.residualGlobalOffender hs
  let : Q.Normal := offenderSubgroup_normal _
  rw [pCore_subnormal_eq_comap 2 (inferInstance : Q.Normal).isSubnormal,
    pCore_quotient_pCore_eq_bot]
  exact (MonoidHom.ker_eq_bot_iff _).mpr Q.subtype_injective

theorem residualGlobalOffender_hypothesis (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    let := (d.residualSpan_reduced hs).elementary
    FFHypothesis KnownSimple.IsKnownSimple (d.residualGlobalAction hs) := by
  let := (d.residualSpan_reduced hs).elementary
  have hY : IsSQTK KnownSimple.IsKnownSimple (Y L F) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe residual_Y_le_normalizer_K)).mp
      (d.residual_normalizer_sqtk.subgroup _)
  let cover : SQTKQuotient KnownSimple.IsKnownSimple (Y L F ⧸ pCore 2 (Y L F)) := {
    Cover := Y L F
    kernel := pCore 2 (Y L F)
    sqtk := hY
    equiv := MulEquiv.refl _ }
  refine ⟨Module.Finite.of_finite,
    (d.residualRepresentation_faithful hs).comp (d.residualGlobalOffender hs).subtype_injective,
    d.residualGlobalOffender_twoCore hs, offenderSubgroup_restrict_eq_top _,
    ⟨cover.subgroup (d.residualGlobalOffender hs)⟩⟩

theorem residualGlobalOffender_classification (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    let := (d.residualSpan_reduced hs).elementary
    AdequateAlternative (d.residualGlobalAction hs) := by
  let := (d.residualSpan_reduced hs).elementary
  exact adequateAlternative_knownSimple _ (d.residualGlobalOffender_hypothesis hs)

private theorem restricted_offender_le {X M : Type*} [Group X] [AddCommGroup M]
    [Module (ZMod 2) M] (ρ : Representation (ZMod 2) X M) (P : Subgroup X) :
    (offenderSubgroup (ρ.comp P.subtype)).map P.subtype ≤ offenderSubgroup ρ := by
  unfold offenderSubgroup generatedBy
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro A
  rw [Subgroup.map_iSup]
  apply iSup_le
  rintro ⟨hA,_⟩
  exact (hA.map_subtype ρ).le_offenderSubgroup ρ

theorem residual_component_le_globalOffender
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    let := (d.residualSpan_reduced hs).elementary
    residualOffenderComponentPlus (L := L) (F := F) B ≤ d.residualGlobalOffender hs := by
  let := (d.residualSpan_reduced hs).elementary
  have h := map_mono (f := (residualOffenderActor (L := L) (F := F) B).subtype)
    (d.residual_component_le_offender earlier hs hB)
  rw [residualOffenderComponent_map_subtype] at h
  exact h.trans (restricted_offender_le (d.residualRepresentation hs) _)

theorem residualGlobalOffender_threeRank (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    primeRank 3 (d.residualGlobalOffender hs) ≤ 1 := by
  apply (primeRank_subgroup_le 3 (d.residualGlobalOffender hs)).trans
  exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
    d.residual_Y_threeRank_le_one

def residualGlobalComponent
    (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) (B : Subgroup G) :
    let := (d.residualSpan_reduced hs).elementary
    Subgroup (d.residualGlobalOffender hs) := by
  let := (d.residualSpan_reduced hs).elementary
  exact (residualOffenderComponentPlus (L := L) (F := F) B).subgroupOf (d.residualGlobalOffender hs)

theorem residualGlobalComponent_isComponent
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    let := (d.residualSpan_reduced hs).elementary
    IsComponent (d.residualGlobalOffender hs) (d.residualGlobalComponent hs B) := by
  let := (d.residualSpan_reduced hs).elementary
  let C := residualOffenderComponent (L := L) (F := F) B
  let Cplus := residualOffenderComponentPlus (L := L) (F := F) B
  let Q := d.residualGlobalOffender hs
  have hCQ := d.residual_component_le_globalOffender earlier hs hB
  let e : d.residualGlobalComponent hs B ≃* C :=
    (subgroupOfEquivOfLe hCQ).trans
      (subgroupOfEquivOfLe (residualOffenderComponentPlus_le_actor (L := L) (F := F) (B := B))).symm
  let : IsQuasisimple C := d.residualOffenderComponent_quasisimple earlier hs hB
  have hBN := residual_component_in_normalizer hB
  have hn := (normal_subgroupOf_iff_le_normalizer hBN.1).mp
    (d.residual_component_normal_in_normalizer earlier hs hB)
  let : (B.subgroupOf (Y L F)).Normal :=
    normal_subgroupOf_of_le_normalizer (residual_Y_le_normalizer_K.trans hn)
  let q := QuotientGroup.mk' (pCore 2 (Y L F))
  let : Cplus.Normal := by
    refine ⟨?_⟩
    intro x hx y
    obtain ⟨b,hb,rfl⟩ := hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (Y L F)) y
    refine ⟨a*b*a⁻¹,(inferInstance : (B.subgroupOf (Y L F)).Normal).conj_mem b hb a,?_⟩
    simp only [map_mul,map_inv]
    rfl
  let : (d.residualGlobalComponent hs B).Normal := inferInstanceAs (Cplus.subgroupOf Q).Normal
  exact ⟨(inferInstance : (d.residualGlobalComponent hs B).Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv e.symm⟩

theorem residual_global_component_classification
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    let := (d.residualSpan_reduced hs).elementary
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion (d.residualGlobalAction hs)
      (d.residualGlobalComponent hs B)) := by
  let := (d.residualSpan_reduced hs).elementary
  let Q := d.residualGlobalOffender hs
  let C := d.residualGlobalComponent hs B
  have hC := d.residualGlobalComponent_isComponent earlier hs hB
  let : IsQuasisimple C := hC.2
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  let : Nontrivial Q := C.subtype_injective.nontrivial
  have cases := AdequateAlternative.at_three_rank_le_one
    (d.residualGlobalOffender_classification hs) (d.residualGlobalOffender_threeRank hs)
  rcases cases with hq | hs3
  · obtain ⟨hq,⟨out⟩⟩ := hq
    have he : C = generalizedFitting Q := hC.eq_of_le
      ⟨(inferInstance : (generalizedFitting Q).Normal).isSubnormal,hq⟩
      (component_le_generalizedFitting Q C hC)
    change Nonempty (ProjectiveLine.QuasisimpleSourceConclusion (d.residualGlobalAction hs) C)
    rw [he]
    exact ⟨out⟩
  · obtain ⟨out⟩ := hs3
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable Q := Group.isSolvable_of_isSolvable_injective (f := out.equiv.toMonoidHom) out.equiv.injective
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
