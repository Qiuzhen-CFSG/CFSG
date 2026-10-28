module

public import Theory.GroupTheory.CommutativeComplementProjection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.Intrinsic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Numerical.SourceCenterBound.DistanceFour.Geometry

/-!
# A natural center section from the actual binary distance-four source

The source radius geometry puts the entire commutator-core center in Z_alpha.
The proved decomposition of Z_alpha into its natural moving factor and its
component-fixed factor gives a conjugation-equivariant projection. Pulling
this map back through the original component inclusion constructs a normal
intrinsic layer containing all of Z(blockU), with component-central kernel.

The final constructor discharges CommonFacts and every early/radius premise
from the original nonabelian MS input. Only the actual critical-distance
branch b=4 is retained; no exact dual-quotient classification is assumed.

Source: MS93 (4.1), (4.6.1)–(4.6.12), pp.881–882,901–912;
Aschbacher–Smith C.1.34, printed pp.136–137.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS

structure NaturalCenterSection (A : Type*) [Group A] where
  marking : (A ⧸ pCore 2 A) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  layer : Subgroup A
  normal : layer.Normal
  center_le : (center (blockU A)).map (blockU A).subtype ≤ layer
  projection : layer →* Multiplicative (Fin 3 → ZMod 2)
  action : ∀ (a : A) (x : layer),
    (projection ⟨a * (x : A) * a⁻¹,normal.conj_mem x x.property a⟩).toAdd =
      Representation.specialLinearNatural 3 (marking (QuotientGroup.mk' _ a))
        (projection x).toAdd
  kernel_central : ∀ x : layer, projection x = 1 → (x : A) ∈ center A

namespace MS93.InputSetup
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
  {h : Input κ L R} (s : InputSetup h)

noncomputable def componentEmbedding : L →* FreeAmalgam s.reduction.radical :=
  (embedM s.reduction.radical).comp (inclusion (show L ≤ s.reduction.overgroup from le_sup_left))

theorem componentEmbedding_injective : Function.Injective s.componentEmbedding :=
  (embedM_injective _).comp (inclusion_injective _)

theorem componentEmbedding_mem_local (l : L) :
    s.componentEmbedding l ∈ stabilizer s.reduction.radical (alpha s.reduction.radical) := by
  rw [alpha,stabilizer_m_base]
  exact ⟨inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l,rfl⟩

theorem componentEmbedding_mem_residual (l : L) :
    s.componentEmbedding l ∈ Ltilde s.reduction.radical (alpha s.reduction.radical) := by
  rw [s.Ltilde_embedded]
  exact mem_map_of_mem _ l.property

theorem intrinsic_core_image : (blockU L).map s.componentEmbedding =
    core s.reduction.radical (alpha s.reduction.radical) := by
  let i := inclusion (show L ≤ s.reduction.overgroup from le_sup_left)
  have he : (blockU L).map i =
      ⁅pCore 2 s.reduction.overgroup,L.subgroupOf s.reduction.overgroup⁆ := by
    apply map_injective s.reduction.overgroup.subtype_injective
    rw [map_map,s.reduction.commutatorCore_eq h]
    exact h.commutatorCore_eq_internal.symm
  change (blockU L).map ((embedM s.reduction.radical).comp i) = _
  rw [← map_map,he,core_alpha _ s.source.two_group s.source.core_le s.source.residual]

noncomputable def intrinsicCoreEquiv : blockU L ≃*
    core s.reduction.radical (alpha s.reduction.radical) :=
  ((blockU L).equivMapOfInjective s.componentEmbedding s.componentEmbedding_injective).trans
    (MulEquiv.subgroupCongr s.intrinsic_core_image)

@[simp] theorem intrinsicCoreEquiv_val (x : blockU L) :
    (s.intrinsicCoreEquiv x : FreeAmalgam s.reduction.radical) =
      s.componentEmbedding (x : L) := rfl

noncomputable def centerLayer : Subgroup L :=
  (Z s.reduction.radical (alpha s.reduction.radical)).comap s.componentEmbedding

theorem centerLayer_normal : s.centerLayer.Normal := by
  constructor
  intro x hx l
  change s.componentEmbedding (l * x * l⁻¹) ∈
    Z s.reduction.radical (alpha s.reduction.radical)
  rw [map_mul,map_mul,map_inv]
  exact (mem_normalizer_iff.mp
    (Z_normalized _ _ (s.componentEmbedding_mem_local l)) _).mp hx

variable (common : CommonFacts s.reduction.radical s.source s.geometry)
local notation "r" => s.reduction.radical
local notation "a" => alpha r
local notation "Z₀" => Z r a
local notation "U₀" => U r a
local notation "F₀" => Z₀ ⊓ centralizer (Ltilde r a : Set (FreeAmalgam r))

noncomputable def centralProjection : Z₀ →* U₀ := by
  let := Z_elementary_of_positive r s.geometry a rfl (by
    change 0 < s.geometry.b r
    exact lt_trans (by decide) common.large_distance)
  exact Subgroup.CommutativeComplementProjection.projection Z₀ U₀ F₀
    common.decomposition common.disjoint

noncomputable def layerProjection : s.centerLayer →* Multiplicative (Fin 3 → ZMod 2) :=
  common.natural.equiv.toMonoidHom.comp ((s.centralProjection common).comp
    (s.componentEmbedding.subgroupComap Z₀))

theorem layerProjection_kernel_central (x : s.centerLayer)
    (hx : s.layerProjection common x = 1) : (x : L) ∈ center L := by
  let := Z_elementary_of_positive r s.geometry a rfl (by
    change 0 < s.geometry.b r
    exact lt_trans (by decide) common.large_distance)
  have hp : s.centralProjection common (s.componentEmbedding.subgroupComap Z₀ x) = 1 :=
    common.natural.equiv.injective (hx.trans common.natural.equiv.map_one.symm)
  have hf : s.componentEmbedding (x : L) ∈ F₀ := by
    change (s.componentEmbedding.subgroupComap Z₀ x) ∈ (F₀).subgroupOf Z₀
    rw [← Subgroup.CommutativeComplementProjection.projection_kernel Z₀ U₀ F₀
      common.decomposition common.disjoint]
    exact hp
  apply mem_center_iff.mpr
  intro l
  apply s.componentEmbedding_injective
  rw [map_mul,map_mul]
  exact hf.2 _ (s.componentEmbedding_mem_residual l)

theorem layerProjection_action (l : L) (x : s.centerLayer) :
    (s.layerProjection common ⟨l * (x : L) * l⁻¹,
      s.centerLayer_normal.conj_mem x x.property l⟩).toAdd =
      Representation.specialLinearNatural 3
        (common.natural.marking (h.quotientEquiv (QuotientGroup.mk' _ l)))
          (s.layerProjection common x).toAdd := by
  let := Z_elementary_of_positive r s.geometry a rfl (by
    change 0 < s.geometry.b r
    exact lt_trans (by decide) common.large_distance)
  let z : Z₀ := s.componentEmbedding.subgroupComap Z₀ x
  let y : s.centerLayer := ⟨l * (x : L) * l⁻¹,
    s.centerLayer_normal.conj_mem x x.property l⟩
  let z' : Z₀ := s.componentEmbedding.subgroupComap Z₀ y
  have hl : s.componentEmbedding l ∈ Mbar r :=
    ⟨inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l,rfl⟩
  have hF : s.componentEmbedding l ∈ centralizer (F₀ : Set (FreeAmalgam r)) := by
    intro f hf
    exact (hf.2 _ (s.componentEmbedding_mem_residual l)).symm
  have hp := Subgroup.CommutativeComplementProjection.projection_conjugate Z₀ U₀ F₀
    common.decomposition common.disjoint (common.natural.normalized hl) hF z z'
    (by change s.componentEmbedding (l * (x : L) * l⁻¹) = _; simp only [map_mul,map_inv]; rfl)
  have he := common.natural.action
    (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l)
    (s.centralProjection common z) (s.centralProjection common z') hp
  have hpi : s.source.projection (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l) =
      h.quotientEquiv (QuotientGroup.mk' _ l) := s.projection_component l
  rw [hpi] at he
  exact he

include common in
theorem centerLayer_contains_center (hb : s.geometry.b r = 4) :
    (center (blockU L)).map (blockU L).subtype ≤ s.centerLayer := by
  let early := DistanceFour.earlyFacts s.source s.geometry common hb
  let radius := DistanceFour.Flags.radiusFacts s.source s.geometry common hb early
  have hz := Numerical.SourceCenterBound.DistanceFour.center_core_image s.source common radius hb
  rintro x ⟨u,hu,rfl⟩
  change s.componentEmbedding (u : L) ∈ Z₀
  have hc := (centerCongr s.intrinsicCoreEquiv ⟨u,hu⟩).property
  have hm := mem_map_of_mem (core r a).subtype hc
  rw [hz] at hm
  exact hm.2

include common in
theorem naturalCenterSection_of_distance_four (hb : s.geometry.b r = 4) :
    Nonempty (NaturalCenterSection L) := by
  exact ⟨{
    marking := h.quotientEquiv.trans common.natural.marking
    layer := s.centerLayer
    normal := s.centerLayer_normal
    center_le := s.centerLayer_contains_center common hb
    projection := s.layerProjection common
    action := s.layerProjection_action common
    kernel_central := s.layerProjection_kernel_central common }⟩

/-- The common and radius source facts are discharged from the same original nonabelian MS input. -/
theorem naturalCenterSection_of_nonabelian_distance_four
    (hc : ¬ IsMulCommutative (commutatorCore L)) (hb : s.geometry.b r = 4) :
    Nonempty (NaturalCenterSection L) := by
  obtain ⟨common⟩ := s.commonFacts hc
  exact s.naturalCenterSection_of_distance_four common hb
end MS93.InputSetup
end CFSG.Quasithin.ChapterC.BinaryMS
