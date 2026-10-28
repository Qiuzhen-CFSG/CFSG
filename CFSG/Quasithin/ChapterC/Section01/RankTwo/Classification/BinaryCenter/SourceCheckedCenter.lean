module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.FullCenterCoefficients
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.SmallKernelCenter
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.Intrinsic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction
/-!
# The moved center under the actual binary source split

For an abelian commutator core the original component two-core centralizes
it. At distance four, the full cover has natural derived subgroup, which
intersects every component-central kernel trivially. Above distance four,
the genuine small-displacement theorem supplies the same conclusion for
central kernels of order at most two. In all three cases the preimage of
the quotient two-core center has exactly the original moved center.

The complete binary MS input therefore requires only prescribed critical-path
replacement in its large-distance branch. No C.1.34 classification output
is assumed. This supplies the checked-center identity in the original
Aschbacher--Smith 13.6.22, printed pp.932--933.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS
local notation "sCenter" => fun (A : Subgroup _) => Subgroup.map (Subgroup.subtype A) (Subgroup.center A)
namespace FullCoreDoubleDualCover
variable {J H : Type*} [Group J] [Group H] [Finite J]
  (c : FullCoreDoubleDualCover J)

include c
omit [Finite J] in
private theorem derived_central_eq_one (x : _root_.commutator (blockU J))
    (hx : (x.val : J) ∈ center J) : x = 1 := by
  apply c.derived_projection_bijective.1
  rw [map_one]
  change c.projection (c.derivedLayer x) = 1
  exact (c.centerProjection_eq_one_iff ⟨x.val,c.derived_le_center x.property⟩).mpr hx

/-- A central quotient preserves the moved center in the actual distance-four cover. -/
theorem center_preimage_commutator (hp : IsPPerfect 2 J)
    (f : J →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hn : f.ker ≤ center J) :
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup J)⁆ =
      ⁅sCenter (pCore 2 J), (⊤ : Subgroup J)⁆ := by
  apply center_preimage_commutator_of_small_displacement hp f hf hk
  · rintro z ⟨zC,hzC,rfl⟩ p hp
    exact mul_inv_eq_iff_eq_mul.mp (c.core_centralizes_center p hp ⟨zC,hzC⟩)
  · intro A hA hd
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    intro x hx
    have hx' := commutator_mono hA le_rfl hx
    rw [← map_subtype_commutator] at hx'
    obtain ⟨q,hq,rfl⟩ := hx'
    have he := c.derived_central_eq_one ⟨q,hq⟩ (hn (hd hx))
    exact congrArg (fun a : _root_.commutator (blockU J) => ((a.val : blockU J) : J)) he
end FullCoreDoubleDualCover
namespace MS93.InputSetup
variable {J H : Type*} [Group J] [Group H] [Finite J]
  {κ : GroupClass} {L R : Subgroup J} {h : Input κ L R} (t : InputSetup h)
open scoped IsMulCommutative
/-- The b=4 source constructs its full cover and discharges every structural premise. -/
theorem distanceFour_center_preimage_commutator
    (hc : ¬ IsMulCommutative (commutatorCore L))
    (hb : t.geometry.b t.reduction.radical = 4)
    (f : L →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hn : f.ker ≤ center L) :
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup L)⁆ =
      ⁅sCenter (pCore 2 L), (⊤ : Subgroup L)⁆ := by
  obtain ⟨c⟩ := t.fullCoreDoubleDualCover_of_nonabelian_distance_four hc hb
  have hp : IsPPerfect 2 L := by rw [← h.residual_eq]; exact isPPerfect_pResidual 2
  exact c.center_preimage_commutator hp f hf hk hn
end MS93.InputSetup
open scoped IsMulCommutative
variable {J H : Type*} [Group J] [Group H] [Finite J]
  {κ : GroupClass} {L R : Subgroup J} (h : Input κ L R)
include h
/-- The actual abelian-core theorem supplies the original two-core action. -/
theorem Input.abelian_center_preimage_commutator
    (hc : IsMulCommutative (commutatorCore L))
    (f : L →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup L)⁆ =
      ⁅sCenter (pCore 2 L), (⊤ : Subgroup L)⁆ := by
  obtain ⟨m,hm,⟨q⟩⟩ := AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient
    (h := h) hc
  have hQc : blockU L ≤ centralizer (pCore 2 L : Set L) := by
    intro x hx y hy
    apply Subtype.ext
    have hx' := (h.abelianCore_componentCore_centralizes_of_naturalQuotient hc q)
      (h.intrinsicCoreEquiv ⟨x,hx⟩).property
    exact hx' y (mem_map_of_mem L.subtype hy)
  have hQQ : IsMulCommutative (blockU L) := by
    apply isMulCommutative_iff.mpr
    intro a b
    apply h.intrinsicCoreEquiv.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hc
      (h.intrinsicCoreEquiv a) (h.intrinsicCoreEquiv b)
  have hp : IsPPerfect 2 L := by rw [← h.residual_eq]; exact isPPerfect_pResidual 2
  apply center_preimage_commutator_of_small_displacement hp f hf hk
    ((map_subtype_le _).trans hQc)
  intro A hA _ a ha x hx
  exact congrArg Subtype.val (isMulCommutative_iff.mp hQQ
    (⟨x,hx⟩ : blockU L) ⟨a,hA ha⟩)

open MS93 MS93.DistanceEight.PathCentrality
/-- The direct binary split proves the center identity in all cases. The only
remaining earlier source input is prescribed replacement above distance four. -/
theorem Input.center_preimage_commutator_of_replacement
    (f : L →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hcard : Nat.card f.ker ≤ 2) (hn : f.ker.map L.subtype ≤ center J)
    (replacement : ∀ (t : InputSetup h),
      CommonFacts t.reduction.radical t.source t.geometry →
      4 < t.geometry.b t.reduction.radical → ∀ {a a'}
      (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators _ p → PrescribedReplacement _ p) :
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup L)⁆ =
      ⁅sCenter (pCore 2 L), (⊤ : Subgroup L)⁆ := by
  by_cases hc : IsMulCommutative (commutatorCore L)
  · exact h.abelian_center_preimage_commutator hc f hf hk
  obtain ⟨t⟩ := exists_setup h hc
  obtain ⟨common⟩ := t.commonFacts hc
  by_cases hb : t.geometry.b t.reduction.radical = 4
  · apply t.distanceFour_center_preimage_commutator hc hb f hf hk
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hn (mem_map_of_mem L.subtype hx)) y)
  · have heven := t.geometry.even (alpha t.reduction.radical) rfl
    change Even (t.geometry.b t.reduction.radical) at heven
    obtain ⟨n,hn'⟩ := heven
    have hlarge : 4 < t.geometry.b t.reduction.radical := by
      have := common.large_distance
      omega
    exact t.large_center_preimage_commutator common
      (Source44.SourceEarlier.earlier common hlarge (replacement t common hlarge))
      f hf hk hcard hn
end CFSG.Quasithin.ChapterC.BinaryMS
