module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Numerical.SourceCenterBound.DistanceFour.Cover

/-!
# The original distance-four center and doubled-dual quotient

The source's complete two-span construction maps its commutator core onto two
copies of the dual natural module. The radius-center identity identifies the
kernel with the full center of the core. Transport through the actual component
embedding gives the intrinsic block core, with precisely the same marking as
the already proved natural center section. Its component-fixed kernel is
retained; no unproved equality of that section with a pure natural module is
used.

The nonabelian InputSetup consumer discharges the common, early and radius
facts. This supplies the homogeneous quotient used by the natural-dual
residual contradiction in Aschbacher--Smith 15.3.24.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12), pp.910--912;
Aschbacher--Smith C.1.34(3), printed pp.136--137.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS
open MS93 MS93.DistanceFour

/-- The actual center section and the quotient by the full intrinsic center
use the same marking. The center section can have a component-fixed kernel. -/
structure NaturalCenterDoubleDualQuotient (A : Type*) [Group A]
    extends NaturalCenterSection A where
  quotient : blockU A →* Multiplicative (Linear.W × Linear.W)
  onto : Function.Surjective quotient
  kernel : quotient.ker = center (blockU A)
  quotient_action : ∀ (a : A) (x : blockU A),
    (quotient (blockConjugate A a x)).toAdd =
      (Linear.dual (marking (QuotientGroup.mk' (pCore 2 A) a)) (quotient x).toAdd.1,
       Linear.dual (marking (QuotientGroup.mk' (pCore 2 A) a)) (quotient x).toAdd.2)

namespace MS93.InputSetup
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
  {h : Input κ L R} (s : InputSetup h)
  (common : CommonFacts s.reduction.radical s.source s.geometry)
local notation "r" => s.reduction.radical
local notation "a" => alpha r

include common in
/-- Both existing source constructions are transported through the identical
intrinsic component embedding, retaining the same quotient marking. -/
theorem naturalCenterDoubleDualQuotient_of_distance_four
    (hb : s.geometry.b r = 4) : Nonempty (NaturalCenterDoubleDualQuotient L) := by
  let early := DistanceFour.earlyFacts s.source s.geometry common hb
  let radius := DistanceFour.Flags.radiusFacts s.source s.geometry common hb early
  obtain ⟨⟨q⟩, hSC⟩ := LargeBranch.fullSpans s.source common radius hb
    (LargeBranch.RankOne.source_spanRecognition common radius hb)
  let p := Numerical.SourceCenterBound.DistanceFour.coreProjection s.source common radius q
  let f : blockU L →* Multiplicative (Linear.W × Linear.W) :=
    p.comp s.intrinsicCoreEquiv.toMonoidHom
  have hp : p.ker = center (core r a) := by
    apply map_injective (core r a).subtype_injective
    rw [Numerical.SourceCenterBound.DistanceFour.coreProjection_kernel,
      Numerical.SourceCenterBound.DistanceFour.center_core_image s.source common radius hb,
      subgroupOf_map_subtype, inf_comm]
  have hf : f.ker = center (blockU L) := by
    rw [← MonoidHom.comap_ker, hp]
    ext x
    change s.intrinsicCoreEquiv x ∈ center (core r a) ↔ x ∈ center (blockU L)
    constructor
    · intro hx
      have hz := (centerCongr s.intrinsicCoreEquiv.symm ⟨s.intrinsicCoreEquiv x, hx⟩).property
      change s.intrinsicCoreEquiv.symm (s.intrinsicCoreEquiv x) ∈ _ at hz
      simpa only [MulEquiv.symm_apply_apply] using hz
    · intro hx
      exact (centerCongr s.intrinsicCoreEquiv ⟨x, hx⟩).property
  refine ⟨{
    marking := h.quotientEquiv.trans common.natural.marking
    layer := s.centerLayer
    normal := s.centerLayer_normal
    center_le := s.centerLayer_contains_center common hb
    projection := s.layerProjection common
    action := s.layerProjection_action common
    kernel_central := s.layerProjection_kernel_central common
    quotient := f
    onto := (Numerical.SourceCenterBound.DistanceFour.coreProjection_onto
      s.source common radius q hSC).comp s.intrinsicCoreEquiv.surjective
    kernel := hf
    quotient_action := ?_ }⟩
  intro l x
  let m : s.reduction.overgroup := inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l
  have hy : (s.intrinsicCoreEquiv (blockConjugate L l x) : FreeAmalgam r) =
      embedM r m * (s.intrinsicCoreEquiv x : FreeAmalgam r) * (embedM r m)⁻¹ := by
    simp only [s.intrinsicCoreEquiv_val]
    change s.componentEmbedding (l * (x : L) * l⁻¹) = _
    simp only [map_mul, map_inv]
    rfl
  have he := Numerical.SourceCenterBound.DistanceFour.coreProjection_action
    s.source common radius q m (s.intrinsicCoreEquiv x)
      (s.intrinsicCoreEquiv (blockConjugate L l x)) hy
  have hm : s.source.projection m = h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) :=
    s.projection_component l
  rw [hm] at he
  exact he

/-- The original nonabelian input discharges all common, early and radius
facts; only its actual distance-four branch remains. -/
theorem naturalCenterDoubleDualQuotient_of_nonabelian_distance_four
    (hc : ¬ IsMulCommutative (commutatorCore L)) (hb : s.geometry.b r = 4) :
    Nonempty (NaturalCenterDoubleDualQuotient L) := by
  obtain ⟨common⟩ := s.commonFacts hc
  exact s.naturalCenterDoubleDualQuotient_of_distance_four common hb

end MS93.InputSetup
end CFSG.Quasithin.ChapterC.BinaryMS
