module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.FullCoreCover

/-!
The two distance-four constructions retain the same original component marking.
The full cover gives the exact natural derived subgroup, while the independent
quotient construction divides by the entire center. Both are built from one
CommonFacts witness, so their markings agree literally. This is the source pair
needed by the weak-center argument in Aschbacher--Smith15.3.23, using MS93(4.6.12).
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS
open MS93 MS93.DistanceFour
namespace MS93.InputSetup
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
  {h : Input κ L R} (s : InputSetup h)
  (common : CommonFacts s.reduction.radical s.source s.geometry)
local notation "r" => s.reduction.radical
local notation "a" => alpha r

include common in
theorem fullCoreDoubleDualCover_marked_of_distance_four
    (hc : ¬ IsMulCommutative (commutatorCore L)) (hb : s.geometry.b r = 4) :
    ∃ c : FullCoreDoubleDualCover L, c.marking = h.quotientEquiv.trans common.natural.marking := by
  let early := DistanceFour.earlyFacts s.source s.geometry common hb
  let radius := DistanceFour.Flags.radiusFacts s.source s.geometry common hb early
  obtain ⟨⟨q⟩, hSC⟩ := LargeBranch.fullSpans s.source common radius hb
    (LargeBranch.RankOne.source_spanRecognition common radius hb)
  obtain ⟨d⟩ := SmallBranch.exists_quotientAction s.source s.geometry common radius
  let ρ : Representation (ZMod 2) SL d.Space :=
    d.representation.comp common.natural.marking.symm.toMonoidHom
  let p : ρ.IntertwiningMap dualPair := {
    toLinearMap := Numerical.SourceCenterBound.DistanceFour.descendedLinear s.source common radius q d
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      change Numerical.SourceCenterBound.DistanceFour.descendedLinear s.source common radius q d
        (d.representation (common.natural.marking.symm g) v) = _
      rw [Numerical.SourceCenterBound.DistanceFour.descendedLinear_action,
        common.natural.marking.apply_symm_apply]
      rfl }
  have hcover := Numerical.SourceCenterBound.DistanceFour.coverMap_isCover
    s.source common radius q hSC d
  have hp : IsCover p := by
    refine ⟨Numerical.SourceCenterBound.DistanceFour.descendedLinear_onto
      s.source common radius q hSC d, ?_, ?_⟩
    · intro v hv g
      have hk : Numerical.SourceCenterBound.DistanceFour.coverMap s.source common radius q d v = 0 := by
        change AbelianCore.DoubleCopy.CoverModels.pairEquiv.symm
          (Numerical.SourceCenterBound.DistanceFour.descendedLinear s.source common radius q d v) = 0
        rw [show Numerical.SourceCenterBound.DistanceFour.descendedLinear s.source common radius q d v = 0 from hv,
          map_zero]
      have he := hcover.2.1 hk
        (Numerical.SourceCenterBound.DistanceFour.markingTwist s.source common
          (common.natural.marking.symm g))
      change d.representation
        ((Numerical.SourceCenterBound.DistanceFour.markingTwist s.source common).symm
          (Numerical.SourceCenterBound.DistanceFour.markingTwist s.source common
            (common.natural.marking.symm g))) v = v at he
      rw [MulEquiv.symm_apply_apply] at he
      exact he
    · have hle : Coinvariants.ker
          (Numerical.SourceCenterBound.DistanceFour.twistedRepresentation s.source common d) ≤
          Coinvariants.ker ρ := by
        apply Submodule.span_le.mpr
        rintro _ ⟨⟨g,v⟩,rfl⟩
        have he := Coinvariants.sub_mem_ker (ρ := ρ)
          (common.natural.marking
            ((Numerical.SourceCenterBound.DistanceFour.markingTwist s.source common).symm g)) v
        change d.representation (common.natural.marking.symm (common.natural.marking _)) v - v ∈ _ at he
        rw [common.natural.marking.symm_apply_apply] at he
        exact he
      rw [hcover.2.2] at hle
      exact top_unique hle
  have hn : ¬ IsMulCommutative (core r a) := by
    intro he
    apply hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply s.coreEquiv.symm.injective
    simpa only [map_mul] using isMulCommutative_iff.mp he
      (s.coreEquiv.symm x) (s.coreEquiv.symm y)
  have hd : (U r a).subgroupOf (core r a) = _root_.commutator (core r a) := by
    apply map_injective (core r a).subtype_injective
    rw [map_subgroupOf_eq_of_le (U_le_core s.source s.geometry common), map_subtype_commutator,
      core_derived_eq_U_of_nonabelian s.source common radius hn]
  let f := d.projection.comp s.intrinsicCoreEquiv.toMonoidHom
  have hf : f.ker = _root_.commutator (blockU L) := by
    rw [← MonoidHom.comap_ker, d.kernel, hd]
    apply map_injective (f := s.intrinsicCoreEquiv.toMonoidHom) s.intrinsicCoreEquiv.injective
    rw [map_comap_eq_self_of_surjective s.intrinsicCoreEquiv.surjective, map_commutator_eq,
      MonoidHom.range_eq_top.mpr s.intrinsicCoreEquiv.surjective, ← _root_.commutator_def]
  have hmap : (_root_.commutator (blockU L)).map s.intrinsicCoreEquiv.toMonoidHom =
      _root_.commutator (core r a) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr s.intrinsicCoreEquiv.surjective,
      ← _root_.commutator_def]
  let Eder : _root_.commutator (blockU L) ≃* U r a :=
    (s.intrinsicCoreEquiv.subgroupMap (_root_.commutator (blockU L))).trans
      ((MulEquiv.subgroupCongr hmap).trans
        ((MulEquiv.subgroupCongr hd.symm).trans
          (subgroupOfEquivOfLe (U_le_core s.source s.geometry common))))
  have hEder (x : _root_.commutator (blockU L)) :
      (Eder x : FreeAmalgam r) = s.componentEmbedding (x.val : L) := rfl
  refine ⟨{
    marking := h.quotientEquiv.trans common.natural.marking
    layer := s.centerLayer
    normal := s.centerLayer_normal
    center_le := s.centerLayer_contains_center common hb
    projection := s.layerProjection common
    action := s.layerProjection_action common
    kernel_central := s.layerProjection_kernel_central common
    Space := d.Space
    representation := ρ
    coreProjection := f
    coreOnto := d.onto.comp s.intrinsicCoreEquiv.surjective
    coreKernel := hf
    coreAction := ?_
    cover := p
    isCover := hp
    derivedEquiv := Eder.trans common.natural.equiv
    derivedAction := ?_ }, rfl⟩
  · intro l x
    let m : s.reduction.overgroup := inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l
    have hy : (s.intrinsicCoreEquiv (blockConjugate L l x) : FreeAmalgam r) =
        embedM r m * (s.intrinsicCoreEquiv x : FreeAmalgam r) * (embedM r m)⁻¹ := by
      simp only [s.intrinsicCoreEquiv_val]
      change s.componentEmbedding (l * (x:L) * l⁻¹) = _
      simp only [map_mul,map_inv]
      rfl
    have he := d.action m (s.intrinsicCoreEquiv x)
      (s.intrinsicCoreEquiv (blockConjugate L l x)) hy
    have hm : s.source.projection m = h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) :=
      s.projection_component l
    rw [hm] at he
    change (d.projection (s.intrinsicCoreEquiv (blockConjugate L l x))).toAdd =
      d.representation (common.natural.marking.symm
        (common.natural.marking (h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l))))
          (d.projection (s.intrinsicCoreEquiv x)).toAdd
    rw [common.natural.marking.symm_apply_apply]
    exact he
  · intro l x y hy
    let m : s.reduction.overgroup := inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l
    have he := common.natural.action m (Eder x) (Eder y) (by
      rw [hEder,hEder]
      have hv : (y.val : L) = l * (x.val : L) * l⁻¹ := congrArg Subtype.val hy
      rw [hv,map_mul,map_mul,map_inv]
      rfl)
    have hm : s.source.projection m = h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) :=
      s.projection_component l
    rw [hm] at he
    exact he


include common in
theorem naturalCenterDoubleDualQuotient_marked_of_distance_four
    (hb : s.geometry.b r = 4) : ∃ c : NaturalCenterDoubleDualQuotient L, c.marking = h.quotientEquiv.trans common.natural.marking := by
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
    quotient_action := ?_ }, rfl⟩
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


omit common in
/-- The two exact source layers retain a single original component marking. -/
theorem fullCore_cover_quotient_same_marking
    (hc : ¬ IsMulCommutative (commutatorCore L)) (hb : s.geometry.b r = 4) :
    ∃ c : FullCoreDoubleDualCover L, ∃ n : NaturalCenterDoubleDualQuotient L,
      c.marking = n.marking := by
  obtain ⟨common⟩ := s.commonFacts hc
  obtain ⟨c,hc'⟩ := s.fullCoreDoubleDualCover_marked_of_distance_four common hc hb
  obtain ⟨n,hn⟩ := s.naturalCenterDoubleDualQuotient_marked_of_distance_four common hb
  exact ⟨c,n,hc'.trans hn.symm⟩
end MS93.InputSetup
end CFSG.Quasithin.ChapterC.BinaryMS
