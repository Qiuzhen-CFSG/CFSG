module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DoubleDualQuotient

/-!
# The nonabelian distance-four core as a full cover

The source's natural subgroup U contains the core's derived subgroup.
Nonabelianness and natural irreducibility give the reverse inclusion, so
U is exactly that derived subgroup. The constructed elementary core/U action
is a full fixed-kernel cover of two dual natural modules. All projections and
natural coordinates use the same original component-quotient marking.

This form retains the possible fixed part of the full center. It is precisely
the input needed by marked cocycle detection to generate the whole core/U;
lifting through its derived-subgroup kernel then generates the whole core.
It avoids identifying the entire center with U.

The actual nonabelian InputSetup application discharges common, early, radius,
and full-span source facts. Source: MS93 (1993), (4.6.12), pp.910--912;
Aschbacher--Smith 15.3.23 and 15.3.31, printed pp.1128--1129 and1132.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS
open MS93 MS93.DistanceFour
universe u

/-- Coordinate realization of the doubled contragredient natural action. -/
abbrev dualPair : Representation (ZMod 2) BinaryLinearThree.Group (Linear.W × Linear.W) :=
  Representation.prod (BinaryLinearThree.W.comp BinaryLinearThree.AutomorphismAction.graph.toMonoidHom)
    (BinaryLinearThree.W.comp BinaryLinearThree.AutomorphismAction.graph.toMonoidHom)

/-- A full intrinsic core cover with its literal component action and natural
derived subgroup, preserving the same marking on the center section. -/
structure FullCoreDoubleDualCover (A : Type u) [Group A] extends NaturalCenterSection A where
  Space : Type u
  [addCommGroup : AddCommGroup Space]
  [module : Module (ZMod 2) Space]
  [finite : Finite Space]
  representation : Representation (ZMod 2) BinaryLinearThree.Group Space
  coreProjection : blockU A →* Multiplicative Space
  coreOnto : Function.Surjective coreProjection
  coreKernel : coreProjection.ker = _root_.commutator (blockU A)
  coreAction : ∀ (a : A) (x : blockU A),
    (coreProjection (blockConjugate A a x)).toAdd =
      representation (marking (QuotientGroup.mk' (pCore 2 A) a)) (coreProjection x).toAdd
  cover : representation.IntertwiningMap dualPair
  isCover : IsCover cover
  derivedEquiv : _root_.commutator (blockU A) ≃* Multiplicative Linear.W
  derivedAction : ∀ (a : A) (x y : _root_.commutator (blockU A)),
    (y : blockU A) = blockConjugate A a (x : blockU A) →
    (derivedEquiv y).toAdd = BinaryLinearThree.W
      (marking (QuotientGroup.mk' (pCore 2 A) a)) (derivedEquiv x).toAdd
attribute [instance] FullCoreDoubleDualCover.addCommGroup FullCoreDoubleDualCover.module
  FullCoreDoubleDualCover.finite

namespace MS93.DistanceFour
variable {M : Type u} [Group M] [Finite M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

omit [Finite M] in
include source common radius in
/-- A nonabelian source core has exactly the natural subgroup as its derived subgroup. -/
theorem core_derived_eq_U_of_nonabelian
    (hc : ¬ IsMulCommutative (core R (alpha R))) :
    ⁅core R (alpha R),core R (alpha R)⁆ = U R (alpha R) := by
  apply Flags.RankOne.natural_subgroup_eq source common.natural _
    (SmallBranch.core_derived_le_U geometry radius _ rfl)
  · intro he
    apply hc
    apply (_root_.commutator_eq_bot_iff _).mp
    apply map_injective (core R (alpha R)).subtype_injective
    rw [map_subtype_commutator, he, Subgroup.map_bot]
  · intro g hg
    rw [mem_normalizer_iff_map_conj_eq, map_commutator]
    have hn : stabilizer R (alpha R) ≤ normalizer (core R (alpha R)) := by
      rw [alpha, stabilizer_m_base]
      exact core_normalized
    rw [mem_normalizer_iff_map_conj_eq.mp (hn hg)]

end MS93.DistanceFour
namespace MS93.InputSetup
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
  {h : Input κ L R} (s : InputSetup h)
  (common : CommonFacts s.reduction.radical s.source s.geometry)
local notation "r" => s.reduction.radical
local notation "a" => alpha r

include common in
/-- The genuine distance-four source constructs the full intrinsic cover;
its projection kernel is exactly the core derived subgroup. -/
theorem fullCoreDoubleDualCover_of_distance_four
    (hc : ¬ IsMulCommutative (commutatorCore L)) (hb : s.geometry.b r = 4) :
    Nonempty (FullCoreDoubleDualCover L) := by
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
    derivedAction := ?_ }⟩
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

/-- The original nonabelian input supplies every common source premise. -/
theorem fullCoreDoubleDualCover_of_nonabelian_distance_four
    (hc : ¬ IsMulCommutative (commutatorCore L)) (hb : s.geometry.b r = 4) :
    Nonempty (FullCoreDoubleDualCover L) := by
  obtain ⟨common⟩ := s.commonFacts hc
  exact s.fullCoreDoubleDualCover_of_distance_four common hc hb

end MS93.InputSetup
end CFSG.Quasithin.ChapterC.BinaryMS
