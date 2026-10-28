module
public import Theory.Representation.Triality.RestrictedWeights.ConcreteRootUniqueness
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.WeightReflection
public import Theory.AlgebraicGroup.RootSubgroups.SL2RootMarking
public import Theory.AlgebraicGroup.RootSystems.Weyl
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Characters
public import Theory.AlgebraicGroup.Borel.SelfNormalizer.Source
public import Theory.AlgebraicGroup.Tori.NormalizerConjugacy
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.NormalizerActionExistence
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.WeylRealization.NormalizerAction
/-!
# The actual Spin torus normalizer and its D4 Weyl action

Conjugation acts on the actual root subgroups. A positive-chamber stabilizer
normalizes both opposite Borels, whose proved self-normalization places it in
their exact torus intersection. Standard chamber transitivity and the concrete
simple normalizers therefore identify the image with the Weyl group. The
source maximal-torus conjugacy theorem supplies ambient torus fusion.
This is the normalizer and fusion input of the triality odd-class count;
no legacy normalizer theorem or Bruhat-uniqueness premise is used.
Source: GLS3 1.9.5(f), Steinberg 6.1–6.4 and 14.8.
-/

public noncomputable section
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.NormalizerActionExistence
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction
namespace Triality.RestrictedWeights.Concrete.TorusGeometrySource
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))
theorem source_multiplicity (a:(finiteGeometry k hu).roots.Root) :
    RootWeightSpaceMultiplicityOne (finiteGeometry k hu).torus
      ((finiteGeometry k hu).roots.rootWeight a) := by
  apply ClassBound.ConnectedCentralizer.Normalizer.RootUniqueness.root_multiplicityOne_of_tangent_span
  change LinearMap.range (Bor1.identityTangentMorphismLinearMap (CorootTorus.closedSubgroup k).inclusion) ⊔
    (⨆ a : ULift RootIndex, LinearMap.range
      (Bor1.identityTangentMorphismLinearMap (rootClosedSubgroup k a.down).inclusion)) = ⊤
  simpa only [iSup_ulift] using torus_root_tangent_span k
theorem chamber_kernel (hmult : ∀ a:(finiteGeometry k hu).roots.Root,
    RootWeightSpaceMultiplicityOne (finiteGeometry k hu).torus
      ((finiteGeometry k hu).roots.rootWeight a))
    (g:(finiteGeometry k hu).torus.normalizer.toSubgroup)
    (hp:∀ a,rootAction (finiteGeometry k hu).realized g a∈(finiteGeometry k hu).roots.positive ↔
       a∈(finiteGeometry k hu).roots.positive) : g.val∈(finiteGeometry k hu).torus.toSubgroup := by
  have hnP := mem_borel_normalizer_of_preserves_positive (finiteGeometry k hu).realized hmult
    (finiteGeometry k hu).bigCell.data.positive_witness g hp
  have hnM := mem_borel_normalizer_of_preserves_positive (finiteGeometry k hu).realized hmult
    (finiteGeometry k hu).bigCell.data.opposite_witness g (fun a => by
      change (finiteGeometry k hu).roots.neg (rootAction (finiteGeometry k hu).realized g a) ∈
        (finiteGeometry k hu).roots.positive ↔ _
      rw [← rootAction_neg]
      exact hp _)
  rw [BorelSelfNormalizer.normalizer_eq (finiteGeometry k hu).simple.1 _
    (finiteGeometry k hu).bigCell.data.B_isBorel] at hnP
  rw [BorelSelfNormalizer.normalizer_eq (finiteGeometry k hu).simple.1 _
    (finiteGeometry k hu).bigCell.data.Bopp_isBorel] at hnM
  have h : g.val∈(finiteGeometry k hu).bigCell.data.B.toSubgroup ⊓
      (finiteGeometry k hu).bigCell.data.Bopp.toSubgroup := ⟨hnP,hnM⟩
  rwa [(finiteGeometry k hu).bigCell.intersection_eq_torus] at h

theorem normalizer_fusion : ClassBound.AmbientCount.TorusGeometry.NormalizerControlsFusion (finiteGeometry k hu) := by
  intro t v hv
  obtain ⟨g,hg,he⟩ := SemisimpleCentralizerTori.normalizer_conjugator_of_toral_conjugacy
    (finiteGeometry k hu).maximalTorus ((finiteGeometry k hu).torus.pointEquiv t).property
    ((finiteGeometry k hu).torus.pointEquiv v).property hv
  exact ⟨⟨g,hg⟩,he⟩


open Theory.AlgebraicGroup.StandardRootSystem
open ClassBound.AmbientCount
def weylRootPerm : Weyl →* Equiv.Perm (finiteGeometry k hu).roots.Root :=
  (finiteGeometry k hu).rootIndex.symm.permCongrHom.toMonoidHom.comp
    (typeDRootPairing 2).weylGroupToPerm

theorem weylRootPerm_injective : Function.Injective (weylRootPerm k hu) := by
  intro g h he
  have hgh : (typeDRootPairing 2).weylGroupToPerm g =
      (typeDRootPairing 2).weylGroupToPerm h := by
    apply Equiv.ext
    intro a
    exact congrArg ULift.down (Equiv.congr_fun he (ULift.up a))
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective (typeDRootPairing 2)
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range (v := (typeDRootPairing 2).root)
    (RootPairing.IsRootSystem.span_root_eq_top (P := typeDRootPairing 2))
  intro i
  change g • (typeDRootPairing 2).root i = h • (typeDRootPairing 2).root i
  rw [RootPairing.weylGroup_apply_root, RootPairing.weylGroup_apply_root, hgh]

def simpleN (i:Fin 4) : (finiteGeometry k hu).torus.normalizer.toSubgroup :=
  ⟨simpleNormalizer k i, CorootTorus.simpleNormalizer_mem_torusNormalizer k i⟩

theorem simpleN_action (i:Fin 4) :
    rootAction (finiteGeometry k hu).realized (simpleN k hu i) =
      weylRootPerm k hu (RootPairing.weylGroup.ofIdx (typeDRootPairing 2) (typeDSimpleRootIndex 2 i)) := by
  ext a
  apply (finiteGeometry k hu).realized.rootSubgroup_injective
  rw [← rootAction_transport (finiteGeometry k hu).realized (source_multiplicity k hu)]
  apply SetLike.coe_injective
  ext x
  change x∈((finiteGeometry k hu).roots.rootSubgroup a).conjugate (simpleN k hu i).val ↔ _
  rw [ClosedSubgroup.mem_conjugate_iff]
  change (simpleNormalizer k i)⁻¹ * x * simpleNormalizer k i ∈ rootClosedSubgroup k a.down ↔
    x ∈ rootClosedSubgroup k ((typeDRootPairing 2).reflectionPerm (simpleRoot i) a.down)
  rw [mem_rootClosedSubgroup_iff,mem_rootClosedSubgroup_iff]
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨t,?_⟩
    have he := congrArg (fun z=> (simpleNormalizer k i)⁻¹ * z * simpleNormalizer k i) ht
    rw [simpleNormalizer_rootPoint_conjugation] at he
    have hnn : simpleNormalizer k i * simpleNormalizer k i=1 := by
      rw [←pow_two]; exact normalizerWord_sq k _ _
    apply he.trans
    calc
      _ = ((simpleNormalizer k i)*(simpleNormalizer k i))⁻¹ * x *
          ((simpleNormalizer k i)*(simpleNormalizer k i)) := by group
      _ = x := by rw [hnn]; simp
  · rintro ⟨t,rfl⟩
    refine ⟨t,?_⟩
    rw [simpleNormalizer_rootPoint_conjugation]
    rw [RootPairing.reflectionPerm_self]

def actualPositiveSubsystem
    (Q:Set (finiteGeometry k hu).roots.Root)
    (hQ:IsPositiveSystem (finiteGeometry k hu).roots Q) :
    (typeDRootPairing 2).PositiveSubsystem where
  carrier := (ULift.up ⁻¹' Q)
  add_mem := by
    intro a b c ha hb hc
    exact hQ.2.2 _ ha _ hb _
      ((pinnedRootData_isRootAdditionRealization k _ _ _).mpr hc)
  mem_xor_neg := by
    intro a
    change Xor (ULift.up a∈Q) (ULift.up ((typeDRootPairing 2).reflectionPerm a a)∈Q)
    change Xor (ULift.up a∈Q) ((finiteGeometry k hu).roots.neg (ULift.up a)∈Q)
    have hor : ULift.up a∈Q ∨ (finiteGeometry k hu).roots.neg (ULift.up a)∈Q := by
      have hh : ULift.up a∈Q ∪ (finiteGeometry k hu).roots.neg ⁻¹' Q := by
        rw [hQ.2.1]; trivial
      exact hh
    have hnot : ¬ (ULift.up a∈Q ∧ (finiteGeometry k hu).roots.neg (ULift.up a)∈Q) := by
      intro h
      have hh : ULift.up a∈Q ∩ (finiteGeometry k hu).roots.neg ⁻¹' Q := h
      rw [hQ.1] at hh
      exact hh
    exact hor.elim (fun h=>Or.inl ⟨h,fun hn=>hnot ⟨h,hn⟩⟩)
      (fun h=>Or.inr ⟨h,fun hp=>hnot ⟨hp,h⟩⟩)


theorem weyl_positive_transport (Q:Set (finiteGeometry k hu).roots.Root)
    (hQ:IsPositiveSystem (finiteGeometry k hu).roots Q) :
    ∃ w:Weyl,∀ a,weylRootPerm k hu w a∈(finiteGeometry k hu).roots.positive ↔ a∈Q := by
  obtain ⟨w,hw⟩ := exists_weylGroup_translate_base_toPositiveSubsystem (typeDRootPairing 2)
    (typeDRootPairing_base 2) (actualPositiveSubsystem k hu Q hQ)
  refine ⟨w⁻¹,?_⟩
  intro a
  have he : (w • typeDRootPairing_base 2).IsPos a.down ↔ a∈Q := by
    rw [← RootPairing.Base.mem_toPositiveSubsystem,hw]
    rfl
  change (RootPairing.Base.mapAut w.val (typeDRootPairing_base 2)).IsPos a.down ↔ a∈Q at he
  rw [RootPairing.Base.isPos_mapAut_iff] at he
  exact he

theorem weyl_has_lift (w:Weyl) : ∃ g:(finiteGeometry k hu).torus.normalizer.toSubgroup,
    rootAction (finiteGeometry k hu).realized g=weylRootPerm k hu w := by
  obtain ⟨l,rfl⟩ := (typeDRootPairing_base 2).exists_wordProd_eq w
  induction l with
  | nil => exact ⟨1,by rw [map_one,RootPairing.Base.wordProd_nil,map_one]⟩
  | cons i l ih =>
    obtain ⟨j,rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective i
    obtain ⟨g,hg⟩ := ih
    refine ⟨simpleN k hu j*g,?_⟩
    rw [map_mul,simpleN_action,hg,RootPairing.Base.wordProd_cons,map_mul]
    rfl

theorem normalizer_action_mem_weyl (g:(finiteGeometry k hu).torus.normalizer.toSubgroup) :
    rootAction (finiteGeometry k hu).realized g∈(weylRootPerm k hu).range := by
  obtain ⟨w,hw⟩ := weyl_positive_transport k hu
    ((rootAction (finiteGeometry k hu).realized g⁻¹) ⁻¹' (finiteGeometry k hu).roots.positive)
    (rootAction_positive_preimage (finiteGeometry k hu).realized
      (finiteGeometry k hu).additionComplete (finiteGeometry k hu).bigCell.data.positive g⁻¹)
  obtain ⟨m,hm⟩ := weyl_has_lift k hu w
  have hmg : (m*g).val ∈ (finiteGeometry k hu).torus.toSubgroup := by
    apply chamber_kernel k hu (source_multiplicity k hu)
    intro a
    have h := hw (rootAction (finiteGeometry k hu).realized g a)
    change _ ↔ rootAction (finiteGeometry k hu).realized g⁻¹
      (rootAction (finiteGeometry k hu).realized g a)∈(finiteGeometry k hu).roots.positive at h
    rw [map_inv,Equiv.Perm.inv_def,Equiv.symm_apply_apply] at h
    simpa only [map_mul,Equiv.Perm.mul_apply,hm] using h
  have hmg' : m*g ∈ (finiteGeometry k hu).torus.toSubgroup.subgroupOf
      (finiteGeometry k hu).torus.normalizer.toSubgroup := hmg
  have hker := torus_le_kernel (finiteGeometry k hu).realized
    (finiteGeometry k hu).maximalTorus.1 hmg'
  change rootAction (finiteGeometry k hu).realized (m*g)=1 at hker
  rw [map_mul,hm] at hker
  refine ⟨w⁻¹,?_⟩
  rw [map_inv]
  exact (eq_inv_of_mul_eq_one_right hker).symm


def normalizerToWeyl :
    (finiteGeometry k hu).torus.normalizer.toSubgroup →* Weyl where
  toFun g := Classical.choose (normalizer_action_mem_weyl k hu g)
  map_one' := (weylRootPerm_injective k hu) (by
    rw [Classical.choose_spec (normalizer_action_mem_weyl k hu 1),map_one,map_one])
  map_mul' g h := (weylRootPerm_injective k hu) (by
    rw [Classical.choose_spec (normalizer_action_mem_weyl k hu (g*h)),map_mul,map_mul,
      Classical.choose_spec (normalizer_action_mem_weyl k hu g),
      Classical.choose_spec (normalizer_action_mem_weyl k hu h)])

theorem normalizerToWeyl_spec (g:(finiteGeometry k hu).torus.normalizer.toSubgroup) :
    weylRootPerm k hu (normalizerToWeyl k hu g)=rootAction (finiteGeometry k hu).realized g :=
  Classical.choose_spec (normalizer_action_mem_weyl k hu g)

theorem normalizerToWeyl_surjective : Function.Surjective (normalizerToWeyl k hu) := by
  intro w
  obtain ⟨g,hg⟩ := weyl_has_lift k hu w
  exact ⟨g,weylRootPerm_injective k hu ((normalizerToWeyl_spec k hu g).trans hg)⟩

theorem normalizerToWeyl_simple (i:Fin 4) : normalizerToWeyl k hu (simpleN k hu i)=
    RootPairing.weylGroup.ofIdx (typeDRootPairing 2) (typeDSimpleRootIndex 2 i) :=
  weylRootPerm_injective k hu ((normalizerToWeyl_spec k hu _).trans (simpleN_action k hu i))

theorem simpleN_conjugation (i:Fin 4) (t:(finiteGeometry k hu).torus.carrierVariety.Point) :
    (simpleN k hu i).val * (finiteGeometry k hu).torus.includePoint t * (simpleN k hu i).val⁻¹ =
      (finiteGeometry k hu).torus.includePoint
        (TorusGeometry.simpleReflection (finiteGeometry k hu) i t) := by
  have he : (CorootTorus.torusReflection k i).onPoints t =
      TorusGeometry.simpleReflection (finiteGeometry k hu) i t := by
    apply ClassBound.ConnectedCentralizer.Normalizer.torusPoint_ext (finiteGeometry k hu)
    intro a
    rw [TorusGeometry.simpleReflection_weight]
    change (weightEquiv k (Multiplicative.ofAdd a)).pointCharacter _ =
      (weightEquiv k (Multiplicative.ofAdd (D4RestrictedWeight.reflection i a))).pointCharacter t
    rw [weightEquiv_apply,weightEquiv_apply]
    exact (CorootTorus.weightEmbedding_reflection k i a t).symm
  calc
    _ = (simpleNormalizer k i)⁻¹ * (CorootTorus.closedSubgroup k).includePoint t * simpleNormalizer k i := by
      change simpleNormalizer k i * (CorootTorus.closedSubgroup k).includePoint t *
        (simpleNormalizer k i)⁻¹ = _
      rw [normalizerWord_inv]
    _ = (CorootTorus.closedSubgroup k).includePoint ((CorootTorus.torusReflection k i).onPoints t) :=
      (CorootTorus.torusReflection_inclusion k i t).symm
    _ = _ := congrArg (finiteGeometry k hu).torus.includePoint he

def normalizerRealization : TorusGeometry.NormalizerRealization (finiteGeometry k hu) where
  toWeyl := normalizerToWeyl k hu
  surjective := normalizerToWeyl_surjective k hu
  kernel_centralizes := by
    intro g hg
    have he : rootAction (finiteGeometry k hu).realized g=1 :=
      (normalizerToWeyl_spec k hu g).symm.trans
        ((congrArg (weylRootPerm k hu) hg).trans (map_one _))
    have ht := chamber_kernel k hu (source_multiplicity k hu) g (fun a=>by rw[he];rfl)
    let T := (finiteGeometry k hu).torus
    let := T.carrierAlgebraicGroup
    have hc := isMulCommutative_iff.mp (finiteGeometry k hu).maximalTorus.1.isMulCommutative
    change g.val∈Subgroup.centralizer _
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    let a := T.pointEquiv.symm ⟨x,hx⟩
    let b := T.pointEquiv.symm ⟨g.val,ht⟩
    have h := congrArg T.inclusion.onPoints (hc a b)
    rw [map_mul,map_mul] at h
    have ha : T.inclusion.onPoints a=x := congrArg Subtype.val (T.pointEquiv.apply_symm_apply _)
    have hb : T.inclusion.onPoints b=g.val := congrArg Subtype.val (T.pointEquiv.apply_symm_apply _)
    rwa [ha,hb] at h
  simple_lift := fun i=>⟨simpleN k hu i,normalizerToWeyl_simple k hu i,simpleN_conjugation k hu i⟩

theorem normalizerRealization_ker_le
    (g:(finiteGeometry k hu).torus.normalizer.toSubgroup)
    (hg:(normalizerRealization k hu).toWeyl g=1) : g.val∈(finiteGeometry k hu).torus.toSubgroup := by
  have he : rootAction (finiteGeometry k hu).realized g=1 :=
    (normalizerToWeyl_spec k hu g).symm.trans
      ((congrArg (weylRootPerm k hu) hg).trans (map_one _))
  exact chamber_kernel k hu (source_multiplicity k hu) g (fun a=>by rw[he];rfl)

def weylGeometry : TorusGeometry.WeylGeometry (finiteGeometry k hu) :=
  (normalizerRealization k hu).weylGeometry (normalizer_fusion k hu)
end Triality.RestrictedWeights.Concrete.TorusGeometrySource
