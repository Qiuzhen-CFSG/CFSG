module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CubicModule
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CoreStabilizers
public import Theory.GroupTheory.Commutator.PerfectQuotient
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
/-!
# The full cubic centralizer and its central double extension

Put H=C_G(z) and let X be the specified Sylow three-subgroup of the
original cubic lift. Restricting H→H/Z(H) gives a surjection from C_H(X)
onto the already identified triple cover of M22. Its kernel is exactly
the original marker line, of order two. The center of C_H(X) is exactly
XZ(H), of order six, and the resulting simple quotient uses the original
cubic automorphism marking.

The derived subgroup is a perfect central cover of 3.M22, hence quasisimple;
it equals the layer of C_H(X) and has index dividing two. Thus the remaining
perfectness obligation is precisely membership of z in that derived subgroup.
The proof does not infer perfectness upstairs merely from perfectness modulo z.

Frattini's product H=Q N_H(X), together with Q∩N_H(X)=Z(H), also gives the
literal double extension N_H(X)/Z(H)≃H/Q. The full centralizer has index two
in this original normalizer. An involution outside it still has to be
constructed to obtain the source splitting.

These are the central-extension steps needed for Aschbacher--Segev,
The uniqueness of groups of type J4, Invent. Math. 105 (1991), (4.8)--(4.9),
printed p.599, DOI 10.1007/BF01232280. The cocode commutator witness and the
involution-lifting argument on that page remain separate obligations.
MathieuJ4RecognitionApplication.FullCubicCentralizer applies every result
to the original Mathieu hypotheses without additional premises.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open LocalGeometry Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e))
noncomputable def fullCubicCentralizer : Subgroup (centralizer z) :=
  Subgroup.centralizer (cubicSylowImage e X : Set (centralizer z))
noncomputable def fullCubicProjection : fullCubicCentralizer e X →* cubicCentralizer e X :=
  ((QuotientGroup.mk' (center (centralizer z))).comp (fullCubicCentralizer e X).subtype).codRestrict
    (cubicCentralizer e X) (fun c => (cubicCentralizer_map_centerQuotient h e X).le
      (mem_map_of_mem _ c.property))
include h

/-- The projection is the original map H → H/Z(H), restricted to C_H(X). -/
@[simp] theorem fullCubicProjection_apply (c : fullCubicCentralizer e X) :
    (fullCubicProjection h e X c : CenterQuotient (z := z)) =
      QuotientGroup.mk' (center (centralizer z)) c.val := rfl

theorem fullCubicProjection_surjective : Function.Surjective (fullCubicProjection h e X) := by
  intro b
  obtain ⟨c,hc,he⟩ := (cubicCentralizer_map_centerQuotient h e X).ge b.property
  exact ⟨⟨c,hc⟩,Subtype.ext he⟩
/-- The full cubic centralizer modulo the original marker line is 3.M22. -/
noncomputable def fullCubicTripleQuotientEquiv :
    (fullCubicCentralizer e X ⧸ (fullCubicProjection h e X).ker) ≃* M22TripleCover :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (fullCubicProjection_surjective h e X)).trans
    (cubicCentralizerTripleEquiv h e X)

theorem fullCubicProjection_ker : (fullCubicProjection h e X).ker =
    (center (centralizer z)).subgroupOf (fullCubicCentralizer e X) := by
  ext c
  change fullCubicProjection h e X c = 1 ↔ c.val ∈ center (centralizer z)
  rw [←QuotientGroup.eq_one_iff c.val]
  exact Subtype.ext_iff

theorem fullCubicProjection_kernel_card : Nat.card (fullCubicProjection h e X).ker = 2 := by
  rw [fullCubicProjection_ker]
  have hle : center (centralizer z) ≤ fullCubicCentralizer e X := center_le_centralizer _
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
  exact centralizer_center_card h

theorem fullCubicProjection_kernel_central :
    (fullCubicProjection h e X).ker ≤ center (fullCubicCentralizer e X) := by
  rw [fullCubicProjection_ker]
  intro c hc
  exact mem_center_iff.mpr (fun d => Subtype.ext (mem_center_iff.mp hc d.val))

theorem fullCubicCentralizer_card : Nat.card (fullCubicCentralizer e X) = 2661120 := by
  have hh := (fullCubicProjection h e X).ker.card_mul_index
  rw [fullCubicProjection_kernel_card,index_ker,
    MonoidHom.range_eq_top.mpr (fullCubicProjection_surjective h e X),card_top,
    Nat.card_congr (cubicCentralizerTripleEquiv h e X).toEquiv,M22TripleCover.card] at hh
  exact hh.symm

private theorem cubicImage_le_fullCenter : cubicSylowImage e X ≤
    (center (fullCubicCentralizer e X)).map (fullCubicCentralizer e X).subtype := by
  have hc : Nat.card (cubicSylowImage e X) = 3 := by
    rw [cubicSylowImage,card_map_of_injective (CubicLift.subgroup e).subtype_injective,
      cubicSylow_card e h X]
  let : IsCyclic (cubicSylowImage e X) := isCyclic_of_prime_card hc
  intro x hx
  have hxC : x ∈ fullCubicCentralizer e X := by
    intro y hy
    exact congrArg Subtype.val (mul_comm' (⟨y,hy⟩ : cubicSylowImage e X) ⟨x,hx⟩)
  exact ⟨⟨x,hxC⟩,mem_center_iff.mpr (fun c => Subtype.ext (c.property x hx).symm),rfl⟩

omit h in
private theorem planeCenter_le_fullCenter : center (centralizer z) ≤
    (center (fullCubicCentralizer e X)).map (fullCubicCentralizer e X).subtype := by
  intro x hx
  exact ⟨⟨x,center_le_centralizer _ hx⟩,
    mem_center_iff.mpr (fun c => Subtype.ext (mem_center_iff.mp hx c.val)),rfl⟩

theorem fullCubicProjection_comap_center :
    (center (cubicCentralizer e X)).comap (fullCubicProjection h e X) =
      center (fullCubicCentralizer e X) := by
  apply le_antisymm
  · intro c hc
    have hm : (QuotientGroup.mk' (center (centralizer z))) c.val ∈
        (cubicSylowImage e X).map (QuotientGroup.mk' (center (centralizer z))) := by
      rw [←cubicCentralizer_center_image h e X]
      exact mem_map_of_mem (cubicCentralizer e X).subtype (x := fullCubicProjection h e X c) hc
    obtain ⟨x,hx,he⟩ := hm
    have hk : c.val*x⁻¹ ∈ center (centralizer z) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (center (centralizer z))) (c.val*x⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hm' : c.val ∈ (center (fullCubicCentralizer e X)).map
        (fullCubicCentralizer e X).subtype := by
      simpa only [inv_mul_cancel_right] using
        ((center (fullCubicCentralizer e X)).map (fullCubicCentralizer e X).subtype).mul_mem
          (planeCenter_le_fullCenter e X hk) (cubicImage_le_fullCenter h e X hx)
    obtain ⟨y,hy,he⟩ := hm'
    exact (Subtype.ext he : y = c) ▸ hy
  · intro c hc
    apply mem_center_iff.mpr
    intro b
    obtain ⟨d,rfl⟩ := fullCubicProjection_surjective h e X b
    exact (map_mul _ d c).symm.trans
      ((congrArg (fullCubicProjection h e X) (mem_center_iff.mp hc d)).trans (map_mul _ c d))

theorem fullCubicCentralizer_center_image :
    (center (fullCubicCentralizer e X)).map (fullCubicCentralizer e X).subtype =
      cubicSylowImage e X ⊔ center (centralizer z) := by
  apply le_antisymm
  · rintro x ⟨c,hc,rfl⟩
    have hm : (QuotientGroup.mk' (center (centralizer z))) c.val ∈
        (cubicSylowImage e X).map (QuotientGroup.mk' (center (centralizer z))) := by
      rw [←cubicCentralizer_center_image h e X]
      have hc' := (fullCubicProjection_comap_center h e X).ge hc
      exact mem_map_of_mem (cubicCentralizer e X).subtype (x := fullCubicProjection h e X c) hc'
    obtain ⟨x,hx,he⟩ := hm
    have hk : c.val*x⁻¹ ∈ center (centralizer z) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (center (centralizer z))) (c.val*x⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    simpa only [inv_mul_cancel_right,Subgroup.subtype_apply] using
      (cubicSylowImage e X ⊔ center (centralizer z)).mul_mem
        ((show center (centralizer z) ≤ cubicSylowImage e X ⊔ center (centralizer z) from le_sup_right) hk)
        ((show cubicSylowImage e X ≤ cubicSylowImage e X ⊔ center (centralizer z) from le_sup_left) hx)
  · exact sup_le (cubicImage_le_fullCenter h e X) (planeCenter_le_fullCenter e X)

noncomputable def fullCubicSimpleProjection : fullCubicCentralizer e X →* M22 :=
  (innerProjection e).comp ((cubicCentralizerProjection h e X).comp (fullCubicProjection h e X))
/-- The simple projection uses the SAME original cubic automorphism marking. -/
theorem fullCubicSimpleProjection_conj (c : fullCubicCentralizer e X) :
    MulAut.conj (fullCubicSimpleProjection h e X c) =
      e.projection (QuotientGroup.mk' (core z) c.val) :=
  innerProjection_conj e _

theorem fullCubicSimpleProjection_surjective : Function.Surjective (fullCubicSimpleProjection h e X) :=
  (innerProjection_surjective e).comp ((cubicCentralizerProjection_surjective h e X).comp
    (fullCubicProjection_surjective h e X))

omit h in
private theorem innerProjection_ker_eq_center : (innerProjection e).ker = center (innerPreimage e) := by
  apply le_antisymm (innerProjection_kernel_central e)
  intro c hc
  change innerProjection e c = 1
  apply mem_bot.mp
  rw [←m22_center_eq_bot]
  apply mem_center_iff.mpr
  intro a
  obtain ⟨b,rfl⟩ := innerProjection_surjective e a
  exact (map_mul _ b c).symm.trans
    ((congrArg (innerProjection e) (mem_center_iff.mp hc b)).trans (map_mul _ c b))

theorem fullCubicSimpleProjection_ker : (fullCubicSimpleProjection h e X).ker =
    center (fullCubicCentralizer e X) := by
  rw [fullCubicSimpleProjection,←MonoidHom.comap_ker,innerProjection_ker_eq_center e,←comap_comap]
  have he : (center (innerPreimage e)).comap (cubicCentralizerProjection h e X) =
      center (cubicCentralizer e X) := by
    ext c
    change cubicCentralizerEquiv h e X c ∈ center (innerPreimage e) ↔ c ∈ center (cubicCentralizer e X)
    constructor
    · intro hc
      apply mem_center_iff.mpr
      intro b
      apply (cubicCentralizerEquiv h e X).injective
      simp only [map_mul]
      exact mem_center_iff.mp hc _
    · intro hc
      apply mem_center_iff.mpr
      intro b
      obtain ⟨a,rfl⟩ := (cubicCentralizerEquiv h e X).surjective b
      rw [←map_mul,←map_mul,mem_center_iff.mp hc a]
  rw [he,fullCubicProjection_comap_center]

/-- The central quotient of C_H(X), retaining the original map to M22. -/
noncomputable def fullCubicCentralQuotientEquiv :
    (fullCubicCentralizer e X ⧸ center (fullCubicCentralizer e X)) ≃* M22 :=
  (QuotientGroup.quotientMulEquivOfEq (fullCubicSimpleProjection_ker h e X).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (fullCubicSimpleProjection_surjective h e X))

theorem fullCubicCentralizer_center_card : Nat.card (center (fullCubicCentralizer e X)) = 6 := by
  have hh := (center (fullCubicCentralizer e X)).card_mul_index
  change _ * Nat.card (fullCubicCentralizer e X ⧸ center (fullCubicCentralizer e X)) = _ at hh
  rw [Nat.card_congr (fullCubicCentralQuotientEquiv h e X).toEquiv,m22_order,
    fullCubicCentralizer_card h e X] at hh
  omega

noncomputable def fullCubicDerivedCover : PerfectCentralCovering.Cover
    (_root_.commutator (fullCubicCentralizer e X)) (cubicCentralizer e X) := by
  let := cubicCentralizer_quasisimple h e X
  exact CentralExtension.derivedCover (fullCubicProjection h e X)
    (fullCubicProjection_surjective h e X) (fullCubicProjection_kernel_central h e X)

theorem fullCubicDerived_quasisimple : IsQuasisimple (_root_.commutator (fullCubicCentralizer e X)) := by
  let := cubicCentralizer_quasisimple h e X
  exact (fullCubicDerivedCover h e X).isQuasisimple

/-- The actual layer upstairs is the quasisimple derived subgroup. -/
theorem fullCubicCentralizer_layer : componentLayer (fullCubicCentralizer e X) =
    _root_.commutator (fullCubicCentralizer e X) := by
  apply le_antisymm
  · apply sSup_le
    intro K hK
    let := hK.2
    rw [←commutator_eq_self (H := K)]
    exact commutator_mono le_top le_top
  · exact le_sSup ⟨(inferInstance : (_root_.commutator (fullCubicCentralizer e X)).Normal).isSubnormal,
      fullCubicDerived_quasisimple h e X⟩

theorem fullCubicDerived_index_dvd_two : (_root_.commutator (fullCubicCentralizer e X)).index ∣ 2 := by
  let := cubicCentralizer_quasisimple h e X
  have hs := CentralExtension.ker_sup_commutator_eq_top_of_surjective
    (fullCubicProjection h e X) (fullCubicProjection_surjective h e X)
  have hd := relIndex_dvd_card (_root_.commutator (fullCubicCentralizer e X)) (fullCubicProjection h e X).ker
  rw [←relIndex_sup_right,hs,relIndex_top_right,fullCubicProjection_kernel_card h e X] at hd
  exact hd

/-- The original marker, inside the full cubic centralizer. -/
def fullCubicMarker : fullCubicCentralizer e X :=
  ⟨⟨z,mem_centralizer_singleton_iff.mpr rfl⟩,fun x _ =>
    Subtype.ext (mem_centralizer_singleton_iff.mp x.property)⟩

theorem fullCubicMarker_order : orderOf (fullCubicMarker e X) = 2 := by
  rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe]
  exact h.involution

theorem fullCubicProjection_ker_zpowers : (fullCubicProjection h e X).ker =
    zpowers (fullCubicMarker e X) := by
  apply Eq.symm
  apply eq_of_le_of_card_ge (zpowers_le.mpr ?_)
  · rw [fullCubicProjection_kernel_card h e X,Nat.card_zpowers,fullCubicMarker_order h e X]
  · rw [fullCubicProjection_ker]
    exact mem_center_iff.mpr (fun c => Subtype.ext (mem_centralizer_singleton_iff.mp c.property))

/-- The exact source obstruction before the central involution is discharged. -/
theorem fullCubicCentralizer_layer_eq_top_iff :
    componentLayer (fullCubicCentralizer e X) = ⊤ ↔
      fullCubicMarker e X ∈ _root_.commutator (fullCubicCentralizer e X) := by
  rw [fullCubicCentralizer_layer h e X]
  constructor
  · intro ht
    rw [ht]
    trivial
  · intro hz
    let := cubicCentralizer_quasisimple h e X
    have hs := CentralExtension.ker_sup_commutator_eq_top_of_surjective
      (fullCubicProjection h e X) (fullCubicProjection_surjective h e X)
    rw [fullCubicProjection_ker_zpowers,sup_eq_right.mpr (zpowers_le.mpr hz)] at hs
    exact hs

/-- The normalizer is taken inside H, before either quotient is formed. -/
noncomputable def fullCubicNormalizer : Subgroup (centralizer z) :=
  normalizer (cubicSylowImage e X : Set (centralizer z))

private theorem core_inf_cubicImage : core z ⊓ cubicSylowImage e X = ⊥ := by
  have hh := congrArg (map (CubicLift.subgroup e).subtype)
    (core_isComplement_cubicSylow e h X).disjoint.eq_bot
  rw [Subgroup.map_inf _ _ _ (CubicLift.subgroup e).subtype_injective,map_subgroupOf_eq_of_le (CubicLift.core_le e),
    Subgroup.map_bot] at hh
  exact hh

theorem fullCubicNormalizer_core_intersection : core z ⊓ fullCubicNormalizer e X =
    center (centralizer z) := by
  apply le_antisymm
  · intro n hn
    have hc : n ∈ fullCubicCentralizer e X := by
      intro a ha
      have hx : n*a*n⁻¹*a⁻¹ ∈ cubicSylowImage e X :=
        (cubicSylowImage e X).mul_mem ((mem_normalizer_iff.mp hn.2 a).mp ha)
          ((cubicSylowImage e X).inv_mem ha)
      have hy : n*a*n⁻¹*a⁻¹ ∈ core z := by
        have hh := (core z).mul_mem hn.1
          ((inferInstance : (core z).Normal).conj_mem n⁻¹ ((core z).inv_mem hn.1) a)
        simpa only [mul_assoc] using hh
      have he : n*a*n⁻¹*a⁻¹ = 1 := (core_inf_cubicImage h e X).le ⟨hy,hx⟩
      exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp he)).symm
    have hz : (⟨n,hn.1⟩ : core z) ∈ center (core z) := (core_cubic_centralizer h e X).le hc
    rw [←core_center_eq_centralizer_center h]
    exact mem_map_of_mem (core z).subtype hz
  · exact le_inf (centralizer_center_le_core h) (center_le_normalizer _)

noncomputable def fullCubicNormalizerProjection : fullCubicNormalizer e X →* centralizer z ⧸ core z :=
  (QuotientGroup.mk' (core z)).comp (fullCubicNormalizer e X).subtype

theorem fullCubicNormalizerProjection_surjective :
    Function.Surjective (fullCubicNormalizerProjection e X) := by
  intro b
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (core z) b
  obtain ⟨q,n,he⟩ := exists_core_mul_cubicNormalizer e h X g
  refine ⟨n,?_⟩
  change QuotientGroup.mk' (core z) n.val = QuotientGroup.mk' (core z) g
  have hq : QuotientGroup.mk' (core z) q.val = 1 := (QuotientGroup.eq_one_iff q.val).mpr q.property
  rw [←he,map_mul,hq,one_mul]

theorem fullCubicNormalizerProjection_ker : (fullCubicNormalizerProjection e X).ker =
    (center (centralizer z)).subgroupOf (fullCubicNormalizer e X) := by
  ext n
  change (QuotientGroup.mk' (core z)) n.val = 1 ↔ n.val ∈ center (centralizer z)
  change (n.val : centralizer z ⧸ core z) = 1 ↔ n.val ∈ center (centralizer z)
  rw [QuotientGroup.eq_one_iff]
  exact ⟨fun hn => (fullCubicNormalizer_core_intersection h e X).le ⟨hn,n.property⟩,
    fun hn => centralizer_center_le_core h hn⟩

theorem fullCubicNormalizerProjection_kernel_card : Nat.card (fullCubicNormalizerProjection e X).ker = 2 := by
  rw [fullCubicNormalizerProjection_ker h e X]
  have hl : center (centralizer z) ≤ fullCubicNormalizer e X := center_le_normalizer _
  rw [Nat.card_congr (subgroupOfEquivOfLe hl).toEquiv,centralizer_center_card h]

noncomputable def fullCubicNormalizerQuotientEquiv :
    (fullCubicNormalizer e X ⧸ (center (centralizer z)).subgroupOf (fullCubicNormalizer e X)) ≃*
      (centralizer z ⧸ core z) :=
  (QuotientGroup.quotientMulEquivOfEq (fullCubicNormalizerProjection_ker h e X).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (fullCubicNormalizerProjection_surjective h e X))

@[simp] theorem fullCubicNormalizerQuotientEquiv_mk (n : fullCubicNormalizer e X) :
    fullCubicNormalizerQuotientEquiv h e X (QuotientGroup.mk' _ n) =
      QuotientGroup.mk' (core z) n.val := rfl

theorem fullCubicNormalizer_card : Nat.card (fullCubicNormalizer e X) = 5322240 := by
  have hh := (fullCubicNormalizerProjection e X).ker.card_mul_index
  rw [fullCubicNormalizerProjection_kernel_card h e X,index_ker,
    MonoidHom.range_eq_top.mpr (fullCubicNormalizerProjection_surjective h e X),card_top,
    coreQuotient_card h] at hh
  exact hh.symm

/-- The full centralizer has index two in the original normalizer; this is
not yet a choice of an involution in its other coset. -/
theorem fullCubicCentralizer_normalizer_index :
    (fullCubicCentralizer e X).relIndex (fullCubicNormalizer e X) = 2 := by
  have hh := ((fullCubicCentralizer e X).subgroupOf (fullCubicNormalizer e X)).card_mul_index
  have hl : fullCubicCentralizer e X ≤ fullCubicNormalizer e X := centralizer_le_normalizer _
  rw [Nat.card_congr (subgroupOfEquivOfLe hl).toEquiv,
    fullCubicCentralizer_card h e X,fullCubicNormalizer_card h e X] at hh
  change 2661120 * (fullCubicCentralizer e X).relIndex (fullCubicNormalizer e X) = 5322240 at hh
  omega
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
