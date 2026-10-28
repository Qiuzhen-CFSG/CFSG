module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.DeletedPointCentralizer
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.AmbientAction
public import Theory.GroupAction.NormalizerFixedCentralizer
public import Theory.GroupAction.AutomorphismFixedResidualTransport

/-!
# Marked deleted-point centralizers in an ambient finite group

A normalizing element whose action is the sixth deleted-coordinate involution
has centralizer in the marked A₆ block projecting onto A₅ with literal kernel
A. When the full normalizer acts as every automorphism of the block, its
centralizer projects onto S₅ with literal kernel C_G(A), and has order 3840.
Both quotients retain the original ambient subgroup inclusions. The proofs
transport the marked actions and then identify the kernels of the coordinate
projections; they do not choose a second block marking.

Source: Aschbacher–Smith 14.3.20, second paragraph, printed pp.997–998.
-/

public section
namespace BinaryPermutation.SixNaturalSplit
open Subgroup SemidirectProduct
variable {G:Type*} [Group G]
variable (K A:Subgroup G) (hAK:A≤K) (f:K≃*Model)
variable (hA:(A.subgroupOf K).map f.toMonoidHom=translations)
variable (d:normalizer (K:Set G))
variable (hmark:MulAut.congr f (K.normalizerMonoidHom d)=pointAutomorphism)

include hmark in
theorem pointAction_compatible (x:K) :
    f (K.normalizerMonoidHom d x)=pointAutomorphism (f x) := by
  have he:=congrArg (fun a:MulAut Model=>a (f x)) hmark
  change f ((K.normalizerMonoidHom d) (f.symm (f x)))=_ at he
  simpa only [f.symm_apply_apply] using he

noncomputable def pointBlockCentralizerEquiv :
    (K⊓centralizer ({(d:G)}:Set G):Subgroup G)≃*pointAutomorphism.fixedSubgroup :=
  (normalizerFixedEquivCentralizer K d).symm.trans
    (MulAut.fixedSubgroupEquivOfCompatible f (K.normalizerMonoidHom d)
      pointAutomorphism (pointAction_compatible K f d hmark))

theorem pointBlockCentralizerEquiv_apply
    (x:(K⊓centralizer ({(d:G)}:Set G):Subgroup G)) :
    (pointBlockCentralizerEquiv K f d hmark x:Model)=f ⟨x,x.property.1⟩ := by
  exact MulAut.fixedSubgroupEquivOfCompatible_apply f _ _ _ _

noncomputable def pointBlockProjection :
    (K⊓centralizer ({(d:G)}:Set G):Subgroup G)→*pointActor :=
  pointFixedProjection.comp (pointBlockCentralizerEquiv K f d hmark).toMonoidHom

theorem pointBlockProjection_surjective :
    Function.Surjective (pointBlockProjection K f d hmark) :=
  pointFixedProjection_surjective.comp (pointBlockCentralizerEquiv K f d hmark).surjective

include hA in
theorem pointBlockProjection_ker :
    (pointBlockProjection K f d hmark).ker=
      A.subgroupOf (K⊓centralizer ({(d:G)}:Set G)) := by
  ext x
  change pointFixedProjection (pointBlockCentralizerEquiv K f d hmark x)=1 ↔ (x:G)∈A
  rw [←MonoidHom.mem_ker,pointFixedProjection_ker]
  change (pointBlockCentralizerEquiv K f d hmark x:Model)∈translations ↔ (x:G)∈A
  rw [pointBlockCentralizerEquiv_apply]
  rw [←hA,mem_map_equiv]
  simp only [MulEquiv.symm_apply_apply,mem_subgroupOf]

include hA hmark in
theorem pointBlockCentralizer_quotient :
    ∃ hnormal:(A.subgroupOf (K⊓centralizer ({(d:G)}:Set G))).Normal,
      let :=hnormal
      Nonempty (((K⊓centralizer ({(d:G)}:Set G):Subgroup G) ⧸
        A.subgroupOf (K⊓centralizer ({(d:G)}:Set G)))≃*alternatingGroup (Fin 5)) := by
  have hk:=pointBlockProjection_ker K A f hA d hmark
  have hn:(A.subgroupOf (K⊓centralizer ({(d:G)}:Set G))).Normal :=
    hk ▸ (pointBlockProjection K f d hmark).normal_ker
  let :=hn
  refine ⟨hn,⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (pointBlockProjection K f d hmark)
      (pointBlockProjection_surjective K f d hmark)).trans pointActorEquiv)

variable (hN:normalizer (action.range:Set (MulAut Vector))=(naturalMulAction (Fin 6)).range)
variable (hb:Function.Bijective K.normalizerMonoidHom)

noncomputable def pointNormalizerEquiv : normalizer (K:Set G)≃*AutomorphismModel :=
  (MulEquiv.ofBijective K.normalizerMonoidHom hb).trans
    ((MulAut.congr f).trans (automorphismEquiv hN))

include hmark in
theorem pointNormalizerEquiv_point :
    pointNormalizerEquiv K f hN hb d=deletedPointElement := by
  change automorphismEquiv hN (MulAut.congr f (K.normalizerMonoidHom d))=_
  rw [hmark,automorphismEquiv_pointAutomorphism]

include hAK hA in
theorem pointNormalizerEquiv_right_eq_one (x:normalizer (K:Set G)) :
    (pointNormalizerEquiv K f hN hb x).right=1 ↔ (x:G)∈centralizer (A:Set G) := by
  change (automorphismEquiv hN ((MulAut.congr f) (K.normalizerMonoidHom x))).right=1 ↔ _
  rw [automorphismEquiv_right_eq_one,←fixingSubgroup_map (A.subgroupOf K) f hA,
    mem_map_equiv,MulEquiv.symm_apply_apply,mem_fixingSubgroup_iff]
  constructor
  · intro hx a ha
    have he := congrArg Subtype.val (hx (⟨a,hAK ha⟩:K) ha)
    change (x:G)*a*(x:G)⁻¹=a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hx a ha
    apply Subtype.ext
    change (x:G)*(a:G)*(x:G)⁻¹=(a:G)
    rw [←hx (a:G) ha,mul_assoc,mul_inv_cancel,mul_one]

private def relativePointCentralizerEquiv {H:Type*} [Group H]
    (L:Subgroup G) (e:L≃*H) (z:L) (u:H) (he:e z=u) :
    (L⊓centralizer ({(z:G)}:Set G):Subgroup G)≃*centralizer ({u}:Set H) where
  toFun x:=⟨e ⟨x,x.property.1⟩,by
    apply mem_centralizer_singleton_iff.mpr
    rw [←he,←map_mul,←map_mul]
    apply congrArg e
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2)⟩
  invFun y:=⟨(e.symm y:G),(e.symm y).property,by
    apply mem_centralizer_singleton_iff.mpr
    have hh:e.symm y*z=z*e.symm y := by
      apply e.injective
      rw [map_mul,map_mul,e.apply_symm_apply,he]
      exact mem_centralizer_singleton_iff.mp y.property
    exact congrArg Subtype.val hh⟩
  left_inv x:=by
    apply Subtype.ext
    exact congrArg (fun t:L=>(t:G)) (e.symm_apply_apply (⟨x,x.property.1⟩:L))
  right_inv y:=Subtype.ext (e.apply_symm_apply y)
  map_mul' x y:=Subtype.ext (e.map_mul (⟨x,x.property.1⟩:L) (⟨y,y.property.1⟩:L))

noncomputable def pointNormalizerCentralizerEquiv :
    (normalizer (K:Set G)⊓centralizer ({(d:G)}:Set G):Subgroup G)≃*deletedPointCentralizer :=
  relativePointCentralizerEquiv (normalizer (K:Set G))
    (pointNormalizerEquiv K f hN hb) d deletedPointElement
    (pointNormalizerEquiv_point K f d hmark hN hb)

include hmark hN hb in
theorem pointNormalizerCentralizer_card :
    Nat.card (normalizer (K:Set G)⊓centralizer ({(d:G)}:Set G):Subgroup G)=3840 :=
  (Nat.card_congr (pointNormalizerCentralizerEquiv K f d hmark hN hb).toEquiv).trans
    deletedPointCentralizer_card

noncomputable def pointNormalizerCentralizerProjection :
    (normalizer (K:Set G)⊓centralizer ({(d:G)}:Set G):Subgroup G)→*pointSymmetric :=
  deletedPointCentralizerProjection.comp
    (pointNormalizerCentralizerEquiv K f d hmark hN hb).toMonoidHom

theorem pointNormalizerCentralizerProjection_surjective :
    Function.Surjective (pointNormalizerCentralizerProjection K f d hmark hN hb) :=
  deletedPointCentralizerProjection_surjective.comp
    (pointNormalizerCentralizerEquiv K f d hmark hN hb).surjective

include hAK hA in
theorem pointNormalizerCentralizerProjection_ker :
    (pointNormalizerCentralizerProjection K f d hmark hN hb).ker=
      (centralizer (A:Set G)).subgroupOf
        (normalizer (K:Set G)⊓centralizer ({(d:G)}:Set G)) := by
  ext x
  change deletedPointCentralizerProjection
    (pointNormalizerCentralizerEquiv K f d hmark hN hb x)=1 ↔ (x:G)∈centralizer (A:Set G)
  rw [←MonoidHom.mem_ker,deletedPointCentralizerProjection_ker]
  change (pointNormalizerEquiv K f hN hb ⟨x,x.property.1⟩).right=1 ↔ _
  exact pointNormalizerEquiv_right_eq_one K A hAK f hA hN hb _

include hAK hA hmark hN hb in
theorem pointNormalizerCentralizer_quotient :
    let C:=normalizer (K:Set G)⊓centralizer ({(d:G)}:Set G)
    ∃ hnormal:((centralizer (A:Set G)).subgroupOf C).Normal,
      let :=hnormal
      Nonempty ((C ⧸ (centralizer (A:Set G)).subgroupOf C)≃*Equiv.Perm (Fin 5)) := by
  intro C
  have hk:=pointNormalizerCentralizerProjection_ker K A hAK f hA d hmark hN hb
  have hn:((centralizer (A:Set G)).subgroupOf C).Normal :=
    hk ▸ (pointNormalizerCentralizerProjection K f d hmark hN hb).normal_ker
  let :=hn
  refine ⟨hn,⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective
      (pointNormalizerCentralizerProjection K f d hmark hN hb)
      (pointNormalizerCentralizerProjection_surjective K f d hmark hN hb)).trans pointSymmetricEquiv)

end BinaryPermutation.SixNaturalSplit
