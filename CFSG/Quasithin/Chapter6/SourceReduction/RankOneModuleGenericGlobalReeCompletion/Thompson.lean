module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.RootExhaustion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeSmallCompletion.OrderRecognition
public import Theory.GroupTheory.TwoInvolutionClassOrder

/-!
# Thompson order comparison for the prepared general Ree row

Every mixed pair of involutions centralizes its canonical half-order power.
The full endpoint maps therefore identify the two Thompson fibers once their
representatives' entire centralizers lie in those endpoints. Native exhaustion
and the proved cross-endpoint fusion match both ambient involution classes.
Thompson's formula gives equality with the SAME full extension, including its
odd field factor. Its full-normalizer small-completion recognizer then proves
generation and identifies the ambient simple group with the native Ree model.

The only additional source obligation is F.4.42 short-centralizer containment
for the supplied marker. The companion Recognition module discharges it from
the original preparation. No order, Weyl relation or recognition premise is
assumed here. All positive parameters, including q=8, are retained.
Source: Aschbacher--Smith F.4.43--44, printed p.296, and 5.3.1--4,
printed pp.658--659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open TwoInvolutionClassOrder
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
open ReeF4 ReeF4.Parabolics ReeF4.EvenInvolutionGeometry

private theorem conj_order {X : Type*} [Group X] {x y : X}
    (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

private theorem halfOrder_injective {X Q : Type*} [Group X] [Group Q]
    (f : Q →* X) (hf : Function.Injective f) (a b : Q) :
    halfOrder (f a) (f b) = f (halfOrder a b) := by
  simp only [halfOrder_def,←map_mul,orderOf_injective f hf,map_pow]

private abbrev LocalFiber {X Q : Type*} [Group X] [Group Q]
    (f : Q →* X) (z v : X) (u : Q) :=
  {p : Q × Q // orderOf p.1=2 ∧ orderOf p.2=2 ∧
    IsConj z (f p.1) ∧ IsConj v (f p.2) ∧ halfOrder p.1 p.2=u}

private def localFiberMap {X Q : Type*} [Group X] [Group Q]
    (f : Q →* X) (hf : Function.Injective f) (z v : X) (u : Q) :
    LocalFiber f z v u → Fiber z v (f u) := fun p =>
  ⟨(f p.val.1,f p.val.2),p.property.2.2.1,p.property.2.2.2.1,
    (halfOrder_injective f hf _ _).trans (congrArg f p.property.2.2.2.2)⟩

private theorem localFiberMap_bijective {X Q : Type*} [Group X] [Finite X] [Group Q]
    (f : Q →* X) (hf : Function.Injective f) (z v : X) (u : Q)
    (hz : orderOf z=2) (hv : orderOf v=2) (hn : ¬ IsConj z v)
    (hC : centralizer ({f u} : Set X) ≤ f.range) :
    Function.Bijective (localFiberMap f hf z v u) := by
  constructor
  · intro p q he
    apply Subtype.ext
    exact Prod.ext (hf (congrArg (fun t => t.val.1) he))
      (hf (congrArg (fun t => t.val.2) he))
  · intro p
    have ha : orderOf p.val.1=2 := (conj_order p.property.1).symm.trans hz
    have hb : orderOf p.val.2=2 := (conj_order p.property.2.1).symm.trans hv
    have hm := fiber_mem_centralizer hz hv hn p
    obtain ⟨a,hea⟩ := hC hm.1
    obtain ⟨b,heb⟩ := hC hm.2
    refine ⟨⟨(a,b),?_,?_,?_,?_,?_⟩,?_⟩
    · exact (orderOf_injective f hf a).symm.trans (hea ▸ ha)
    · exact (orderOf_injective f hf b).symm.trans (heb ▸ hb)
    · exact hea ▸ p.property.1
    · exact heb ▸ p.property.2.1
    · apply hf
      rw [←halfOrder_injective f hf,hea,heb]
      exact p.property.2.2
    · exact Subtype.ext (Prod.ext hea heb)

private theorem kappa_transport {X Y Q : Type*}
    [Group X] [Finite X] [Group Y] [Finite Y] [Group Q]
    (f : Q →* X) (hf : Function.Injective f)
    (g : Q →* Y) (hg : Function.Injective g) (z v : X) (z' v' : Y) (u : Q)
    (hz : orderOf z=2) (hv : orderOf v=2)
    (hz' : orderOf z'=2) (hv' : orderOf v'=2)
    (hnf : ¬ IsConj z v) (hng : ¬ IsConj z' v')
    (hX : centralizer ({f u} : Set X) ≤ f.range)
    (hY : centralizer ({g u} : Set Y) ≤ g.range)
    (hfusion : ∀ a : Q, orderOf a=2 →
      (IsConj z (f a) ↔ IsConj z' (g a)) ∧
      (IsConj v (f a) ↔ IsConj v' (g a))) :
    kappa z v (f u) = kappa z' v' (g u) := by
  have he : LocalFiber f z v u ≃ LocalFiber g z' v' u :=
    Equiv.subtypeEquivRight (by
      intro p
      constructor
      · rintro ⟨ha,hb,hza,hvb,hu⟩
        exact ⟨ha,hb,(hfusion p.1 ha).1.mp hza,(hfusion p.2 hb).2.mp hvb,hu⟩
      · rintro ⟨ha,hb,hza,hvb,hu⟩
        exact ⟨ha,hb,(hfusion p.1 ha).1.mpr hza,(hfusion p.2 hb).2.mpr hvb,hu⟩)
  have hc := Nat.card_congr
    ((Equiv.ofBijective _ (localFiberMap_bijective f hf z v u hz hv hnf hX)).symm.trans
      (he.trans (Equiv.ofBijective _
        (localFiberMap_bijective g hg z' v' u hz' hv' hng hY))))
  simpa only [kappa_def,Fiber,halfOrder_def] using hc

private theorem centralizer_card_transport {G E : Type*} [Group G] [Group E]
    (P : Subgroup G) (f : P →* E) (hf : Function.Injective f) (u : P)
    (hC : centralizer ({u.val} : Set G) ≤ P)
    (hmap : ((centralizer ({u.val} : Set G)).subgroupOf P).map f =
      centralizer ({f u} : Set E)) :
    Nat.card (centralizer ({u.val} : Set G)) =
      Nat.card (centralizer ({f u} : Set E)) := by
  rw [←hmap,card_map_of_injective hf]
  exact (Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv).symm

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ)
  (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
include d h hH hp he

/-- F.4.43 for the same constructed extension, conditional on the independently
owned F.4.42 short-centralizer containment. The short marker and its literal
local-centralizer map may be supplied by the existing extremal selection. -/
theorem Preparation.ree_order_eq_of_short_centralizer
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (t : Model m) (v : normalizer (L : Set G))
    (ht : IsShortRootInvolution t)
    (hmark : D.leftToCarrier v = D.extension.baseHom t)
    (hmap : ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
      D.leftToCarrier = centralizer ({D.extension.baseHom t} : Set D.extension.carrier))
    (hC : centralizer ({v.val} : Set G) ≤ normalizer (L : Set G)) :
    Nat.card G = Nat.card D.extension.carrier := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  have hi : Function.Injective D.extension.baseHom :=
    (MonoidHom.injective_codRestrict _ _ _).mpr (ReeF4.SmallCompletion.conj_injective m hm)
  have hvE : orderOf (D.leftToCarrier v) = 2 := by
    rw [hmark,orderOf_injective _ hi]
    exact orderOf_of_isShortRootInvolution ht
  have hvG : orderOf v.val = 2 := by
    rw [orderOf_injective _ D.leftToCarrier_injective,←Subgroup.orderOf_coe] at hvE
    exact hvE
  obtain ⟨z,hz,hz2,hCz⟩ := d.ree_right_center_involution h hH hp m he
  obtain ⟨z0,hz0,rfl⟩ := hz
  let zc : center (residual H) := ⟨z0,hz0⟩
  have hzc : orderOf zc = 2 := by
    rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe]
    exact hz2
  let zN : normalizer (residual H : Set G) :=
    ⟨z0.val,(residual H).le_normalizer z0.property⟩
  obtain ⟨tz,htz,hmz⟩ := d.ree_long_root_marking h hH hp m D zc hzc
  let ze : D.extension.family true := ⟨D.rightToCarrier zN,(D.full.right zN).property⟩
  let ve : D.extension.family false := ⟨D.leftToCarrier v,(D.full.left v).property⟩
  have hzE : orderOf ze.val = 2 := by
    rw [orderOf_injective D.rightToCarrier D.rightToCarrier_injective,←Subgroup.orderOf_coe]
    exact hz2
  have hnf : ¬ IsConj z0.val v.val := by
    have hh := d.ree_root_endpoint_nonfusion h hH hp m he D ze ve htz ht hmz.symm hmark.symm
    rw [D.endpointInverse_right,D.endpointInverse_left] at hh
    exact hh
  have hnE : ¬ IsConj ze.val ve.val := by
    intro hc
    have hh := d.ree_extension_involution_fusion h hp m D ze ve hzE hc
    rw [D.endpointInverse_right,D.endpointInverse_left] at hh
    exact hnf hh
  have hclassesE (x : D.extension.carrier) (hx : orderOf x = 2) :
      IsConj ze.val x ∨ IsConj ve.val x := by
    obtain ⟨a,ha,hax⟩ := GeneralReeFour.extension_involution_native D.extension hm x hx
    rw [←hax]
    rcases ReeF4.SourceCompletion.involution_root_classes m hm a ha with hlong | hshort
    · left
      change IsConj (D.rightToCarrier zN) (D.extension.baseHom a)
      rw [hmz]
      exact D.extension.baseHom.map_isConj (ReeF4.SourceCompletion.long_class_isConj htz hlong)
    · right
      change IsConj (D.leftToCarrier v) (D.extension.baseHom a)
      rw [hmark]
      exact D.extension.baseHom.map_isConj (ReeF4.SourceCompletion.short_class_isConj ht hshort)
  have hclassesG (x : G) (hx : orderOf x = 2) :
      IsConj z0.val x ∨ IsConj v.val x := by
    obtain ⟨y,a,_,ha,hxy,hym⟩ := d.ree_involution_native_representative h hH hp m he D x hx
    let yL := inclusion (show normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ≤
      normalizer (L : Set G) from inf_le_left) y
    let ye : D.extension.family false := ⟨D.leftToCarrier yL,(D.full.left yL).property⟩
    have hye : orderOf ye.val = 2 := by
      change orderOf (D.leftToCarrier yL) = 2
      rw [←D.middleToCarrier_left y,hym,orderOf_injective _ hi]
      exact ha
    rcases hclassesE ye.val hye with hh | hh
    · have hc := d.ree_extension_involution_fusion h hp m D ze ye hzE hh
      rw [D.endpointInverse_right,D.endpointInverse_left] at hc
      exact Or.inl (hc.trans hxy.symm)
    · have hc := d.ree_extension_involution_fusion h hp m D ve ye hvE hh
      rw [D.endpointInverse_left,D.endpointInverse_left] at hc
      exact Or.inr (hc.trans hxy.symm)
  have hlongmap := (d.ree_long_centralizer_comparison h hH hp m he D zc hzc).1
  change ((centralizer ({z0.val} : Set G)).subgroupOf
    (normalizer (residual H : Set G))).map D.rightToCarrier =
      centralizer ({D.rightToCarrier zN} : Set D.extension.carrier) at hlongmap
  have hshortmap : ((centralizer ({v.val} : Set G)).subgroupOf
      (normalizer (L : Set G))).map D.leftToCarrier =
      centralizer ({D.leftToCarrier v} : Set D.extension.carrier) := by
    rwa [hmark]
  have hzCount : kappa z0.val v.val z0.val = kappa ze.val ve.val ze.val := by
    apply kappa_transport (normalizer (residual H : Set G)).subtype
      (normalizer (residual H : Set G)).subtype_injective
      D.rightToCarrier D.rightToCarrier_injective z0.val v.val ze.val ve.val zN
      hz2 hvG hzE hvE hnf hnE
    · simpa only [range_subtype, subtype_apply] using hCz
    · rw [←hlongmap]
      exact map_le_range _ _
    · intro a ha
      have haE : orderOf (D.rightToCarrier a) = 2 :=
        (orderOf_injective _ D.rightToCarrier_injective a).trans ha
      let ae : D.extension.family true := ⟨D.rightToCarrier a,(D.full.right a).property⟩
      have hzF := d.ree_endpoint_involution_fusion_iff h hp m hH he D ze ae hzE haE
      have hvF := d.ree_endpoint_involution_fusion_iff h hp m hH he D ve ae hvE haE
      rw [D.endpointInverse_right,D.endpointInverse_right] at hzF
      rw [D.endpointInverse_left,D.endpointInverse_right] at hvF
      exact ⟨hzF,hvF⟩
  have hvCount : kappa z0.val v.val v.val = kappa ze.val ve.val ve.val := by
    apply kappa_transport (normalizer (L : Set G)).subtype
      (normalizer (L : Set G)).subtype_injective
      D.leftToCarrier D.leftToCarrier_injective z0.val v.val ze.val ve.val v
      hz2 hvG hzE hvE hnf hnE
    · simpa only [range_subtype, subtype_apply] using hC
    · rw [←hshortmap]
      exact map_le_range _ _
    · intro a ha
      have haE : orderOf (D.leftToCarrier a) = 2 :=
        (orderOf_injective _ D.leftToCarrier_injective a).trans ha
      let ae : D.extension.family false := ⟨D.leftToCarrier a,(D.full.left a).property⟩
      have hzF := d.ree_endpoint_involution_fusion_iff h hp m hH he D ze ae hzE haE
      have hvF := d.ree_endpoint_involution_fusion_iff h hp m hH he D ve ae hvE haE
      rw [D.endpointInverse_right,D.endpointInverse_left] at hzF
      rw [D.endpointInverse_left,D.endpointInverse_left] at hvF
      exact ⟨hzF,hvF⟩
  have hzCard := centralizer_card_transport _ D.rightToCarrier
    D.rightToCarrier_injective zN hCz hlongmap
  have hvCard := centralizer_card_transport _ D.leftToCarrier
    D.leftToCarrier_injective v hC hshortmap
  have hG := TwoInvolutionClassOrder.card_eq z0.val v.val hz2 hvG hnf hclassesG
  rw [hzCount,hvCount,hzCard,hvCard] at hG
  exact hG.trans (TwoInvolutionClassOrder.card_eq ze.val ve.val hzE hvE hnE hclassesE).symm

/-- The literal source F.4.42 containment is the only remaining geometric
input: Thompson's equality feeds the full-extension recognizer, proves that
both full normalizers generate G, and uses ambient simplicity to remove the
outer extension. Both comparison orientations and q=8 are retained. -/
theorem Preparation.ree_ambient_recognition_of_short_centralizer
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (t : Model m) (v : normalizer (L : Set G))
    (ht : IsShortRootInvolution t)
    (hmark : D.leftToCarrier v = D.extension.baseHom t)
    (hmap : ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
      D.leftToCarrier = centralizer ({D.extension.baseHom t} : Set D.extension.carrier))
    (hC : centralizer ({v.val} : Set G) ≤ normalizer (L : Set G)) :
    2*m+1 = n ∧ 0 < m ∧
      normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      Nat.card G = Nat.card D.extension.carrier ∧ Nonempty (G ≃* Model m) := by
  have horder := d.ree_order_eq_of_short_centralizer h hH hp m he D t v ht hmark hmap hC
  exact d.ree_full_normalizers_recognition_of_order_bound h hH hp m he D.extension
    (.inl D.full) horder.le

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
