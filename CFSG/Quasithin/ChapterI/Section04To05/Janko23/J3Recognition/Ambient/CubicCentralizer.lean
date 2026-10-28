module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.LocalActionFusion
public import Theory.SpecificGroups.MinusExtraspecial.CubicAction.NormalForm
public import Theory.SpecificGroups.MinusExtraspecial.CubicAction.FixedSubgroup
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicCentralizer
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicDihedralQuotient

/-!
# Dihedral involution centralizers in the actual cubic quotient

A nontrivial cubic automorphism of the marked minus-type extraspecial core
has fixed subgroup D₈. The self-centralizing cubic image in the actual A₅
quotient then gives C_H(s) = C_Q(s) × ⟨s⟩. Ambient involution conjugacy
transports this calculation simultaneously with s to every commuting
involution. Finally, unique involution lifting through the central cubic
identifies every involution centralizer in C_G(s)/⟨s⟩ with D₈.

The local cubic normal-form argument is adapted from the common H-type
calculation in `J2Recognition/SourceLocal/SourceOrbits/Representatives/SL23Local/CoreConstruction`.
Only `HTypeAt` is used here, followed by the J₃ one-class hypothesis;
the J₂ two-class seed and its global census are not inputs.

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Lemma 2.1(v) and the first part of Lemma 2.4, pp.493–495.
-/

@[expose] public noncomputable section
open Subgroup
open MinusExtraspecial.CubicAction
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The literal cubic conjugation on the original core has the standard normal form. -/
theorem cubic_core_coordinates (h : HTypeAt z) (s : involutionCentralizer z)
    (hs : orderOf s = 3) :
    ∃ e : localCore z ≃* MinusExtraspecial.Model,
      ∀ q : localCore z, e (MulAut.conjNormal s q) = cycle (e q) := by
  let Q := localCore z
  let b : MulAut Q := MulAut.conjNormal s
  have hs3 : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
  have hb3 : b ^ 3 = 1 := by
    change (MulAut.conjNormal s : MulAut Q) ^ 3 = 1
    rw [← map_pow, hs3, map_one]
  have hb : b ≠ 1 := by
    intro hb
    have hker : s ∈ (coreFrattiniAction z).ker := by
      change quotientAut (frattini Q) b = 1
      rw [hb, map_one]
    rw [h.coreFrattiniAction_kernel] at hker
    have hd := Q.orderOf_dvd_natCard hker
    rw [h.core_card, hs] at hd
    norm_num at hd
  let e : Q ≃* MinusExtraspecial.Model := h.core_equiv.some
  let a : MulAut MinusExtraspecial.Model := MulAut.congr e b
  have ha3 : a ^ 3 = 1 := by
    dsimp only [a]
    rw [← map_pow, hb3, map_one]
  have ha : a ≠ 1 := by
    intro hh
    apply hb
    exact (MulAut.congr e).injective (hh.trans (map_one _).symm)
  obtain ⟨f, hf⟩ := hasCubicNormalForm a ha3 ha
  exact ⟨e.trans f, fun q => by simpa [a, MulAut.congr] using hf (e q)⟩

/-- The fixed subgroup in the original core is the genuine dihedral group of order eight. -/
theorem cubic_core_fixed (h : HTypeAt z) (s : involutionCentralizer z)
    (hs : orderOf s = 3) :
    Nonempty ((localCore z ⊓ centralizer ({s} : Set (involutionCentralizer z)) :
      Subgroup (involutionCentralizer z)) ≃* DihedralGroup 4) := by
  obtain ⟨e, he⟩ := cubic_core_coordinates h s hs
  let Q := localCore z
  let i : MinusExtraspecial.Model →* involutionCentralizer z := Q.subtype.comp e.symm.toMonoidHom
  have hi : Function.Injective i := Q.subtype_injective.comp e.symm.injective
  have hm : fixedSubgroup.map i = Q ⊓ centralizer ({s} : Set (involutionCentralizer z)) := by
    ext q
    constructor
    · rintro ⟨m, hm, rfl⟩
      refine ⟨(e.symm m).property, mem_centralizer_singleton_iff.mpr ?_⟩
      have hf : MulAut.conjNormal s (e.symm m) = e.symm m := by
        apply e.injective
        rw [he, e.apply_symm_apply, (mem_fixedSubgroup m).mp hm]
      have hh := congrArg Subtype.val hf
      change s * i m * s⁻¹ = i m at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · rintro ⟨hq, hc⟩
      refine mem_map.mpr ⟨e ⟨q,hq⟩, ?_, ?_⟩
      · change cycle (e ⟨q,hq⟩) = e ⟨q,hq⟩
        rw [← he]
        apply congrArg e
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hc).symm
      · exact congrArg Subtype.val (e.symm_apply_apply ⟨q,hq⟩)
  have ef : fixedSubgroup ≃* DihedralGroup 4 :=
    (MulEquiv.subgroupCongr fixedSubgroup_eq_dihedral_range).trans
      (MonoidHom.ofInjective MinusExtraspecial.dihedral_injective).symm
  exact ⟨(MulEquiv.subgroupCongr hm).symm.trans
    ((fixedSubgroup.equivMapOfInjective i hi).symm.trans ef)⟩

/-- The full local cubic centralizer is the commuting product of its core part and cubic line. -/
theorem cubic_local_product (h : HTypeAt z) (s : involutionCentralizer z)
    (hs : orderOf s = 3) :
    Disjoint (localCore z ⊓ centralizer ({s} : Set (involutionCentralizer z))) (zpowers s) ∧
    (localCore z ⊓ centralizer ({s} : Set (involutionCentralizer z))) ⊔ zpowers s =
      centralizer ({s} : Set (involutionCentralizer z)) := by
  let H := involutionCentralizer z
  let Q := localCore z
  let C := centralizer ({s} : Set H)
  let Y := zpowers s
  let q := QuotientGroup.mk' Q
  have hY : Nat.card Y = 3 := (Nat.card_zpowers s).trans hs
  have hd : Disjoint Q Y := disjoint_of_coprime_natCard (by
    rw [h.core_card, hY]
    decide)
  have hi : Function.Injective (q.comp Y.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro y hy
    apply Subtype.ext
    exact disjoint_def.mp hd ((QuotientGroup.eq_one_iff _).mp hy) y.property
  have hYq : Nat.card (Y.map q) = 3 := by
    have hr : (q.comp Y.subtype).range = Y.map q := by rw [MonoidHom.range_comp, range_subtype]
    rw [← hr]
    exact (Nat.card_congr (MonoidHom.ofInjective hi).symm.toEquiv).trans hY
  have hYC : Y ≤ C := by
    apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr rfl
  have hYself : centralizer (Y.map q : Set (H ⧸ Q)) = Y.map q := by
    symm
    apply eq_of_le_of_card_ge (Y.map q).le_centralizer
    rw [alternatingGroup.FiveLocalGeometry.cubic_centralizer_card
      h.quotient_equiv.some _ hYq, hYq]
  have hCY : C ≤ centralizer (Y : Set H) := by
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro c hc
    exact mem_centralizer_singleton_iff.mp hc
  have hCq : C.map q ≤ Y.map q := by
    rw [← hYself]
    rintro _ ⟨c,hc,rfl⟩ _ ⟨y,hy,rfl⟩
    rw [← map_mul, ← map_mul, hCY hc y hy]
  refine ⟨hd.mono_left inf_le_left, le_antisymm (sup_le inf_le_right hYC) ?_⟩
  intro c hc
  obtain ⟨y,hy,hyc⟩ := hCq (mem_map_of_mem q hc)
  have hcy : c * y⁻¹ ∈ Q ⊓ C := by
    refine ⟨(QuotientGroup.eq_one_iff _).mp ?_, C.mul_mem hc (C.inv_mem (hYC hy))⟩
    change q (c * y⁻¹) = 1
    rw [map_mul, map_inv, hyc, mul_inv_cancel]
  simpa only [inv_mul_cancel_right] using
    (Q ⊓ C ⊔ Y).mul_mem (mem_sup_left hcy) (mem_sup_right hy)

/-- Simultaneous transport of the involution and cubic gives an actual dihedral complement. -/
theorem cubic_involution_complement (h : HTypeAt z) (hc : OneInvolutionClass G)
    (s t : G) (hs : orderOf s = 3) (ht : orderOf t = 2) (hst : Commute s t) :
    ∃ U : Subgroup G, Nonempty (U ≃* DihedralGroup 4) ∧
      Disjoint U (zpowers s) ∧ U ⊔ zpowers s =
        involutionCentralizer t ⊓ centralizer ({s} : Set G) := by
  obtain ⟨a,_,ha⟩ := hc
  obtain ⟨g,hg⟩ := isConj_iff.mp ((ha t ht).trans (ha z h.involution).symm)
  let e := MulAut.conj g
  have het : e t = z := hg
  let H := involutionCentralizer z
  let sH : H := ⟨e s, mem_centralizer_singleton_iff.mpr (by
    rw [← het, ← map_mul, ← map_mul, hst.eq])⟩
  have hsH : orderOf sH = 3 :=
    (orderOf_coe sH).symm.trans ((e.orderOf_eq s).trans hs)
  let j : H →* G := e.symm.toMonoidHom.comp H.subtype
  have hj : Function.Injective j := e.symm.injective.comp H.subtype_injective
  have hjs : j sH = s := e.symm_apply_apply s
  let U0 := localCore z ⊓ centralizer ({sH} : Set H)
  let U := U0.map j
  have hcent : (centralizer ({sH} : Set H)).map j =
      involutionCentralizer t ⊓ centralizer ({s} : Set G) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      constructor
      · apply mem_centralizer_singleton_iff.mpr
        apply e.injective
        simp only [map_mul, j, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          Subgroup.coe_subtype, e.apply_symm_apply, het]
        exact mem_centralizer_singleton_iff.mp y.property
      · apply mem_centralizer_singleton_iff.mpr
        rw [← hjs, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hy]
    · rintro ⟨hxt,hxs⟩
      have heH : e x ∈ H := by
        apply mem_centralizer_singleton_iff.mpr
        rw [← het, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hxt]
      refine ⟨⟨e x,heH⟩, ?_, e.symm_apply_apply x⟩
      apply mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      change e x * e s = e s * e x
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hxs]
  obtain ⟨hd,hgen⟩ := cubic_local_product h sH hsH
  have hY : (zpowers sH).map j = zpowers s := by
    rw [MonoidHom.map_zpowers, hjs]
  refine ⟨U, ⟨(U0.equivMapOfInjective j hj).symm.trans
    (cubic_core_fixed h sH hsH).some⟩, ?_, ?_⟩
  · rw [← hY]
    exact disjoint_map hj hd
  · rw [← hY, ← Subgroup.map_sup, hgen, hcent]


/-- The original cubic subgroup, relative to its full ambient centralizer. -/
def cubicKernel (s : G) : Subgroup (centralizer ({s} : Set G)) :=
  (zpowers s).subgroupOf (centralizer ({s} : Set G))

omit [Finite G] in
/-- The cubic line lies in the full centralizer of its generator. -/
theorem cubic_le_centralizer (s : G) : zpowers s ≤ centralizer ({s} : Set G) :=
  zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)

omit [Finite G] in
/-- The relative cubic kernel is central in the full cubic centralizer. -/
theorem cubicKernel_central (s : G) : cubicKernel s ≤ center (centralizer ({s} : Set G)) := by
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hx
  change (y : G) * (x : G) = (x : G) * y
  change s ^ n = (x : G) at hn
  rw [← hn]
  exact (show Commute (y : G) s from mem_centralizer_singleton_iff.mp y.property).zpow_right n

instance cubicKernel_normal (s : G) : (cubicKernel s).Normal where
  conj_mem x hx g := by
    rw [mem_center_iff.mp (cubicKernel_central s hx) g, mul_inv_cancel_right]
    exact hx

omit [Finite G] in
/-- The relative kernel has the order of the original cubic line. -/
theorem cubicKernel_card (s : G) (hs : orderOf s = 3) : Nat.card (cubicKernel s) = 3 :=
  (Nat.card_congr (subgroupOfEquivOfLe (cubic_le_centralizer s)).toEquiv).trans
    ((Nat.card_zpowers s).trans hs)

/-- Every involution centralizer in the literal central cubic quotient is D₈. -/
theorem cubic_quotient_involution_centralizers (h : HTypeAt z) (hc : OneInvolutionClass G)
    (s : G) (hs : orderOf s = 3)
    (v : centralizer ({s} : Set G) ⧸ cubicKernel s) (hv : orderOf v = 2) :
    Nonempty (centralizer ({v} : Set (centralizer ({s} : Set G) ⧸ cubicKernel s)) ≃*
      DihedralGroup 4) := by
  let C := centralizer ({s} : Set G)
  let K := cubicKernel s
  let q := QuotientGroup.mk' K
  obtain ⟨t,ht,htv⟩ :=
    Sporadic.Janko3.SourceRecognition.CentralCubicQuotient.exists_involution_lift
      K (cubicKernel_card s hs) v hv
  have htG : orderOf (t : G) = 2 := (orderOf_coe t).trans ht
  obtain ⟨U,⟨eU⟩,hd,hgen⟩ := cubic_involution_complement h hc s t hs htG
    (mem_centralizer_singleton_iff.mp t.property).symm
  have hUC : U ≤ C := le_sup_left.trans (hgen.le.trans inf_le_right)
  let V := U.subgroupOf C
  have hdV : Disjoint V K := by
    apply disjoint_def.mpr
    intro x hx hy
    apply Subtype.ext
    exact disjoint_def.mp hd hx hy
  have hVgen : V ⊔ K = centralizer ({t} : Set C) := by
    apply map_injective C.subtype_injective
    change (V ⊔ cubicKernel s).map C.subtype = _
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hUC]
    change U ⊔ ((zpowers s).subgroupOf C).map C.subtype = _
    rw [map_subgroupOf_eq_of_le (cubic_le_centralizer s)]
    rw [hgen]
    ext x
    constructor
    · rintro ⟨hxt,hxs⟩
      refine mem_map.mpr ⟨⟨x,hxs⟩,?_,rfl⟩
      exact mem_centralizer_singleton_iff.mpr (Subtype.ext
        (mem_centralizer_singleton_iff.mp hxt))
    · rintro ⟨x,hx,rfl⟩
      exact ⟨mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (mem_centralizer_singleton_iff.mp hx)), x.property⟩
  obtain ⟨e⟩ := Sporadic.Janko3.SourceRecognition.CentralCubicQuotient.centralizer_equiv
    K (cubicKernel_central s) (cubicKernel_card s hs) t ht V hdV hVgen
  rw [htv] at e
  exact ⟨e.trans ((subgroupOfEquivOfLe hUC).trans eU)⟩


end CFSG.Quasithin.Janko23.J3Recognition.Ambient
