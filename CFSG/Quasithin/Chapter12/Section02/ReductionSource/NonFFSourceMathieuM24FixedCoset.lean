module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Crossing
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetFixedCoset

/-!
# The full M24 core intersections modulo their centers

The actual hexacode quotient supplies every displacement character on V_z.
A fixed coset in O₂(LT) modulo the original involution line therefore has a
representative centralizing O₂(L_z). Perfectness of L_z promotes this to
centralization of L_z, with the entire O₂(LT) kernel retained.

For every subgroup Y between the original closure E and O₂(C_G(z)), this
identifies O₂(LT) ∩ Y with V_z Z(Y), and identifies C_{V_z}(Y) with ⟨z⟩.
The order calculation gives |Y/Z(Y)| = 4096. In particular the full
centralizer core is E Z(O₂(C_G(z))), and the original E/Z(E) is elementary
abelian of order 4096. No center bound or fixed-coset callback is assumed.

These results isolate the remaining center bound in source 8.2.12. They do
not assert Z(E)=⟨z⟩ or extraspeciality. That bound, the earlier whole-cocode
marking, the remaining Mathieu branches and ambient J4 recognition stay
with qt-d-1222-nonff-mathieu. In the M24 model the perfect sextet residual
has index two in the full sextet stabilizer, so the Sylow containment used
in the separate Hermitian model is not available here.
Source: Aschbacher–Smith 8.2.11–12, printed p.722, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

omit [Finite G] in
private theorem intersection_eq_seed_sup_center
    (Q X W Y : Subgroup G) [IsMulCommutative Q]
    (hXQ : X ≤ normalizer (Q : Set G)) (hQW : Q ≤ centralizer (W : Set G))
    (hker : X ⊓ centralizer (W : Set G) ≤ Q)
    (hWY : W ≤ Y) (hWQ : W ≤ Q)
    (hYXQ : Y ≤ X ⊔ Q) (hXYQ : X ≤ Y ⊔ Q)
    (hcoset : ∀ d ∈ Q ⊓ Y, ∃ w ∈ W, w⁻¹*d ∈ Q ⊓ centralizer (X : Set G)) :
    Q ⊓ Y = W ⊔ (Y ⊓ centralizer (Y : Set G)) ∧
      Y ⊓ centralizer (Y : Set G) = Q ⊓ Y ⊓ centralizer (X : Set G) := by
  let J := X ⊔ Q
  have hCQ : Q ≤ centralizer (Q : Set G) := by
    intro x hx q hq
    exact congrArg Subtype.val (mul_comm' (⟨q,hq⟩ : Q) ⟨x,hx⟩)
  have hcenter : Y ⊓ centralizer (Y : Set G) = Q ⊓ Y ⊓ centralizer (X : Set G) := by
    apply le_antisymm
    · intro a ha
      have haW : a ∈ centralizer (W : Set G) := centralizer_le hWY ha.2
      have haJ := hYXQ ha.1
      let : (Q.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
        (sup_le hXQ Q.le_normalizer)
      have hj : (⟨a,haJ⟩ : J) ∈ X.subgroupOf J ⊔ Q.subgroupOf J := by
        rw [←subgroupOf_sup (show X ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
        exact mem_top _
      obtain ⟨x,hx,q,hq,he⟩ := mem_sup_of_normal_right.mp hj
      have he' : (x : G)*(q : G)=a := congrArg J.subtype he
      have hxW : (x : G) ∈ centralizer (W : Set G) := by
        have hh := (centralizer (W : Set G)).mul_mem haW ((centralizer _).inv_mem (hQW hq))
        change a*(q : G)⁻¹ ∈ _ at hh
        rwa [←he',mul_inv_cancel_right] at hh
      have haQ : a ∈ Q := by
        rw [←he']
        exact Q.mul_mem (hker ⟨hx,hxW⟩) hq
      refine ⟨⟨haQ,ha.1⟩,?_⟩
      have hyc : Y ≤ centralizer ({a} : Set G) :=
        fun y hy => mem_centralizer_singleton_iff.mpr (ha.2 y hy)
      have hqc : Q ≤ centralizer ({a} : Set G) :=
        fun q hq => mem_centralizer_singleton_iff.mpr (hCQ haQ q hq)
      intro x hx
      exact mem_centralizer_singleton_iff.mp ((sup_le hyc hqc) (hXYQ hx))
    · intro a ha
      refine ⟨ha.1.2,?_⟩
      have hxc : X ≤ centralizer ({a} : Set G) :=
        fun x hx => mem_centralizer_singleton_iff.mpr (ha.2 x hx)
      have hqc : Q ≤ centralizer ({a} : Set G) :=
        fun q hq => mem_centralizer_singleton_iff.mpr (hCQ ha.1.1 q hq)
      intro y hy
      exact mem_centralizer_singleton_iff.mp ((sup_le hxc hqc) (hYXQ hy))
  refine ⟨le_antisymm ?_ (sup_le (le_inf hWQ hWY) (hcenter.le.trans inf_le_left)),hcenter⟩
  intro d hd
  obtain ⟨w,hw,hwc⟩ := hcoset d hd
  have hwY : w⁻¹*d ∈ Y := Y.mul_mem (Y.inv_mem (hWY hw)) hd.2
  have hh := (W ⊔ (Y ⊓ centralizer (Y : Set G))).mul_mem (mem_sup_left hw)
    (mem_sup_right (hcenter.ge ⟨⟨hwc.1,hwY⟩,hwc.2⟩))
  simpa only [mul_inv_cancel_left] using hh

omit [Finite G] in
private theorem seed_centralizer_of_join
    (Q X W Y Z : Subgroup G)
    (hQW : Q ≤ centralizer (W : Set G)) (hYXQ : Y ≤ X ⊔ Q) (hXYQ : X ≤ Y ⊔ Q)
    (hfix : W ⊓ centralizer (X : Set G) = Z) :
    W ⊓ centralizer (Y : Set G) = Z := by
  have hWQ := le_centralizer_iff.mp hQW
  have hf (A B : Subgroup G) (hAB : A ≤ B ⊔ Q) :
      W ⊓ centralizer (B : Set G) ≤ W ⊓ centralizer (A : Set G) := by
    intro w hw
    refine ⟨hw.1,?_⟩
    have hb : B ≤ centralizer ({w} : Set G) :=
      fun b hb => mem_centralizer_singleton_iff.mpr (hw.2 b hb)
    have hq : Q ≤ centralizer ({w} : Set G) :=
      fun q hq => mem_centralizer_singleton_iff.mpr (hWQ hw.1 q hq)
    intro a ha
    exact mem_centralizer_singleton_iff.mp ((sup_le hb hq) (hAB ha))
  exact le_antisymm ((hf X Y hXYQ).trans hfix.le) (hfix.ge.trans (hf Y X hYXQ))

/-- The common fixed subgroup on the whole original module is the central line. -/
theorem sourceOrbit_m24_centralizer_module_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    D.sourceOrbit ⊓ centralizer (localTwoCore L z : Set G) = zpowers (z : G) := by
  have hZW := (D.sourceOrbit_m24_centralizer_commutator_series h hmany hV hq hnon a E hE z hz hne).2.2.2.1.le
  have hf := D.sourceOrbit_m24_centralizer_transvection_fixed h hmany hV hq hnon a E hE z hz hne
  apply le_antisymm
  · intro v hv
    have hw := (D.sourceOrbit_m24_centralizer_fixed_modulo_line h hmany hV hq hnon a E hE z hz hne
      ⟨v,hv.1⟩).mp (fun x => by
        rw [commutatorElement_eq_one_iff_mul_comm.mpr (hv.2 x x.property)]
        exact (zpowers (z : G)).one_mem)
    exact hf.le ⟨hw,hv.2⟩
  · exact (le_inf (hZW.trans (commutatorSpace_le L D.sourceOrbit z
      D.sourceOrbit_component_normalizes)) (hf.ge.trans inf_le_right))


/-- Inside the full LT core, centralizing the point two-core is equivalent to centralizing its perfect residual. -/
theorem sourceOrbit_m24_centralizer_core_centralizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (localTwoCore L z : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (localResidual L z : Set G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := localResidual L z
  let X := localTwoCore L z
  let : Group.IsPerfect R := Group.IsPerfect.map _
  have hRL : R ≤ L := (localResidual_le L z).trans inf_le_left
  have hRQ : R ≤ normalizer (Q : Set G) := (hRL.trans le_sup_left).trans
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hRX : R ≤ normalizer (X : Set G) := R.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image R (pCore 2 R))
  have hcomm := (D.sourceOrbit_m24_cocode_block_structure h hmany hV hq hnon a E hE).1
  have hZR : zpowers (z : G) ≤ centralizer (R : Set G) := zpowers_le.mpr (by
    intro r hr
    exact mem_centralizer_singleton_iff.mp ((localResidual_le L z) hr).2)
  have hc := centralizer_core_le_of_perfect Q D.sourceOrbit R X (zpowers (z : G)) hRQ hRX
    ((commutator_mono le_rfl hRL).trans hcomm.le)
    (D.sourceOrbit_m24_centralizer_module_fixed h hmany hV hq hnon a E hE z hz hne).le hZR
  exact le_antisymm (le_inf inf_le_left hc)
    (inf_le_inf_left Q (centralizer_le (localTwoCore_le L z)))


/-- Correct each centrally displaced element of the full LT core by an actual vector in V_z. -/
theorem sourceOrbit_m24_centralizer_core_fixed_coset
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (d : G) (hd : d ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hfixed : ∀ x : localTwoCore L z, ⁅(x : G),d⁆ ∈ zpowers (z : G)) :
    ∃ w ∈ commutatorSpace L D.sourceOrbit z,
      w⁻¹*d ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (localResidual L z : Set G) := by
  let W := commutatorSpace L D.sourceOrbit z
  let X := localTwoCore L z
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hWV : W ≤ D.sourceOrbit := commutatorSpace_le L D.sourceOrbit z D.sourceOrbit_component_normalizes
  have hVQ : D.sourceOrbit ≤ Q := hV ▸ D.le_core
  have hz2 : orderOf (z : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) z.property)
    (fun hh => hne (Subtype.ext hh))
  obtain ⟨_,q,hqs,hqk⟩ := D.sourceOrbit_m24_centralizer_twoCore_quotient h hmany hV hq hnon a E hE z hz hne
  obtain ⟨hcard,_,hcomm,_⟩ := D.sourceOrbit_m24_centralizer_commutator_series h hmany hV hq hnon a E hE z hz hne
  have hVC : D.sourceOrbit ≤ centralizer (W : Set G) := by
    intro v hv w hw
    exact congrArg Subtype.val (mul_comm' (⟨w,hWV hw⟩ : D.sourceOrbit) ⟨v,hv⟩)
  have hWZ : W ≤ centralizer ({(z : G)} : Set G) :=
    commutatorSpace_le_centralizer L D.sourceOrbit z z.property D.sourceOrbit_component_normalizes
  obtain ⟨w,hw,hwc⟩ := MathieuSextet.hexacode_fixed_coset W X D.sourceOrbit (z : G) hz2 q hqs hqk hVC
    ((localTwoCore_le L z).trans ((localResidual_le L z).trans inf_le_right)) hWZ
    (by rw [commutator_comm]; exact hcomm.le)
    (D.sourceOrbit_m24_centralizer_transvection_fixed h hmany hV hq hnon a E hE z hz hne)
    hcard d hfixed ((show Q ≤ centralizer (D.sourceOrbit : Set G) from hV ▸ D.core_centralizes) hd)
  have hwQ : w⁻¹*d ∈ Q := Q.mul_mem (Q.inv_mem (hVQ (hWV hw))) hd
  exact ⟨w,hw,(D.sourceOrbit_m24_centralizer_core_centralizers h hmany hV hq hnon a E hE z hz hne).le ⟨hwQ,hwc⟩⟩


/-- The full-core intersection retains exactly the residual-centralizer obstruction beyond V_z. -/
theorem sourceOrbit_m24_centralizer_full_core_intersection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    let C := centralizer ({(z : G)} : Set G)
    Q ⊓ C.pCoreIn 2 = commutatorSpace L D.sourceOrbit z ⊔
      (Q ⊓ C.pCoreIn 2 ⊓ centralizer (localResidual L z : Set G)) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let C := centralizer ({(z : G)} : Set G)
  let W := commutatorSpace L D.sourceOrbit z
  have hWQ : W ≤ Q := (commutatorSpace_le L D.sourceOrbit z
    D.sourceOrbit_component_normalizes).trans (show D.sourceOrbit ≤ Q from hV ▸ D.le_core)
  obtain ⟨hcomm,hcap,_⟩ := D.sourceOrbit_m24_centralizer_module_core_intersections h hmany hV hq hnon a E hE z hz hne
  have hWC : W ≤ C.pCoreIn 2 := hcap.ge.trans inf_le_right
  change Q ⊓ C.pCoreIn 2 = W ⊔ (Q ⊓ C.pCoreIn 2 ⊓ centralizer (localResidual L z : Set G))
  apply le_antisymm
  · intro d hd
    have hfixed (x : localTwoCore L z) : ⁅(x : G),d⁆ ∈ zpowers (z : G) := by
      rw [commutator_comm] at hcomm
      exact hcomm (commutator_mem_commutator x.property hd)
    obtain ⟨w,hw,hwc⟩ := D.sourceOrbit_m24_centralizer_core_fixed_coset h hmany hV hq hnon a E hE z hz hne d hd.1 hfixed
    have hwC : w⁻¹*d ∈ C.pCoreIn 2 := (C.pCoreIn 2).mul_mem ((C.pCoreIn 2).inv_mem (hWC hw)) hd.2
    have hh := (W ⊔ (Q ⊓ C.pCoreIn 2 ⊓ centralizer (localResidual L z : Set G))).mul_mem
      (mem_sup_left hw) (mem_sup_right ⟨⟨hwc.1,hwC⟩,hwc.2⟩)
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le (le_inf hWQ hWC) inf_le_left


/-- For every intermediate closure overgroup, the excess intersection is precisely its center, and its fixed subgroup on V_z is the original line. -/
theorem sourceOrbit_m24_centralizer_intersections_mod_centers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)    (Y : Subgroup G)
    (hEY : (sourceClosure L D.sourceOrbit z).map
      (centralizer ({(z : G)} : Set G)).subtype ≤ Y)
    (hYC : Y ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2) :
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    let W := commutatorSpace L D.sourceOrbit z
    Q ⊓ Y = W ⊔ (Y ⊓ centralizer (Y : Set G)) ∧
      Y ⊓ centralizer (Y : Set G) = Q ⊓ Y ⊓ centralizer (localResidual L z : Set G) ∧
      W ⊓ centralizer (Y : Set G) = zpowers (z : G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let X := localTwoCore L z
  let W := commutatorSpace L D.sourceOrbit z
  let C := centralizer ({(z : G)} : Set G)
  let F := (sourceClosure L D.sourceOrbit z).map C.subtype
  have hWV : W ≤ D.sourceOrbit := commutatorSpace_le L D.sourceOrbit z D.sourceOrbit_component_normalizes
  have hVQ : D.sourceOrbit ≤ Q := hV ▸ D.le_core
  have hWY : W ≤ Y := (commutatorSpace_le_sourceClosure L D.sourceOrbit z z.property
    D.sourceOrbit_component_normalizes).trans hEY
  have hQW : Q ≤ centralizer (W : Set G) :=
    (show Q ≤ centralizer (D.sourceOrbit : Set G) from hV ▸ D.core_centralizes).trans (centralizer_le hWV)
  have hXQ : X ≤ normalizer (Q : Set G) :=
    ((localTwoCore_le L z).trans ((localResidual_le L z).trans inf_le_left)).trans
      (le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))
  have hker : X ⊓ centralizer (W : Set G) ≤ Q :=
    (D.sourceOrbit_m24_centralizer_transvection_kernel h hmany hV hq hnon a E hE z hz hne).le.trans hVQ
  have hYXQ : Y ≤ X ⊔ Q := hYC.trans
    (D.sourceOrbit_m24_centralizer_closure_local_containment h hmany hV hq hnon a E hE z hz hne).1
  have hXYQ : X ≤ Y ⊔ Q := (le_sup_left.trans
    (D.sourceOrbit_m24_centralizer_closure_join_core h hmany hV hq hnon a E hE z hz hne).ge).trans
      (sup_le_sup_right hEY Q)
  have hc := D.sourceOrbit_m24_centralizer_core_centralizers h hmany hV hq hnon a E hE z hz hne
  have hcomm := (D.sourceOrbit_m24_centralizer_module_core_intersections h hmany hV hq hnon a E hE z hz hne).1
  have hcoset (d : G) (hd : d ∈ Q ⊓ Y) : ∃ w ∈ W, w⁻¹*d ∈ Q ⊓ centralizer (X : Set G) := by
    have hfixed (x : X) : ⁅(x : G),d⁆ ∈ zpowers (z : G) := by
      rw [commutator_comm] at hcomm
      exact hcomm (commutator_mem_commutator x.property ⟨hd.1,hYC hd.2⟩)
    obtain ⟨w,hw,hwc⟩ := D.sourceOrbit_m24_centralizer_core_fixed_coset h hmany hV hq hnon a E hE z hz hne d hd.1 hfixed
    exact ⟨w,hw,hc.ge hwc⟩
  let := (D.sourceOrbit_m24_cocode_block_structure h hmany hV hq hnon a E hE).2.2.2.2.2.2.2.2.1
  obtain ⟨hcap,hcenter⟩ := intersection_eq_seed_sup_center Q X W Y hXQ hQW hker hWY (hWV.trans hVQ) hYXQ hXYQ hcoset
  have he : Q ⊓ Y ⊓ centralizer (X : Set G) = Q ⊓ Y ⊓ centralizer (localResidual L z : Set G) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1,(hc.le ⟨hx.1.1,hx.2⟩).2⟩
    · intro hx
      exact ⟨hx.1,(hc.ge ⟨hx.1.1,hx.2⟩).2⟩
  exact ⟨hcap,hcenter.trans he,seed_centralizer_of_join Q X W Y (zpowers (z : G)) hQW hYXQ hXYQ
    (D.sourceOrbit_m24_centralizer_transvection_fixed h hmany hV hq hnon a E hE z hz hne)⟩

/-- The exact full hexacode quotient and the original seed give order 4096 modulo the center of every intermediate closure overgroup. -/
theorem sourceOrbit_m24_centralizer_center_quotient_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)    (Y : Subgroup G)
    (hEY : (sourceClosure L D.sourceOrbit z).map
      (centralizer ({(z : G)} : Set G)).subtype ≤ Y)
    (hYC : Y ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2) :
    Nat.card (Y ⧸ center Y) = 4096 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let X := localTwoCore L z
  let W := commutatorSpace L D.sourceOrbit z
  let C := centralizer ({(z : G)} : Set G)
  let F := (sourceClosure L D.sourceOrbit z).map C.subtype
  let ZY := Y ⊓ centralizer (Y : Set G)
  have hWV : W ≤ D.sourceOrbit := commutatorSpace_le L D.sourceOrbit z D.sourceOrbit_component_normalizes
  have hVQ : D.sourceOrbit ≤ Q := hV ▸ D.le_core
  have hWY : W ≤ Y := (commutatorSpace_le_sourceClosure L D.sourceOrbit z z.property
    D.sourceOrbit_component_normalizes).trans hEY
  have hXQ : X ≤ normalizer (Q : Set G) :=
    ((localTwoCore_le L z).trans ((localResidual_le L z).trans inf_le_left)).trans
      (le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))
  have hYXQ : Y ≤ X ⊔ Q := hYC.trans
    (D.sourceOrbit_m24_centralizer_closure_local_containment h hmany hV hq hnon a E hE z hz hne).1
  have hXYQ : X ≤ Y ⊔ Q := (le_sup_left.trans
    (D.sourceOrbit_m24_centralizer_closure_join_core h hmany hV hq hnon a E hE z hz hne).ge).trans
      (sup_le_sup_right hEY Q)
  have hYQ : Y ≤ normalizer (Q : Set G) := hYXQ.trans (sup_le hXQ Q.le_normalizer)
  have hj : Y ⊔ Q = X ⊔ Q := le_antisymm (sup_le hYXQ le_sup_right) (sup_le hXYQ le_sup_right)
  obtain ⟨hcap,hcen,hfix⟩ := D.sourceOrbit_m24_centralizer_intersections_mod_centers
    h hmany hV hq hnon a E hE z hz hne Y hEY hYC
  change Q ⊓ Y = W ⊔ ZY at hcap
  have hZW : ZY ≤ normalizer (W : Set G) :=
    (inf_le_right.trans (centralizer_le hWY)).trans (Subgroup.centralizer_le_normalizer _)
  have hWZ : W ⊓ ZY = zpowers (z : G) := by
    change W ⊓ (Y ⊓ centralizer (Y : Set G)) = _
    rw [←inf_assoc,inf_eq_left.mpr hWY]
    exact hfix
  obtain ⟨hVX,q,hqsur,hqker⟩ := D.sourceOrbit_m24_centralizer_twoCore_quotient h hmany hV hq hnon a E hE z hz hne
  have hQX : Q ⊓ X = D.sourceOrbit := by
    apply le_antisymm ?_ (le_inf hVQ hVX)
    intro x hx
    apply (D.sourceOrbit_m24_centralizer_transvection_kernel h hmany hV hq hnon a E hE z hz hne).le
    exact ⟨hx.2,centralizer_le hWV ((show Q ≤ centralizer (D.sourceOrbit : Set G) from hV ▸ D.core_centralizes) hx.1)⟩
  have hXcard : Nat.card X = 64*Nat.card D.sourceOrbit := by
    rw [q.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hqsur).toEquiv,
      hqker,Nat.card_congr (subgroupOfEquivOfLe hVX).toEquiv]
    have hm : Nat.card (Multiplicative Atlas.Codes.hexacode) = 64 := Atlas.Codes.hexacode_card
    rw [hm]
  have hpX := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q X hXQ
  rw [hQX,hXcard,sup_comm Q X] at hpX
  have hXQcard : Nat.card (X ⊔ Q : Subgroup G) = 64*Nat.card Q := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := D.sourceOrbit))
    nlinarith [hpX]
  have hpY := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q Y hYQ
  rw [sup_comm Q Y,hj,hXQcard] at hpY
  have hYcard : Nat.card Y = 64*Nat.card (Q ⊓ Y : Subgroup G) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q))
    nlinarith [hpY]
  have hWcard := (D.sourceOrbit_m24_centralizer_commutator_series h hmany hV hq hnon a E hE z hz hne).1
  have hzcard : Nat.card (zpowers (z : G)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) z.property)
      (fun hh => hne (Subtype.ext hh))
  have hpZ := card_mul_eq_card_inf_mul_card_sup_of_normalizes W ZY hZW
  rw [hWZ,←hcap,hWcard,hzcard] at hpZ
  have hcZ : Nat.card (Q ⊓ Y : Subgroup G) = 64*Nat.card ZY := by omega
  have hcenterMap : (center Y).map Y.subtype = ZY := by
    ext y
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,fun b hb => congrArg Subtype.val (mem_center_iff.mp ha ⟨b,hb⟩)⟩
    · intro hy
      exact ⟨⟨y,hy.1⟩,mem_center_iff.mpr (fun b => Subtype.ext (hy.2 b b.property)),rfl⟩
  have hcZY : Nat.card ZY = Nat.card (center Y) := by
    rw [←hcenterMap,card_map_of_injective Y.subtype_injective]
  have hc := card_eq_card_quotient_mul_card_subgroup (center Y)
  rw [hYcard,hcZ,hcZY] at hc
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := center Y))
  nlinarith [hc]

/-- The full centralizer core is the original closure times its center, and every central element of the closure centralizes that full core. -/
theorem sourceOrbit_m24_centralizer_core_central_product
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    let C := centralizer ({(z : G)} : Set G)
    let F := (sourceClosure L D.sourceOrbit z).map C.subtype
    let Q := C.pCoreIn 2
    Q = F ⊔ (Q ⊓ centralizer (Q : Set G)) ∧
      F ⊓ centralizer (F : Set G) = F ⊓ centralizer (Q : Set G) := by
  let C := centralizer ({(z : G)} : Set G)
  let F := (sourceClosure L D.sourceOrbit z).map C.subtype
  let Q := C.pCoreIn 2
  let M := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let X := localTwoCore L z
  let W := commutatorSpace L D.sourceOrbit z
  have hFQ : F ≤ Q := map_mono
    (D.sourceOrbit_m24_centralizer_closure_core h hmany hV hq hnon a E hE z hz hne).1
  have hWQ : W ≤ F := commutatorSpace_le_sourceClosure L D.sourceOrbit z z.property
    D.sourceOrbit_component_normalizes
  have hQM : Q ≤ F ⊔ M :=
    (D.sourceOrbit_m24_centralizer_closure_local_containment h hmany hV hq hnon a E hE z hz hne).1.trans
      (D.sourceOrbit_m24_centralizer_closure_join_core h hmany hV hq hnon a E hE z hz hne).ge
  have hcap := (D.sourceOrbit_m24_centralizer_intersections_mod_centers h hmany hV hq hnon a E hE z hz hne Q hFQ le_rfl).1
  have hFM : F ≤ normalizer (M : Set G) :=
    (le_sup_left.trans (D.sourceOrbit_m24_centralizer_closure_join_core h hmany hV hq hnon a E hE z hz hne).le).trans
      (sup_le (((localTwoCore_le L z).trans ((localResidual_le L z).trans inf_le_left)).trans
        (le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))) M.le_normalizer)
  have hprod : Q = F ⊔ (Q ⊓ centralizer (Q : Set G)) := by
    apply le_antisymm ?_ (sup_le hFQ inf_le_left)
    intro d hd
    let J := F ⊔ M
    let : (M.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer (sup_le hFM M.le_normalizer)
    have hj : (⟨d,hQM hd⟩ : J) ∈ F.subgroupOf J ⊔ M.subgroupOf J := by
      rw [←subgroupOf_sup (show F ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
      exact mem_top _
    obtain ⟨f,hf,m,hm,he⟩ := mem_sup_of_normal_right.mp hj
    have he' : (f : G)*(m : G)=d := congrArg J.subtype he
    have hmQ : (m : G) ∈ Q := by
      have hh := Q.mul_mem (Q.inv_mem (hFQ hf)) hd
      change (f : G)⁻¹*d ∈ Q at hh
      rwa [←he',inv_mul_cancel_left] at hh
    have hmcap : (m : G) ∈ W ⊔ (Q ⊓ centralizer (Q : Set G)) := hcap.le ⟨hm,hmQ⟩
    rw [←he']
    exact (F ⊔ (Q ⊓ centralizer (Q : Set G))).mul_mem (mem_sup_left hf)
      ((sup_le_sup_right hWQ _) hmcap)
  refine ⟨hprod,le_antisymm ?_ (inf_le_inf_left F (centralizer_le hFQ))⟩
  intro f hf
  refine ⟨hf.1,?_⟩
  have hF : F ≤ centralizer ({f} : Set G) :=
    fun x hx => mem_centralizer_singleton_iff.mpr (hf.2 x hx)
  have hZ : Q ⊓ centralizer (Q : Set G) ≤ centralizer ({f} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hx.2 f (hFQ hf.1)).symm
  intro q hq
  exact mem_centralizer_singleton_iff.mp ((sup_le hF hZ) (hprod.le hq))

/-- The original relative closure and intrinsic centralizer two-core both have central quotient order 4096; the closure quotient is elementary abelian. -/
theorem sourceOrbit_m24_centralizer_center_quotients
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    let C := centralizer ({(z : G)} : Set G)
    let F := sourceClosure L D.sourceOrbit z
    IsElementaryAbelian 2 (F ⧸ center F) ∧
      Nat.card (F ⧸ center F) = 4096 ∧
      Nat.card ((pCore 2 C) ⧸ center (pCore 2 C)) = 4096 := by
  let C := centralizer ({(z : G)} : Set G)
  let F := sourceClosure L D.sourceOrbit z
  let F' := F.map C.subtype
  let Q := C.pCoreIn 2
  have hclosure := D.sourceOrbit_m24_centralizer_closure_core h hmany hV hq hnon a E hE z hz hne
  have hFQ : F' ≤ Q := map_mono hclosure.1
  have hF := D.sourceOrbit_m24_centralizer_center_quotient_card h hmany hV hq hnon a E hE z hz hne
  let eF : F ≃* F' := F.equivMapOfInjective C.subtype C.subtype_injective
  let eQ : pCore 2 C ≃* Q := (pCore 2 C).equivMapOfInjective C.subtype C.subtype_injective
  let cF := QuotientGroup.congr (center F) (center F') eF (FixedElementary.map_center eF)
  let cQ := QuotientGroup.congr (center (pCore 2 C)) (center Q) eQ (FixedElementary.map_center eQ)
  exact ⟨hclosure.2.2.2,(Nat.card_congr cF.toEquiv).trans (hF F' le_rfl hFQ),
    (Nat.card_congr cQ.toEquiv).trans (hF Q hFQ le_rfl)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
