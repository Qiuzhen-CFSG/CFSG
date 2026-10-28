module

public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.QuaternionResidual.Geometry
public import Theory.GroupTheory.PResidual.OddImage
public import Theory.GroupTheory.AutomorphismLocalDisplacement
public import Theory.GroupTheory.QuaternionElementaryEightCentralizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.PGroupCore

/-!
# The outer image of the quaternion residual normalizer

Let U be the actual normal quaternion central product in H, with central-quotient
conjugation kernel O₂(H). For the swapping involution a, put A = ⟨a,[U,a]⟩.
Suppose K* has elementary order nine and the marked cubic L₁* is normal in H*,
inverted by a*, with the earlier source product H* = N_H(A)* L₁*.
Then the actual R = N_K(A), K = O²(H), satisfies [R : R ∩ O₂(H)] = 3 and
R ∩ C_G(A) ≤ O₂(H), with both characteristic subgroups mapped from H into G.

The normalizer image centralizes a*: the image of A is the cyclic group
⟨a*⟩ of order at most two. Its intersection with the inverted cubic is therefore
trivial. The source product restricts to K*, giving an intersection of order
three. To lift that intersection into the actual residual normalizer, take the
two-residual of its preimage in N_H(A); its odd image is unchanged. This step
does not require the action kernel to lie in K.

For the centralizer, [U,a] is a normal self-centralizing elementary eight in U.
An automorphism fixing it pointwise has square one, by displacement into this
eight. Its image in the elementary three-group K* consequently vanishes.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of 14.4.4,
printed p.1007. Both d = 4 alternatives are covered: only their already
established K* and marked cubic data are used. Fixed-point-free action of L₁*
and the other split geometry enter the earlier producer of the set product.
That product remains an explicit premise; no A₄ action or equality U = O₂(H)
is assumed. The chapter assembly must discharge the product using its action
dichotomy and supply the earlier split geometry.
-/

open Subgroup
open scoped Pointwise commutatorElement

namespace Subgroup.QuaternionResidual.OuterNormalizer

variable {B D : Type*} [Group B] [Finite B] [Group D]

private theorem residual_map_of_odd_image (f : B →* D) (P : Subgroup B)
    (ho : Odd (Nat.card (P.map f))) :
    ((pResidual 2 P).map P.subtype).map f = P.map f := by
  rw [map_embedded_pResidual]
  have hr : pResidual 2 (P.map f) = ⊤ := by
    apply top_unique
    intro x _
    apply mem_pResidual_of_orderOf_coprime
    exact ho.coprime_two_left.of_dvd_right (_root_.orderOf_dvd_natCard x)
  rw [hr, ← MonoidHom.range_eq_map, range_subtype]

private theorem odd_image_le_residual_image (f : B →* D) (P : Subgroup B)
    (ho : Odd (Nat.card (P.map f))) : P.map f ≤ (pResidual 2 B).map f := by
  rw [← residual_map_of_odd_image f P ho]
  exact map_mono (map_pResidual_le 2 P.subtype)

/-- An odd residual image commutes with intersection with a subgroup,
even when the action kernel is not contained in the residual. -/
public theorem residual_inf_map (f : B →* D) (N : Subgroup B)
    (ho : Odd (Nat.card ((pResidual 2 B).map f))) :
    (N ⊓ pResidual 2 B).map f = N.map f ⊓ (pResidual 2 B).map f := by
  apply le_antisymm (map_inf_le _ _ _)
  let P := N ⊓ ((pResidual 2 B).map f).comap f
  have hP : P.map f = N.map f ⊓ (pResidual 2 B).map f := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨mem_map_of_mem f hb.1, hb.2⟩
    · rintro ⟨⟨b, hb, rfl⟩, hk⟩
      exact ⟨b, ⟨hb, hk⟩, rfl⟩
  have hodd : Odd (Nat.card (P.map f)) :=
    ho.of_dvd_nat (card_dvd_of_le (hP ▸ inf_le_right))
  rw [← hP, ← residual_map_of_odd_image f P hodd]
  apply map_mono
  exact le_inf ((map_subtype_le _).trans inf_le_left) (map_pResidual_le 2 P.subtype)

private theorem residual_normalizer_index [Finite D]
    (f : B →* D) (N L : Subgroup B) (s : D)
    (hK : Nat.card ((pResidual 2 B).map f) = 9)
    (hL : Nat.card (L.map f) = 3)
    (hLn : f.range ≤ normalizer (L.map f : Set D))
    (hprod : (f.range : Set D) = (N.map f : Set D) * (L.map f : Set D))
    (hNc : N.map f ≤ centralizer ({s} : Set D))
    (hinv : ∀ l ∈ L.map f, s * l * s⁻¹ = l⁻¹) :
    f.ker.relIndex (N ⊓ pResidual 2 B) = 3 := by
  have hoK : Odd (Nat.card ((pResidual 2 B).map f)) := by rw [hK]; decide
  have hoL : Odd (Nat.card (L.map f)) := by rw [hL]; decide
  have hLK := odd_image_le_residual_image f L hoL
  have hd : Disjoint (N.map f) (L.map f) := by
    apply disjoint_def.mpr
    intro x hxN hxL
    have hx2 : x ^ 2 = 1 := by
      have hc := mem_centralizer_singleton_iff.mp (hNc hxN)
      have he : x = x⁻¹ := by
        simpa only [← hc, mul_inv_cancel_right] using hinv x hxL
      rw [pow_two, show x * x = x * x⁻¹ from congrArg (x * ·) he, mul_inv_cancel]
    have hx3 : x ^ 3 = 1 := by
      have h := pow_card_eq_one' (x := (⟨x, hxL⟩ : L.map f))
      rw [hL] at h
      exact congrArg Subtype.val h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by
      simpa using Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx2)
        (orderOf_dvd_of_pow_eq_one hx3)))
  let P := N.map f ⊓ (pResidual 2 B).map f
  have hjoin : L.map f ⊔ P = (pResidual 2 B).map f := by
    apply le_antisymm (sup_le hLK inf_le_right)
    intro x hx
    have hxR : x ∈ (f.range : Set D) := (map_le_range f _) hx
    rw [hprod] at hxR
    obtain ⟨n, hn, l, hl, rfl⟩ := hxR
    have hnK : n ∈ (pResidual 2 B).map f := by
      simpa only [mul_inv_cancel_right] using
        ((pResidual 2 B).map f).mul_mem hx (((pResidual 2 B).map f).inv_mem (hLK hl))
    exact (L.map f ⊔ P).mul_mem (mem_sup_right ⟨hn, hnK⟩) (mem_sup_left hl)
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint (L.map f) P
    (inf_le_left.trans ((map_le_range f N).trans hLn)) (hd.symm.mono_right inf_le_left)
  rw [hjoin, hK, hL] at hc
  rw [relIndex_ker, residual_inf_map f N hoK]
  change Nat.card P = 3
  omega

variable {G : Type*} [Group G] [Finite G]

/-- The conjugation action on the actual central quotient of the embedded U. -/
@[expose] public def action (H U : Subgroup G) (hHU : H ≤ normalizer (U : Set G)) :
    H →* MulAut (U ⧸ center U) :=
  (quotientAut (center U)).comp (U.normalizerMonoidHom.comp (inclusion hHU))

private theorem action_eq_one_of_mem_core (H U : Subgroup G)
    (d : QuaternionCentralProductData U) (hHU : H ≤ normalizer (U : Set G))
    (x : H) (hx : (x : G) ∈ U) : action H U hHU x = 1 := by
  let := d.quotient_elementary
  apply MulEquiv.ext
  intro v
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center U) v
  change quotientAut (center U) (U.normalizerMonoidHom (inclusion hHU x))
    (QuotientGroup.mk' (center U) u) = QuotientGroup.mk' (center U) u
  rw [quotientAut_apply_mk]
  change QuotientGroup.mk' (center U) (⟨(x : G) * u * (x : G)⁻¹, _⟩ : U) =
    QuotientGroup.mk' (center U) u
  have he : (⟨(x : G) * u * (x : G)⁻¹, _⟩ : U) =
      (⟨x, hx⟩ : U) * u * (⟨x, hx⟩ : U)⁻¹ := rfl
  rw [he, map_mul, map_mul, map_inv]
  rw [mul_comm' (QuotientGroup.mk' (center U) ⟨x, hx⟩), mul_assoc,
    mul_inv_cancel, mul_one]

private theorem normalizer_image_centralizes (H U A : Subgroup G)
    (d : QuaternionCentralProductData U) (hHU : H ≤ normalizer (U : Set G))
    (hUH : U ≤ H) (a : G) (haH : a ∈ H) (ha : a ^ 2 = 1)
    (hW : ⁅U, zpowers a⁆ ≤ U) (hA : A = zpowers a ⊔ ⁅U, zpowers a⁆) :
    ((normalizer (A : Set G)).subgroupOf H).map (action H U hHU) ≤
      centralizer ({action H U hHU ⟨a, haH⟩} : Set (MulAut (U ⧸ center U))) := by
  let f := action H U hHU
  let aa : H := ⟨a, haH⟩
  have hAH : A ≤ H := by rw [hA]; exact sup_le (zpowers_le.mpr haH) (hW.trans hUH)
  have hAs : A.subgroupOf H = zpowers aa ⊔ (⁅U, zpowers a⁆).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hAH, map_sup, MonoidHom.map_zpowers,
      map_subgroupOf_eq_of_le (hW.trans hUH)]
    exact hA
  have him : (A.subgroupOf H).map f = zpowers (f aa) := by
    rw [hAs, map_sup, MonoidHom.map_zpowers]
    have hw : ((⁅U, zpowers a⁆).subgroupOf H).map f = ⊥ := by
      apply eq_bot_iff.mpr
      rintro _ ⟨x, hx, rfl⟩
      exact action_eq_one_of_mem_core H U d hHU x (hW hx)
    rw [hw, sup_bot_eq]
  have hn : ((normalizer (A : Set G)).subgroupOf H).map f ≤
      normalizer (zpowers (f aa) : Set (MulAut (U ⧸ center U))) := by
    rw [← him, subgroupOf_normalizer_eq hAH]
    exact le_normalizer_map f
  by_cases he : f aa = 1
  · intro x _
    rw [show action H U hHU ⟨a, haH⟩ = 1 from he]
    exact mem_centralizer_singleton_iff.mpr (by simp)
  · have ha2 : (f aa) ^ 2 = 1 := by
      rw [← map_pow, show aa ^ 2 = 1 from Subtype.ext ha, map_one]
    exact hn.trans_eq (normalizer_zpowers_eq_centralizer_of_order_two _
      (orderOf_eq_prime ha2 he))

private theorem square_conjugation_of_centralizes_sixteen (H U A : Subgroup G)
    (d : QuaternionCentralProductData U) (hHU : H ≤ normalizer (U : Set G))
    (a : G) (ha : a ^ 2 = 1) (hout : a ∉ U)
    (hswap : (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom =
      d.right.map U.subtype)
    (hA : A = zpowers a ⊔ ⁅U, zpowers a⁆)
    (x : H) (hx : (x : G) ∈ centralizer (A : Set G)) :
    (U.normalizerMonoidHom (inclusion hHU x)) ^ 2 = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hw, hAe, _⟩ := d.elementary_sixteen_of_swap U a ha hout hswap
  let : IsElementaryAbelian 2 A := hA ▸ hAe
  let W := ⁅U, zpowers a⁆
  have hWU : W ≤ U := by
    dsimp only [W]
    rw [hw]
    exact inf_le_left
  have hWA : W ≤ A := hA ▸ le_sup_right
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWA
  let E := W.subgroupOf U
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hWU
  have hE : Nat.card E = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWU).toEquiv]
    obtain ⟨hk, hc⟩ := core_centralizer_of_swap U A d a ha hout hswap hA
    rwa [hk] at hc
  have hself : centralizer (E : Set U) ≤ E := by
    have hs := inf_centralizer_elementary_eight_of_quaternion_factors
      d.left d.right E d.left_model d.right_model d.intersection_card d.commute
      hE (by rw [d.span]; exact le_top)
    rw [d.span, top_inf_eq] at hs
    exact hs.le
  apply MulEquiv.ext
  intro u
  apply MulAut.square_apply_eq_on_normalizer E hself
    (U.normalizerMonoidHom (inclusion hHU x))
  · intro e he
    apply Subtype.ext
    change (x : G) * (e : G) * (x : G)⁻¹ = e
    rw [← hx e (hWA he), mul_inv_cancel_right]
  · rw [← subgroupOf_normalizer_eq hWU]
    exact normalizer_commutator_ge_left U (zpowers a) u.property

/-- Centralizing the source sixteen inside the actual two-residual forces
trivial action on U/Z(U), and hence membership in the actual two-core. -/
public theorem residual_centralizer_le_twoCore (H U A : Subgroup G)
    (d : QuaternionCentralProductData U) (hHU : H ≤ normalizer (U : Set G))
    (hker : (action H U hHU).ker = pCore 2 H)
    (hK : IsElementaryAbelian 3 ((pResidual 2 H).map (action H U hHU)))
    (a : G) (ha : a ^ 2 = 1) (hout : a ∉ U)
    (hswap : (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom =
      d.right.map U.subtype)
    (hA : A = zpowers a ⊔ ⁅U, zpowers a⁆) :
    ((pResidual 2 H).map H.subtype) ⊓ centralizer (A : Set G) ≤
      (pCore 2 H).map H.subtype := by
  rintro x ⟨⟨y, hy, rfl⟩, hx⟩
  refine ⟨y, ?_, rfl⟩
  rw [← hker]
  change action H U hHU y = 1
  have h2 : (action H U hHU y) ^ 2 = 1 := by
    change (quotientAut (center U) (U.normalizerMonoidHom (inclusion hHU y))) ^ 2 = 1
    rw [← map_pow, square_conjugation_of_centralizes_sixteen H U A d hHU
      a ha hout hswap hA y hx, map_one]
  let := hK
  have h3 : (action H U hHU y) ^ 3 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian _ (mem_map_of_mem _ hy)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by
    simpa using Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one h3)))

/-- The outer index and centralizer kernel for the literal residual normalizer.
The set product is the earlier source action-dichotomy conclusion. -/
public theorem outerNormalizer_indices (H U A L₁ : Subgroup G)
    (d : QuaternionCentralProductData U) (hHU : H ≤ normalizer (U : Set G))
    (hker : (action H U hHU).ker = pCore 2 H)
    (hK : IsElementaryAbelian 3 ((pResidual 2 H).map (action H U hHU)))
    (hKcard : Nat.card ((pResidual 2 H).map (action H U hHU)) = 9)
    (hLcard : Nat.card ((L₁.subgroupOf H).map (action H U hHU)) = 3)
    (hLn : (action H U hHU).range ≤
      normalizer ((L₁.subgroupOf H).map (action H U hHU) : Set (MulAut (U ⧸ center U))))
    (a : G) (haH : a ∈ H) (ha : a ^ 2 = 1) (hout : a ∉ U)
    (hswap : (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom =
      d.right.map U.subtype)
    (hinv : ∀ l ∈ (L₁.subgroupOf H).map (action H U hHU),
      action H U hHU ⟨a, haH⟩ * l * (action H U hHU ⟨a, haH⟩)⁻¹ = l⁻¹)
    (hA : A = zpowers a ⊔ ⁅U, zpowers a⁆)
    (hUK : U ≤ (pResidual 2 H).map H.subtype)
    (hprod : ((action H U hHU).range : Set (MulAut (U ⧸ center U))) =
      (((normalizer (A : Set G)).subgroupOf H).map (action H U hHU) :
        Set (MulAut (U ⧸ center U))) *
      ((L₁.subgroupOf H).map (action H U hHU) : Set (MulAut (U ⧸ center U)))) :
    ((pCore 2 H).map H.subtype).relIndex
      (((pResidual 2 H).map H.subtype) ⊓ normalizer (A : Set G)) = 3 ∧
    ((((pResidual 2 H).map H.subtype) ⊓ normalizer (A : Set G)) ⊓
      centralizer (A : Set G)) ≤ (pCore 2 H).map H.subtype := by
  have hUH : U ≤ H := hUK.trans (map_subtype_le _)
  have hW : ⁅U, zpowers a⁆ ≤ U :=
    (d.elementary_sixteen_of_swap U a ha hout hswap).1 ▸ inf_le_left
  have hc := normalizer_image_centralizes H U A d hHU hUH a haH ha hW hA
  have hi := residual_normalizer_index (action H U hHU)
    ((normalizer (A : Set G)).subgroupOf H) (L₁.subgroupOf H)
    (action H U hHU ⟨a, haH⟩) hKcard hLcard hLn hprod hc hinv
  rw [hker] at hi
  have hm : (((normalizer (A : Set G)).subgroupOf H) ⊓ pResidual 2 H).map H.subtype =
      ((pResidual 2 H).map H.subtype) ⊓ normalizer (A : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy.2, rfl⟩, hy.1⟩
    · rintro ⟨⟨y, hy, rfl⟩, hn⟩
      exact ⟨y, ⟨hn, hy⟩, rfl⟩
  constructor
  · rw [← hm, relIndex_map_map_of_injective _ _ H.subtype_injective]
    exact hi
  · exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans
      (residual_centralizer_le_twoCore H U A d hHU hker hK a ha hout hswap hA)

end Subgroup.QuaternionResidual.OuterNormalizer
