module

public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.NonsplitGeometry.BinaryInvolutions
public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.NonsplitGeometry.QuaternionRank
public import Theory.GroupTheory.QuaternionCentralProductTransport
public import Theory.GroupTheory.ElementarySixteenExtensionGeometry
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.QuaternionProductOrderFourCentralizer

/-!
# Nonsplit-block geometry and the elementary-sixteen branch

The transfer application below uses relative normality in the actual
local overgroup M. It transports the literal subgroups, quotients,
centralizers and rank bound to the ambient Sylow subgroup. The local
square-one and centralizer premises of Thompson transfer are proved
from the B.4.8(3) fixed-space containment and involution lifts in L.

Source: Aschbacher–Smith, Lemmas 14.4.4(6) and 14.4.5, printed
pp.1007–1008, combined manuscript of 1 March 2004. This is conditional
local mathematics: the same embedded quaternion core supplies rank three,
order 64, quotient involution lifts, conjugators, and order-four witnesses.
These give the regular action on A − V and the elementary-extension
transfer contradiction, without assuming its square or centralizer bounds.

Only the fixed-space containment from B.4.8(3) is needed. It is stated
on the literal L/(A ∩ L) conjugation action, then transported to M/A.
The earlier B.4 theorem and the source construction of the local block,
c₂ action, and overgroup alternatives remain with their assembly owners.
This module does not assert all of 14.4.4 or 14.4.5.
-/

open Subgroup

namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.NonsplitGeometry

variable {G : Type*} [Group G] [Finite G]

/-- The quaternion core and a single involution class in the actual quotient
supply both lifting and order-four premises for the elementary-extension
calculation. The order-eight intersection makes the core strictly larger. -/
public theorem involution_geometry_of_single_quotient_class
    (L A : Subgroup G) [A.Normal] (U : Subgroup L)
    (d : QuaternionCentralProductData U)
    (hcover : L ⊔ A = ⊤) (hVU : A.subgroupOf L ≤ U)
    (hV : Nat.card (A.subgroupOf L) = 8)
    (hclass : ∀ a b : L ⧸ A.subgroupOf L,
      orderOf a = 2 → orderOf b = 2 → IsConj a b) :
    (∀ q : G ⧸ A, orderOf q = 2 →
      ∃ y ∈ L, y^2=1 ∧ QuotientGroup.mk' A y = q) ∧
    (∀ y : L, orderOf y = 2 → ∃ r : L, Commute y r ∧ orderOf r = 4) := by
  have hproper : ¬ U ≤ A.subgroupOf L := by
    intro h
    have hc := card_le_of_le h
    rw [d.card,hV] at hc
    omega
  obtain ⟨hlift,hconj⟩ := quaternion_involution_lifts_and_cover_of_single_quotient_class
    (A.subgroupOf L) U d hVU hproper hclass
  refine ⟨involution_lifts_of_normal_supplement L A hcover hlift, ?_⟩
  intro y hy
  obtain ⟨g,hg⟩ := hconj y hy
  exact exists_commuting_order_four_of_conj_mem_quaternion U d y g hg

/-- In the local overgroup, the source order-64 intersection makes the
canonical quotient action regular on the eight elements of A outside L. -/
public theorem regular_action_on_elementary_coset
    (T : Sylow 2 G) (L A : Subgroup G) [L.Normal] [A.Normal]
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hcover : L ⊔ A = ⊤) (hA : Nat.card A = 16)
    (hV : Nat.card (L ⊓ A : Subgroup G) = 8)
    (hTL : Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) = 64)
    (hfixed : ∀ y ∈ L, orderOf (QuotientGroup.mk' A y) = 2 →
      ∀ a ∈ A, Commute y a → a ∈ L)
    (a b : A) (ha : (a : G) ∉ L) (hb : (b : G) ∉ L) :
    ∃! q : (T : Subgroup G).map (QuotientGroup.mk' A),
      abelianQuotientConj A q a = b :=
  regular_quotient_action_of_fixed_bound (T : Subgroup G) L A T.isPGroup' hcover
    hfixed hA hV
    (sylow_image_card_of_elementary_extension (T : Subgroup G) L A hAT hcover hA hV hTL)
    a b ha hb

/-- Transfer with every local subgroup interpreted inside the actual overgroup M. -/
public theorem elementary_extension_transfer_of_fixed_spaces
    (T : Sylow 2 G) (M L A : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hLM : L ≤ M) (hAT : A ≤ (T : Subgroup G))
    [(L.subgroupOf M).Normal] [(A.subgroupOf M).Normal]
    [IsElementaryAbelian 2 A]
    (hcover : L.subgroupOf M ⊔ A.subgroupOf M = ⊤)
    (hA : Nat.card A = 16) (hV : Nat.card (L ⊓ A : Subgroup G) = 8)
    (hfixed : ∀ y ∈ L.subgroupOf M,
      orderOf (QuotientGroup.mk' (A.subgroupOf M) y) = 2 →
      ∀ a ∈ A.subgroupOf M, Commute y a → a ∈ L.subgroupOf M)
    (hlift : ∀ q : M ⧸ A.subgroupOf M, orderOf q = 2 →
      ∃ y ∈ L.subgroupOf M, y^2 = 1 ∧ QuotientGroup.mk' (A.subgroupOf M) y = q)
    (hrank : primeRank 2 ((T : Subgroup G) ⊓ L : Subgroup G) ≤ 3)
    (hfour : ∀ y : L, orderOf y = 2 → ∃ r : L, Commute y r ∧ orderOf r = 4)
    (hnorm : normalizer (A : Set G) ≤ normalizer (L : Set G))
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) : False := by
  let TL := (T : Subgroup G) ⊓ L
  let T₀ := (T : Subgroup G).subgroupOf M
  let L₀ := L.subgroupOf M
  let A₀ := A.subgroupOf M
  have hAM : A ≤ M := hAT.trans hTM
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hAM
  have hA₀ : Nat.card A₀ = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAM).toEquiv).trans hA
  have hV₀ : Nat.card (L₀ ⊓ A₀ : Subgroup M) = 8 := by
    change Nat.card ((L ⊓ A).subgroupOf M) = 8
    exact (Nat.card_congr (subgroupOfEquivOfLe
      ((inf_le_left : L ⊓ A ≤ L).trans hLM)).toEquiv).trans hV
  have hi := relative_index_two_of_elementary_extension T₀ L₀ A₀
    (fun _ hx => hAT hx) hcover hA₀ hV₀
  have hindex : (L.subgroupOf (T : Subgroup G)).index = 2 := by
    change L₀.relIndex T₀ = 2 at hi
    rw [relIndex_subgroupOf hTM] at hi
    exact hi
  have hbound (E : Subgroup G) (hET : E ≤ (T : Subgroup G)) (hEL : E ≤ L)
      (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 8 := by
    let : IsElementaryAbelian 2 E := hE
    have hETL : E ≤ TL := le_inf hET hEL
    have hE₀ := IsElementaryAbelian.subgroupOf (p := 2) hETL
    have hc := (primeRank_le_iff_elementary_card_le TL).mp hrank (E.subgroupOf TL) hE₀
    rw [Nat.card_congr (subgroupOfEquivOfLe hETL).toEquiv] at hc
    exact hc
  have hout (x : G) (hx : x ∈ (T : Subgroup G)) (hxL : x ∉ L) (hx2 : x^2 = 1) :
      x ∈ A := by
    exact outside_involution_mem_of_involution_lifts L₀ A₀ hfixed hlift
      (⟨x,hTM hx⟩ : M) hxL (Subtype.ext hx2)
  have hsmall (a : G) (ha : a ∈ A) (haL : a ∉ L) :
      (T : Subgroup G) ⊓ centralizer ({a} : Set G) ≤ A := by
    have hp : IsPGroup 2 T₀ := T.isPGroup'.comap_subtype
    have hc := centralizer_bound_of_quotient_involution_fixed T₀ L₀ A₀ hp hcover
      hfixed (⟨a,hAM ha⟩ : M) ha haL
    intro x hx
    apply hc (show (⟨x,hTM hx.1⟩ : M) ∈ T₀ ⊓
      centralizer ({(⟨a,hAM ha⟩ : M)} : Set M) from ?_)
    exact ⟨hx.1, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp hx.2))⟩
  apply elementary_sixteen_extension_transfer T L A hno hAT hA hindex hbound hout hnorm hsmall
  intro y hy hy2
  obtain ⟨r,hr,hr4⟩ := hfour (⟨y,hy⟩ : L) (by rwa [← Subgroup.orderOf_coe])
  exact ⟨r,hr.map L.subtype, by rwa [Subgroup.orderOf_coe]⟩

omit [Finite G] in
/-- The inclusion of the block induces an injection of its intrinsic quotient
into the overgroup quotient. Thus B.4.8(3) applies to the same involutions. -/
private theorem fixed_bound_from_block_quotient
    (L A : Subgroup G) [A.Normal]
    (hfixed : ∀ y : L, orderOf (QuotientGroup.mk' (A.subgroupOf L) y) = 2 →
      ∀ a ∈ A, Commute (y : G) a → a ∈ L) :
    ∀ y ∈ L, orderOf (QuotientGroup.mk' A y) = 2 →
      ∀ a ∈ A, Commute y a → a ∈ L := by
  let f : L →* G ⧸ A := (QuotientGroup.mk' A).comp L.subtype
  have hker : A.subgroupOf L = f.ker := by
    ext x
    exact (QuotientGroup.eq_one_iff (x : G)).symm
  let j : (L ⧸ A.subgroupOf L) →* G ⧸ A :=
    (QuotientGroup.kerLift f).comp
      (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom
  have hj : Function.Injective j :=
    (QuotientGroup.kerLift_injective f).comp
      (QuotientGroup.quotientMulEquivOfEq hker).injective
  intro y hy hq a ha hc
  apply hfixed ⟨y, hy⟩ ?_ a ha hc
  exact (orderOf_injective j hj (QuotientGroup.mk' (A.subgroupOf L) ⟨y, hy⟩)).symm.trans hq

/-- One actual c₂ quaternion core supplies the order and rank of T ∩ L,
all elementary-cardinality bounds, lifts into L, actual conjugators into the
image of that same core, and commuting order-four witnesses in L.
The elementary eight used for the lower bound is the actual A ∩ L. -/
public theorem binary_c2_block_geometry
    (T L A : Subgroup G) [A.Normal] [IsElementaryAbelian 2 A]
    (hAT : A ≤ T) (hcover : L ⊔ A = ⊤)
    (hV : Nat.card (L ⊓ A : Subgroup G) = 8)
    (U : Subgroup (T ⊓ L : Subgroup G)) [U.Normal]
    (d : QuaternionCentralProductData U) (hindex : U.index = 2)
    (s : (T ⊓ L : Subgroup G)) (hs : s ∉ U)
    (hc2 : d.IsC2 (MulAut.conjNormal s))
    (hVU : A.subgroupOf (T ⊓ L) ≤ U)
    (e : (L ⧸ A.subgroupOf L) ≃* Matrix.PSL3Two.PSL) :
    Nat.card (T ⊓ L : Subgroup G) = 64 ∧
    primeRank 2 (T ⊓ L : Subgroup G) = 3 ∧
    (∀ E : Subgroup G, E ≤ T → E ≤ L → IsElementaryAbelian 2 E → Nat.card E ≤ 8) ∧
    (∀ q : G ⧸ A, orderOf q = 2 →
      ∃ y ∈ L, y ^ 2 = 1 ∧ QuotientGroup.mk' A y = q) ∧
    (∀ y : L, orderOf y = 2 →
      ∃ g : L, MulAut.conj g y ∈ U.map (inclusion inf_le_right)) ∧
    (∀ y : L, orderOf y = 2 → ∃ r : L, Commute y r ∧ orderOf r = 4) := by
  let P := T ⊓ L
  let V := A.subgroupOf P
  have hVA : V ≃* (L ⊓ A : Subgroup G) := {
    toFun := fun x => ⟨x.val.val, x.val.property.2, x.property⟩
    invFun := fun x => ⟨⟨x.val, hAT x.property.2, x.property.1⟩, x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hVc : Nat.card V = 8 := (Nat.card_congr hVA.toEquiv).trans hV
  let _ : IsElementaryAbelian 2 V := {
    toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative P A
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian
        (p := 2) x.val.val x.property))) }
  let VU := V.subgroupOf U
  have hVUe : VU ≃* V := subgroupOfEquivOfLe hVU
  have hVUc : Nat.card VU = 8 := (Nat.card_congr hVUe.toEquiv).trans hVc
  have hVUelem : IsElementaryAbelian 2 VU := IsElementaryAbelian.subgroupOf hVU
  obtain ⟨hcard, hrank, hbound⟩ :=
    quaternion_c2_rank_and_order U d hindex s hs hc2 VU hVUelem hVUc
  let i : P →* L := inclusion inf_le_right
  have hi : Function.Injective i := inclusion_injective inf_le_right
  let UL := U.map i
  let dL := d.map (U.equivMapOfInjective i hi)
  have hVL : A.subgroupOf L ≤ UL := by
    intro x hx
    exact ⟨⟨x.val, hAT hx, x.property⟩, hVU hx, rfl⟩
  have hVLcard : Nat.card (A.subgroupOf L) = 8 := by
    rw [← inf_subgroupOf_right A L]
    exact (Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv).trans
      (by simpa only [inf_comm] using hV)
  obtain ⟨hliftL, hconj, hfour⟩ :=
    binary_block_involution_geometry (A.subgroupOf L) UL dL hVL hVLcard e
  have hlift := involution_lifts_of_normal_supplement L A hcover (fun q hq => by
    obtain ⟨y, hy, hyq⟩ := hliftL q hq
    exact ⟨y, by simpa only [hy] using pow_orderOf_eq_one y, hyq⟩)
  refine ⟨hcard, hrank, ?_, hlift, hconj, hfour⟩
  intro E hET hEL hE
  let _ := hE
  have hEP : E ≤ P := le_inf hET hEL
  have hb := hbound (E.subgroupOf P) (IsElementaryAbelian.subgroupOf hEP)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv] at hb

/-- The E₁₆ local geometry in the overgroup M (here named G).
The only module input is B.4.8(3)'s fixed-space containment for the actual
block quotient. The regular action uses the literal image of T in M/A;
no square-one, centralizer, or regularity conclusion is assumed. -/
public theorem elementary_extension_geometry_of_binary_c2
    (T L A : Subgroup G) [L.Normal] [A.Normal] [IsElementaryAbelian 2 A]
    (hT : IsPGroup 2 T) (hAT : A ≤ T) (hcover : L ⊔ A = ⊤)
    (hA : Nat.card A = 16) (hV : Nat.card (L ⊓ A : Subgroup G) = 8)
    (U : Subgroup (T ⊓ L : Subgroup G)) [U.Normal]
    (d : QuaternionCentralProductData U) (hindex : U.index = 2)
    (s : (T ⊓ L : Subgroup G)) (hs : s ∉ U)
    (hc2 : d.IsC2 (MulAut.conjNormal s))
    (hVU : A.subgroupOf (T ⊓ L) ≤ U)
    (e : (L ⧸ A.subgroupOf L) ≃* Matrix.PSL3Two.PSL)
    (hfixed : ∀ y : L, orderOf (QuotientGroup.mk' (A.subgroupOf L) y) = 2 →
      ∀ a ∈ A, Commute (y : G) a → a ∈ L) :
    Nat.card (T ⊓ L : Subgroup G) = 64 ∧
    primeRank 2 (T ⊓ L : Subgroup G) = 3 ∧
    (L.subgroupOf T).index = 2 ∧
    (∀ E : Subgroup G, E ≤ T → E ≤ L → IsElementaryAbelian 2 E → Nat.card E ≤ 8) ∧
    (∀ x ∈ T, x ∉ L → x ^ 2 = 1 → x ∈ A) ∧
    (∀ a ∈ A, a ∉ L → T ⊓ centralizer ({a} : Set G) ≤ A) ∧
    (∀ a b : A, (a : G) ∉ L → (b : G) ∉ L →
      ∃! q : T.map (QuotientGroup.mk' A), abelianQuotientConj A q a = b) := by
  obtain ⟨hcard, hrank, hbound, hlift, _, _⟩ :=
    binary_c2_block_geometry T L A hAT hcover hV U d hindex s hs hc2 hVU e
  have hfix := fixed_bound_from_block_quotient L A hfixed
  refine ⟨hcard, hrank,
    relative_index_two_of_elementary_extension T L A hAT hcover hA hV, hbound, ?_, ?_, ?_⟩
  · intro x _ hxL hx2
    exact outside_involution_mem_of_involution_lifts L A hfix hlift x hxL hx2
  · exact centralizer_bound_of_quotient_involution_fixed T L A hT hcover hfix
  · exact regular_quotient_action_of_fixed_bound T L A hT hcover hfix hA hV
      (sylow_image_card_of_elementary_extension T L A hAT hcover hA hV hcard)


/-- The E₁₆ branch of 14.4.5 contradicts the ambient transfer hypothesis.
Both local normality assumptions are relative to M. The core is embedded
in the actual local intersection, and its elementary subgroup bounds and
order-four witnesses are transported to the original ambient subgroups.
The configuration owner supplies the block, c₂ action, B.4.8(3), and the
normalizer and no-index-two hypotheses from the source setup. -/
public theorem elementary_extension_transfer_of_binary_c2
    (T : Sylow 2 G) (M L A : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hLM : L ≤ M) (hAT : A ≤ (T : Subgroup G))
    [(L.subgroupOf M).Normal] [(A.subgroupOf M).Normal]
    [IsElementaryAbelian 2 A]
    (hcover : L.subgroupOf M ⊔ A.subgroupOf M = ⊤)
    (hA : Nat.card A = 16) (hV : Nat.card (L ⊓ A : Subgroup G) = 8)
    (U : Subgroup ((T : Subgroup G).subgroupOf M ⊓ L.subgroupOf M : Subgroup M))
    [U.Normal] (d : QuaternionCentralProductData U) (hindex : U.index = 2)
    (s : ((T : Subgroup G).subgroupOf M ⊓ L.subgroupOf M : Subgroup M))
    (hs : s ∉ U) (hc2 : d.IsC2 (MulAut.conjNormal s))
    (hVU : (A.subgroupOf M).subgroupOf
      ((T : Subgroup G).subgroupOf M ⊓ L.subgroupOf M) ≤ U)
    (e : ((L.subgroupOf M) ⧸ (A.subgroupOf M).subgroupOf (L.subgroupOf M)) ≃*
      Matrix.PSL3Two.PSL)
    (hfixed : ∀ y : L.subgroupOf M,
      orderOf (QuotientGroup.mk' ((A.subgroupOf M).subgroupOf (L.subgroupOf M)) y) = 2 →
      ∀ a ∈ A.subgroupOf M, Commute (y : M) a → a ∈ L.subgroupOf M)
    (hnorm : normalizer (A : Set G) ≤ normalizer (L : Set G))
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) : False := by
  let T₀ := (T : Subgroup G).subgroupOf M
  let L₀ := L.subgroupOf M
  let A₀ := A.subgroupOf M
  have hAM : A ≤ M := hAT.trans hTM
  let _ : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hAM
  have hV₀ : Nat.card (L₀ ⊓ A₀ : Subgroup M) = 8 := by
    change Nat.card ((L ⊓ A).subgroupOf M) = 8
    exact (Nat.card_congr (subgroupOfEquivOfLe
      ((inf_le_left : L ⊓ A ≤ L).trans hLM)).toEquiv).trans hV
  obtain ⟨_, _, hbound, hlift, _, hfour⟩ :=
    binary_c2_block_geometry T₀ L₀ A₀ (fun _ hx => hAT hx) hcover hV₀ U d hindex s hs hc2 hVU e
  have hrank' : primeRank 2 ((T : Subgroup G) ⊓ L : Subgroup G) ≤ 3 := by
    apply (primeRank_le_iff_elementary_card_le _).mpr
    intro E hE
    let _ := hE
    let P := (T : Subgroup G) ⊓ L
    let i : P →* M := inclusion (inf_le_left.trans hTM)
    have hEm : IsElementaryAbelian 2 (E.map i) := IsElementaryAbelian.map i
    have hb := hbound (E.map i)
      (by rintro _ ⟨x, _, rfl⟩; exact x.property.1)
      (by rintro _ ⟨x, _, rfl⟩; exact x.property.2) hEm
    rwa [card_map_of_injective (inclusion_injective _)] at hb
  have hfour' (y : L) (hy : orderOf y = 2) : ∃ r : L, Commute y r ∧ orderOf r = 4 := by
    let el : L₀ ≃* L := subgroupOfEquivOfLe hLM
    obtain ⟨r, hc, hr⟩ := hfour (el.symm y) ((el.symm.orderOf_eq y).trans hy)
    refine ⟨el r, ?_, (el.orderOf_eq r).trans hr⟩
    have h := hc.map el.toMonoidHom
    change Commute (el (el.symm y)) (el r) at h
    simpa only [MulEquiv.apply_symm_apply] using h
  exact elementary_extension_transfer_of_fixed_spaces T M L A hTM hLM hAT hcover hA hV
    (fixed_bound_from_block_quotient L₀ A₀ hfixed) hlift hrank' hfour' hnorm hno

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.NonsplitGeometry
