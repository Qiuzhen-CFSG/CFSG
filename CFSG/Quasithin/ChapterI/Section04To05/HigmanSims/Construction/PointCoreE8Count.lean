module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreSeedCoverage
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointPlaneCoreCard
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Counting elementary eights in the original HS point core

The literal elementary eights containing the marked involution are counted
by ordered generators modulo that involution line. Each contributes24
pairs. The central cyclic four bounds square-one elements in the point
core and in its order32 involution centralizers, bounding the total pairs
by30·12. These are direct consequences of HS1--HS2 preceding
Aschbacher--Smith I.4.8, printed p.418.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims

variable {G : Type*} [Group G] [Finite G]

/-- The literal elementary-eight subgroups of the marked point core which
contain the marked involution. -/
@[expose, reducible] def pointCoreEights (z : G) :=
  {E : Subgroup G // E ≤ (involutionCentralizer z).pCoreIn 2 ∧ z ∈ E ∧
    IsElementaryAbelian 2 E ∧ Nat.card E = 8}

private theorem outside_card (A E : Subgroup G) (hAE : A ≤ E) :
    Nat.card {x : E // (x : G) ∉ A} = Nat.card E - Nat.card A := by
  classical
  let := Fintype.ofFinite E
  change Nat.card {x : E // ¬ x ∈ A.subgroupOf E} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    Nat.card_congr (subgroupOfEquivOfLe hAE).toEquiv]

omit [Finite G] in
private theorem plane_card (E : Subgroup G) [IsElementaryAbelian 2 E]
    (z x : G) (hz : z ∈ E) (hz2 : orderOf z = 2) (hx : x ∈ E)
    (hxz : x ∉ zpowers z) : Nat.card (zpowers z ⊔ zpowers x : Subgroup G) = 4 := by
  rw [card_sup_zpowers_of_normalizing_involution _ _
    (elemPow_eq_one_of_isElementaryAbelian x hx) hxz]
  · rw [Nat.card_zpowers, hz2]
  · apply centralizer_le_normalizer
    rw [zpowers_eq_closure, centralizer_closure]
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : E) ⟨z, hz⟩)

private abbrev eightPairs (E : Subgroup G) (z : G) :=
  Σ x : {x : E // (x : G) ∉ zpowers z},
    {y : E // (y : G) ∉ (zpowers z ⊔ zpowers (x.val : G) : Subgroup G)}

private theorem eight_pairs_card (E : Subgroup G) [IsElementaryAbelian 2 E]
    (z : G) (hz : z ∈ E) (hz2 : orderOf z = 2) (hE : Nat.card E = 8) :
    Nat.card (eightPairs E z) = 24 := by
  classical
  let := Fintype.ofFinite {x : E // (x : G) ∉ zpowers z}
  have hc : Nat.card {x : E // (x : G) ∉ zpowers z} = 6 := by
    rw [outside_card _ _ (zpowers_le.mpr hz), hE, Nat.card_zpowers, hz2]
  have hy (x : {x : E // (x : G) ∉ zpowers z}) :
      Nat.card {y : E // (y : G) ∉ (zpowers z ⊔ zpowers (x.val : G) : Subgroup G)} = 4 := by
    rw [outside_card _ _ (sup_le (zpowers_le.mpr hz) (zpowers_le.mpr x.val.property)),
      hE, plane_card E z x hz hz2 x.val.property x.property]
  change Nat.card (Σ x : {x : E // (x : G) ∉ zpowers z},
    {y : E // (y : G) ∉ (zpowers z ⊔ zpowers (x.val : G) : Subgroup G)}) = 24
  rw [Nat.card_sigma]
  simp only [hy, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, hc]

private theorem eight_pairs_generate (E : Subgroup G) [IsElementaryAbelian 2 E]
    (z : G) (hz : z ∈ E) (hz2 : orderOf z = 2) (hE : Nat.card E = 8)
    (p : eightPairs E z) :
    E = (zpowers z ⊔ zpowers (p.1.val : G)) ⊔ zpowers (p.2.val : G) := by
  let B := zpowers z ⊔ zpowers (p.1.val : G)
  have hBE : B ≤ E := sup_le (zpowers_le.mpr hz) (zpowers_le.mpr p.1.val.property)
  symm
  apply eq_of_le_of_card_ge (sup_le hBE (zpowers_le.mpr p.2.val.property))
  rw [card_sup_zpowers_of_normalizing_involution _ _
    (elemPow_eq_one_of_isElementaryAbelian _ p.2.val.property) p.2.property]
  · rw [plane_card E z p.1 hz hz2 p.1.val.property p.1.property, hE]
  · apply centralizer_le_normalizer
    intro x hx
    exact congrArg Subtype.val (mul_comm (⟨x, hBE hx⟩ : E) p.2.val)

private theorem square_one_bound (K : Subgroup G) (c : G) (hc : c ∈ K)
    (hcomm : ∀ x ∈ K, Commute c x) (hc2 : c ^ 2 ≠ 1) :
    2 * ({x : G | x ∈ K ∧ x ^ 2 = 1} : Set G).ncard ≤ Nat.card K := by
  let S : Set K := {x | x ^ 2 = 1}
  let cK : K := ⟨c, hc⟩
  have hi : Set.InjOn (fun x : K => cK * x) S := (mul_right_injective cK).injOn
  have hm : (fun x : K => cK * x) '' S ⊆ Sᶜ := by
    rintro _ ⟨x, hx, rfl⟩ hh
    apply hc2
    have hxG : (x : G) ^ 2 = 1 := congrArg Subtype.val hx
    have hhG : (c * (x : G)) ^ 2 = 1 := congrArg Subtype.val hh
    rwa [(hcomm x x.property).mul_pow, hxG, mul_one] at hhG
  have hle := Set.ncard_le_ncard hm
  rw [hi.ncard_image] at hle
  have hsum := Set.ncard_add_ncard_compl S
  have he : ({x : G | x ∈ K ∧ x ^ 2 = 1} : Set G) = Subtype.val '' S := by
    ext x
    constructor
    · rintro ⟨hx, hx2⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hx2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.property, congrArg Subtype.val hx⟩
  rw [he, Set.ncard_image_of_injective _ Subtype.val_injective]
  omega

variable {z : G} {V : Subgroup G}

private theorem central_four (h : TypeAt z V) :
    ∃ c : G, c ∈ (involutionCentralizer z).pCoreIn 2 ∧
      (∀ x ∈ (involutionCentralizer z).pCoreIn 2, Commute c x) ∧ c ^ 2 ≠ 1 := by
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  have hs : CoreShape Q := (h.centralizer_core.of_equiv
    (MulEquiv.subgroupCongr h.centralizer_fitting)).of_equiv
      ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective)
  obtain ⟨e⟩ := hs.center_model
  let c : center Q := e.symm (Multiplicative.ofAdd (1 : ZMod 4))
  refine ⟨c.val, c.val.property, ?_, ?_⟩
  · intro x hx
    exact (congrArg (fun a : Q => (a : G))
      (mem_center_iff.mp c.property (⟨x, hx⟩ : Q))).symm
  · intro hh
    have hh' : c ^ 2 = 1 := Subtype.ext (Subtype.ext hh)
    have he := congrArg e hh'
    have hn : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 ≠ 1 := by decide +kernel
    exact hn (by simpa only [map_pow, map_one, MulEquiv.apply_symm_apply, c] using he)

private theorem point_core_map (e : MulAut G) (x : G) :
    ((involutionCentralizer x).pCoreIn 2).map e.toMonoidHom =
      (involutionCentralizer (e x)).pCoreIn 2 := by
  have hc : (involutionCentralizer x).map e.toMonoidHom = involutionCentralizer (e x) := by
    ext y
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    rw [← e.injective.eq_iff]
    simp only [map_mul, MulEquiv.apply_symm_apply]
  rw [map_pCoreIn_of_ker_isPGroup _ (by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    exact IsPGroup.of_subsingleton 2 (⊥ : Subgroup G)), hc]

private theorem point_core_involution_centralizer_card (h : TypeAt z V)
    (x : G) (hx : x ∈ (involutionCentralizer z).pCoreIn 2)
    (hx2 : x ^ 2 = 1) (hxz : x ∉ zpowers z) :
    Nat.card ((involutionCentralizer z).pCoreIn 2 ⊓ involutionCentralizer x : Subgroup G) = 32 := by
  have hx1 : x ≠ 1 := fun he => hxz (he ▸ (zpowers z).one_mem)
  obtain ⟨g, w, hw, he⟩ := h.centralizer_core_involution_seed_conjugate x hx
    (orderOf_eq_prime hx2 hx1)
  let e := MulAut.conj (g : G)
  have hzfix : e z = z := by
    change (g : G) * z * (g : G)⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp g.property, mul_inv_cancel_right]
  have hw1 : w ≠ 1 := by
    intro hw1
    exact hx1 (he.symm.trans (by rw [hw1, map_one]))
  have hwz : w ≠ z := by
    intro hwz
    have hxz' : x = z := he.symm.trans (hwz ▸ hzfix)
    exact hxz (hxz' ▸ mem_zpowers z)
  have hc : (involutionCentralizer w).map e.toMonoidHom = involutionCentralizer x := by
    rw [← he]
    change (centralizer ({w} : Set G)).map e.toMonoidHom = centralizer ({e w} : Set G)
    ext y
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    rw [← e.injective.eq_iff]
    simp only [map_mul, MulEquiv.apply_symm_apply]
  have hm : (((involutionCentralizer z).pCoreIn 2 ⊓ involutionCentralizer w : Subgroup G).map
      e.toMonoidHom) = (involutionCentralizer z).pCoreIn 2 ⊓ involutionCentralizer x := by
    rw [map_inf _ _ _ e.injective, point_core_map, hzfix, hc]
  rw [← hm, card_map_of_injective e.injective]
  exact h.point_core_other_point_centralizer_card w hw hw1 hwz

private theorem square_outside_bound (K A : Subgroup G) (hAK : A ≤ K)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (c : G) (hc : c ∈ K)
    (hcomm : ∀ x ∈ K, Commute c x) (hc2 : c ^ 2 ≠ 1) :
    2 * (Nat.card {x : G // x ∈ K ∧ x ^ 2 = 1 ∧ x ∉ A} + Nat.card A) ≤ Nat.card K := by
  let S : Set G := {x | x ∈ K ∧ x ^ 2 = 1}
  have hAS : (A : Set G) ⊆ S := fun a ha => ⟨hAK ha, hA2 a ha⟩
  have hd := Set.ncard_sdiff_add_ncard_of_subset hAS
  have he : S \ (A : Set G) = {x : G | x ∈ K ∧ x ^ 2 = 1 ∧ x ∉ A} := by
    ext x
    exact and_assoc
  rw [he] at hd
  have hb := square_one_bound K c hc hcomm hc2
  change 2 * S.ncard ≤ Nat.card K at hb
  rw [← hd] at hb
  exact hb

private abbrev coreX (z : G) :=
  {x : G // x ∈ (involutionCentralizer z).pCoreIn 2 ∧ x ^ 2 = 1 ∧ x ∉ zpowers z}

private abbrev coreY (z : G) (x : coreX z) :=
  {y : G // y ∈ (involutionCentralizer z).pCoreIn 2 ∧ y ^ 2 = 1 ∧
    Commute x.val y ∧ y ∉ (zpowers z ⊔ zpowers x.val : Subgroup G)}

private theorem coreX_card_le (h : TypeAt z V) : Nat.card (coreX z) ≤ 30 := by
  let Q := (involutionCentralizer z).pCoreIn 2
  have hVQ : V ≤ Q := by
    change V ≤ (pCore 2 (involutionCentralizer z)).map (involutionCentralizer z).subtype
    rw [← h.centralizer_fitting]
    exact h.seed_le_core
  obtain ⟨c, hc, hcomm, hc2⟩ := central_four h
  have hz2 : ∀ a ∈ zpowers z, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    have he : (z ^ n) ^ 2 = (z ^ 2) ^ n := by
      simpa only [zpow_ofNat] using zpow_comm z n (2 : ℤ)
    have hzsq : z ^ 2 = 1 := h.involution ▸ pow_orderOf_eq_one z
    rw [he, hzsq, one_zpow]
  have hb := square_outside_bound Q (zpowers z)
    (zpowers_le.mpr (hVQ h.involution_mem_seed)) hz2 c hc hcomm hc2
  have hQ : Nat.card Q = 64 := by
    change Nat.card ((pCore 2 (involutionCentralizer z)).map (involutionCentralizer z).subtype) = 64
    rw [card_map_of_injective (involutionCentralizer z).subtype_injective,
      ← h.centralizer_fitting]
    exact h.centralizer_core_card
  rw [Nat.card_zpowers, h.involution, hQ] at hb
  change 2 * (Nat.card (coreX z) + 2) ≤ 64 at hb
  omega

private theorem coreY_card_le (h : TypeAt z V) (x : coreX z) : Nat.card (coreY z x) ≤ 12 := by
  let Q := (involutionCentralizer z).pCoreIn 2
  let K := Q ⊓ involutionCentralizer x.val
  let B := zpowers z ⊔ zpowers x.val
  have hK : Nat.card K = 32 :=
    point_core_involution_centralizer_card h x x.property.1 x.property.2.1 x.property.2.2
  have hzQ : z ∈ Q := by
    change z ∈ (pCore 2 (involutionCentralizer z)).map (involutionCentralizer z).subtype
    rw [← h.centralizer_fitting]
    exact h.seed_le_core h.involution_mem_seed
  have hzx : Commute z x.val :=
    (mem_centralizer_singleton_iff.mp (pCoreIn_le 2 _ x.property.1)).symm
  have hBK : B ≤ K := sup_le
    (zpowers_le.mpr ⟨hzQ, mem_centralizer_singleton_iff.mpr hzx⟩)
    (zpowers_le.mpr ⟨x.property.1, mem_centralizer_singleton_iff.mpr rfl⟩)
  have hxN : x.val ∈ normalizer (zpowers z : Set G) := by
    apply centralizer_le_normalizer
    intro a ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    exact (hzx.zpow_left n).eq
  have hB4 : Nat.card B = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution _ _ x.property.2.1 x.property.2.2]
    · rw [Nat.card_zpowers, h.involution]
    · exact hxN
  have hB2 : ∀ a ∈ B, a ^ 2 = 1 := by
    have hn : zpowers x.val ≤ normalizer (zpowers z : Set G) := zpowers_le.mpr hxN
    intro a ha
    change a ∈ (↑(zpowers z ⊔ zpowers x.val) : Set G) at ha
    rw [coe_mul_of_right_le_normalizer_left _ _ hn] at ha
    obtain ⟨a, ha, b, hb, rfl⟩ := ha
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
    have hez : (z ^ m) ^ 2 = (z ^ 2) ^ m := by
      simpa only [zpow_ofNat] using zpow_comm z m (2 : ℤ)
    have hex : (x.val ^ n) ^ 2 = (x.val ^ 2) ^ n := by
      simpa only [zpow_ofNat] using zpow_comm x.val n (2 : ℤ)
    have hzsq : z ^ 2 = 1 := h.involution ▸ pow_orderOf_eq_one z
    rw [(hzx.zpow_zpow m n).mul_pow, hez, hex,
      hzsq, x.property.2.1, one_zpow, one_zpow, one_mul]
  obtain ⟨c, hc, hcomm, hc2⟩ := central_four h
  have hcK : c ∈ K := ⟨hc, mem_centralizer_singleton_iff.mpr (hcomm x x.property.1)⟩
  have hb := square_outside_bound K B hBK hB2 c hcK (fun y hy => hcomm y hy.1) hc2
  have he : coreY z x ≃ {y : G // y ∈ K ∧ y ^ 2 = 1 ∧ y ∉ B} := {
    toFun y := ⟨y, ⟨y.property.1, mem_centralizer_singleton_iff.mpr y.property.2.2.1.symm⟩,
      y.property.2.1, y.property.2.2.2⟩
    invFun y := ⟨y, y.property.1.1, y.property.2.1,
      (mem_centralizer_singleton_iff.mp y.property.1.2).symm, y.property.2.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [← Nat.card_congr he, hB4, hK] at hb
  omega

/-- There are at most fifteen literal elementary-eight subgroups in the
original marked point core which contain its marked involution. -/
theorem TypeAt.point_core_eights_count (h : TypeAt z V) : Nat.card (pointCoreEights z) ≤ 15 := by
  classical
  let := Fintype.ofFinite (pointCoreEights z)
  let := Fintype.ofFinite (coreX z)
  let T := Σ E : pointCoreEights z, eightPairs E.val z
  let U := Σ x : coreX z, coreY z x
  have hT : Nat.card T = Nat.card (pointCoreEights z) * 24 := by
    change Nat.card (Σ E : pointCoreEights z, eightPairs E.val z) = _
    rw [Nat.card_sigma]
    have hh (E : pointCoreEights z) : Nat.card (eightPairs E.val z) = 24 := by
      let := E.property.2.2.1
      exact eight_pairs_card E.val z E.property.2.1 h.involution E.property.2.2.2
    simp only [hh, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  have hU : Nat.card U ≤ 360 := by
    change Nat.card (Σ x : coreX z, coreY z x) ≤ _
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _ : coreX z, 12 := Finset.sum_le_sum fun x _ => coreY_card_le h x
      _ = Nat.card (coreX z) * 12 := by simp [← Nat.card_eq_fintype_card]
      _ ≤ 360 := by have hh := coreX_card_le h; omega
  let f : T → U := fun p => by
    let E := p.1
    let := E.property.2.2.1
    refine ⟨⟨p.2.1.val, E.property.1 p.2.1.val.property,
      elemPow_eq_one_of_isElementaryAbelian _ p.2.1.val.property, p.2.1.property⟩,
      ⟨p.2.2.val, E.property.1 p.2.2.val.property,
        elemPow_eq_one_of_isElementaryAbelian _ p.2.2.val.property, ?_, p.2.2.property⟩⟩
    exact congrArg Subtype.val (mul_comm p.2.1.val p.2.2.val)
  have hf : Function.Injective f := by
    rintro ⟨E, p⟩ ⟨F, q⟩ he
    have hx : (p.1.val : G) = q.1.val := congrArg (fun r : U => r.1.val) he
    have hy : (p.2.val : G) = q.2.val := congrArg (fun r : U => r.2.val) he
    have hEF : E = F := by
      apply Subtype.ext
      let := E.property.2.2.1
      let := F.property.2.2.1
      rw [eight_pairs_generate E.val z E.property.2.1 h.involution E.property.2.2.2 p,
        eight_pairs_generate F.val z F.property.2.1 h.involution F.property.2.2.2 q]
      exact congrArg₂ (fun x y : G => (zpowers z ⊔ zpowers x) ⊔ zpowers y) hx hy
    subst F
    have hpx : p.1 = q.1 := Subtype.ext (Subtype.ext hx)
    have hp : p = q := by
      apply Sigma.ext hpx
      cases p with | mk px py =>
        cases q with | mk qx qy =>
          dsimp only at hpx hy
          subst qx
          exact heq_of_eq (Subtype.ext (Subtype.ext hy))
    cases hp
    rfl
  have hc := Nat.card_le_card_of_injective f hf
  rw [hT] at hc
  omega

end CFSG.Quasithin.HigmanSims
