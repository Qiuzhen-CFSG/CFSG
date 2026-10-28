module
public import Theory.GroupTheory.MarkedCentralProductQuotient
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PGroup.OrderTwentySeven
open Subgroup
open scoped IsMulCommutative
/-!
# Cubic roots in a rank-four central product

This module packages the factor-level extraction in the proof of
Aschbacher--Smith A.2.12(II), printed p.37. A rank-four elementary cubic
subgroup has order 81 after the two factor projections are bounded by rank
two. The resulting order-27 factor preimages are abelian and their cube maps
cover the marked order-three centers. The quotient maps and original factor
embeddings remain explicit, so the result is suitable for the SU₃ central
product consumer.
-/

namespace CubicProductRankFour
private theorem card_comap_center {G : Type*} [Group G] [Finite G]
    (U : Subgroup (G ⧸ center G)) :
    Nat.card (U.comap (QuotientGroup.mk' (center G))) =
      Nat.card U * Nat.card (center G) := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero U.index_ne_zero_of_finite)
  calc
    Nat.card (U.comap (QuotientGroup.mk' (center G))) * U.index = Nat.card G := by
      rw [← U.index_comap_of_surjective (QuotientGroup.mk'_surjective (center G))]
      exact (U.comap (QuotientGroup.mk' (center G))).card_mul_index
    _ = Nat.card (G ⧸ center G) * Nat.card (center G) :=
      card_eq_card_quotient_mul_card_subgroup (center G)
    _ = (Nat.card U * Nat.card (center G)) * U.index := by
      rw [← U.card_mul_index]
      ac_rfl

private theorem exists_abelian_cube_root_factor
    {H : Type*} [Group H] [Finite H] (A B E : Subgroup H)
    (hc : A ≤ centralizer (B : Set H))
    (hprod : ∀ h : H, ∃ a : A, ∃ b : B, (a : H) * b = h)
    (q : H →* (A ⧸ center A))
    (hq : ∀ (a : A) (b : B), q ((a : H) * b) = QuotientGroup.mk' (center A) a)
    [IsElementaryAbelian 3 E]
    (himage : Nat.card (E.map q) = 9)
    (hinter : Nat.card (E.subgroupOf A) = 9)
    (hcenter : Nat.card (center A) = 3) (hrank : primeRank 3 A ≤ 2) :
    ∃ P : Subgroup A, IsMulCommutative P ∧ Nat.card P = 27 ∧ center A ≤ P ∧
      (∀ a ∈ P, a ^ 3 ∈ center A) ∧
      (∀ z ∈ center A, ∃ a : P, (a : A) ^ 3 = z) := by
  let qa := QuotientGroup.mk' (center A)
  let P := (E.map q).comap qa
  have hZP : center A ≤ P := by
    intro a ha
    change qa a ∈ E.map q
    rw [show qa a = 1 from (QuotientGroup.eq_one_iff _).mpr ha]
    exact one_mem _
  have hP : Nat.card P = 27 := by
    rw [card_comap_center, himage, hcenter]
  have hcub (a : A) (ha : a ∈ P) : a ^ 3 ∈ center A := by
    let : IsElementaryAbelian 3 (E.map q) := IsElementaryAbelian.map q
    apply (QuotientGroup.eq_one_iff _).mp
    change qa (a ^ 3) = 1
    rw [map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian (A := E.map q) _ ha
  have hIP : E.subgroupOf A ≤ P := by
    intro a ha
    change qa a ∈ E.map q
    refine mem_map.mpr ⟨(a : H),ha,?_⟩
    simpa only [Subgroup.coe_one,mul_one] using hq a 1
  have hcent : E.subgroupOf A ≤ (center P).map P.subtype := by
    intro u hu
    refine mem_map.mpr ⟨⟨u,hIP hu⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    obtain ⟨e,he,heq⟩ := a.property
    obtain ⟨a',b',heprod⟩ := hprod e
    have hqa : qa a' = qa (a : A) := by
      rw [← hq a' b', heprod]
      exact heq
    have hdiff : a'⁻¹ * (a : A) ∈ center A := by
      apply (QuotientGroup.eq_one_iff _).mp
      change qa (a'⁻¹ * (a : A)) = 1
      rw [map_mul,map_inv,hqa,inv_mul_cancel]
    have hue : (u : H) * e = e * u :=
      congrArg Subtype.val (mul_comm (⟨u,hu⟩ : E) ⟨e,he⟩)
    have hub : (u : H) * b' = (b' : H) * u := (hc u.property b' b'.property).symm
    have hua' : u * a' = a' * u := by
      apply Subtype.ext
      apply mul_right_cancel (b := (b' : H))
      change ((u : H) * a') * b' = ((a' : H) * u) * b'
      calc
        ((u : H) * a') * b' = (u : H) * e := by rw [mul_assoc,heprod]
        _ = e * u := hue
        _ = ((a' : H) * u) * b' := by rw [← heprod,mul_assoc,← hub,mul_assoc]

    have hud : u * (a'⁻¹ * (a : A)) = (a'⁻¹ * (a : A)) * u :=
      mem_center_iff.mp hdiff u
    have huap : u * (a : A) = (a : A) * u := by
      have h := (show Commute u a' from hua').mul_right (show Commute u (a'⁻¹ * (a : A)) from hud)
      simpa only [mul_inv_cancel_left] using h.eq
    exact huap.symm
  have hab : IsMulCommutative P := by
    by_contra hn
    have hs := card_le_of_le hcent
    rw [card_map_of_injective P.subtype_injective, hinter, OrderTwentySeven.center_card hP hn] at hs
    omega
  let : IsMulCommutative P := hab
  let : CommGroup P := IsMulCommutative.instCommGroup
  let f : P →* center A :=
    { toFun := fun a => ⟨(a : A)^3,hcub a a.property⟩
      map_one' := Subtype.ext (one_pow 3)
      map_mul' := fun a b => Subtype.ext (congrArg (fun x : P => (x : A)) (mul_pow a b 3)) }
  have hf : Function.Surjective f := by
    by_contra hn
    have hr : f.range = ⊥ := by
      have hd : Nat.card f.range ∣ 3 := hcenter ▸ f.range.card_subgroup_dvd_card
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with hone | hthree
      · exact card_eq_one.mp hone
      · exact (hn (MonoidHom.range_eq_top.mp (eq_top_of_card_eq _ (hthree.trans hcenter.symm)))).elim
    have hall (a : P) : a^3=1 := by
      apply Subtype.ext
      exact congrArg (fun x : center A => (x : A)) (show f a = 1 from mem_bot.mp (hr ▸ show f a ∈ f.range from ⟨a,rfl⟩))
    let : IsElementaryAbelian 3 P :=
      { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hall }
    have hsmall := (primeRank_le_iff_elementary_card_le A).mp hrank P inferInstance
    rw [hP] at hsmall
    norm_num at hsmall
  refine ⟨P,hab,hP,hZP,hcub,?_⟩
  intro z hz
  obtain ⟨a,ha⟩ := hf ⟨z,hz⟩
  exact ⟨a,congrArg Subtype.val ha⟩

private theorem card_kernel_image {G K : Type*} [Group G] [Finite G] [Group K]
    (E : Subgroup G) (q : G →* K) :
    Nat.card (q.ker.subgroupOf E) * Nat.card (E.map q) = Nat.card E := by
  have h := (q.comp E.subtype).ker.card_mul_index
  rw [index_ker] at h
  have hr : (q.comp E.subtype).range = E.map q := by rw [← MonoidHom.map_range, E.range_subtype]
  rwa [hr] at h

private theorem intersection_card_nine
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    (E B : Subgroup H) [IsElementaryAbelian 3 E]
    (q : H →* K) (hker : q.ker = B)
    (hE : 81 ≤ Nat.card E) (hB : primeRank 3 B ≤ 2) (hK : primeRank 3 K ≤ 2) :
    Nat.card (E.subgroupOf B) = 9 ∧ Nat.card (E.map q) = 9 ∧ Nat.card E = 81 := by
  let : IsElementaryAbelian 3 (E.subgroupOf B) :=
    { toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative B E
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
        Subtype.ext (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ x.property))) }
  let : IsElementaryAbelian 3 (E.map q) := IsElementaryAbelian.map q
  have hEB := (primeRank_le_iff_elementary_card_le B).mp hB (E.subgroupOf B) inferInstance
  have hEq := (primeRank_le_iff_elementary_card_le K).mp hK (E.map q) inferInstance
  have hcard := card_kernel_image E q
  rw [hker] at hcard
  have he : Nat.card (B.subgroupOf E) = Nat.card (E.subgroupOf B) := by
    exact Nat.card_congr
      { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
        invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [he] at hcard
  change Nat.card (E.subgroupOf B) ≤ 9 at hEB
  change Nat.card (E.map q) ≤ 9 at hEq
  have hc : Nat.card (E.subgroupOf B) * Nat.card (E.map q) ≤ 81 := Nat.mul_le_mul hEB hEq
  have hcardE : Nat.card E = 81 := by omega
  have hleft : Nat.card (E.subgroupOf B) = 9 := by nlinarith
  have hright : Nat.card (E.map q) = 9 := by nlinarith
  exact ⟨hleft, hright, hcardE⟩


private theorem projection_ker
    {H : Type*} [Group H] (A B : Subgroup H)
    (hc : A ≤ centralizer (B : Set H))
    (hprod : ∀ h : H, ∃ a : A, ∃ b : B, (a : H) * b = h)
    (hZ : (center A).map A.subtype ≤ B)
    (q : H →* (A ⧸ center A))
    (hq : ∀ (a : A) (b : B), q ((a : H) * b) = QuotientGroup.mk' (center A) a) :
    q.ker = B := by
  ext h
  obtain ⟨a,b,rfl⟩ := hprod h
  change q ((a : H) * b) = 1 ↔ (a : H) * b ∈ B
  rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro ha
    exact B.mul_mem (hZ (mem_map.mpr ⟨a,ha,rfl⟩)) b.property
  · intro hab
    have haB : (a : H) ∈ B := by
      have ht := B.mul_mem hab (B.inv_mem b.property)
      simpa only [mul_inv_cancel_right] using ht
    apply mem_center_iff.mpr
    intro a'
    exact Subtype.ext ((hc a'.property a haB).symm)

public theorem exists_factors_of_rank_four
    {H : Type*} [Group H] [Finite H] (A B : Subgroup H)
    (hc : A ≤ centralizer (B : Set H))
    (hprod : ∀ h : H, ∃ a : A, ∃ b : B, (a : H) * b = h)
    (hcenters : (center A).map A.subtype = (center B).map B.subtype)
    (hAc : Nat.card (center A) = 3) (hBc : Nat.card (center B) = 3)
    (hA : primeRank 3 A ≤ 2) (hB : primeRank 3 B ≤ 2)
    (hAq : primeRank 3 (A ⧸ center A) ≤ 2)
    (hBq : primeRank 3 (B ⧸ center B) ≤ 2)
    (hH : 4 ≤ primeRank 3 H) :
    (∃ P : Subgroup A, IsMulCommutative P ∧ Nat.card P = 27 ∧ center A ≤ P ∧
      (∀ a ∈ P, a ^ 3 ∈ center A) ∧
      (∀ z ∈ center A, ∃ a : P, (a : A) ^ 3 = z)) ∧
    (∃ P : Subgroup B, IsMulCommutative P ∧ Nat.card P = 27 ∧ center B ≤ P ∧
      (∀ b ∈ P, b ^ 3 ∈ center B) ∧
      (∀ z ∈ center B, ∃ b : P, (b : B) ^ 3 = z)) := by
  obtain ⟨E,hE,hEc⟩ := exists_elementaryAbelian_card_primeRank (G := H) (p := 3)
  let : IsElementaryAbelian 3 E := hE
  have hE81 : 81 ≤ Nat.card E := by
    rw [hEc]
    exact Nat.pow_le_pow_right (by decide : 0 < 3) hH
  obtain ⟨e,he⟩ := exists_centerQuotient_product_equiv A B hc hprod
  let qA : H →* (A ⧸ center A) :=
    (MonoidHom.fst _ _).comp (e.toMonoidHom.comp (QuotientGroup.mk' (center H)))
  let qB : H →* (B ⧸ center B) :=
    (MonoidHom.snd _ _).comp (e.toMonoidHom.comp (QuotientGroup.mk' (center H)))
  have hqa (a : A) (b : B) : qA ((a : H) * b) = QuotientGroup.mk' (center A) a :=
    congrArg Prod.fst (he a b)
  have hqb (b : B) (a : A) : qB ((b : H) * a) = QuotientGroup.mk' (center B) b := by
    rw [hc a.property b b.property]
    exact congrArg Prod.snd (he a b)
  have hc' : B ≤ centralizer (A : Set H) := le_centralizer_iff.mp hc
  have hprod' (h : H) : ∃ b : B, ∃ a : A, (b : H) * a = h := by
    obtain ⟨a,b,hab⟩ := hprod h
    exact ⟨b,a,(hc a.property b b.property).trans hab⟩
  have hqaK := projection_ker A B hc hprod (hcenters ▸ map_subtype_le (center B)) qA hqa
  have hqbK := projection_ker B A hc' hprod' (hcenters.symm ▸ map_subtype_le (center A)) qB hqb
  obtain ⟨hEB,hEqa,_⟩ := intersection_card_nine E B qA hqaK hE81 hB hAq
  obtain ⟨hEA,hEqb,_⟩ := intersection_card_nine E A qB hqbK hE81 hA hBq
  exact ⟨exists_abelian_cube_root_factor A B E hc hprod qA hqa hEqa hEA hAc hA,
    exists_abelian_cube_root_factor B A E hc' hprod' qB hqb hEqb hEB hBc hB⟩

public theorem exists_matching_cube_roots_of_rank_four
    {H : Type*} [Group H] [Finite H] (A B : Subgroup H)
    (hc : A ≤ centralizer (B : Set H))
    (hprod : ∀ h : H, ∃ a : A, ∃ b : B, (a : H) * b = h)
    (hcenters : (center A).map A.subtype = (center B).map B.subtype)
    (hAc : Nat.card (center A) = 3) (hBc : Nat.card (center B) = 3)
    (hA : primeRank 3 A ≤ 2) (hB : primeRank 3 B ≤ 2)
    (hAq : primeRank 3 (A ⧸ center A) ≤ 2)
    (hBq : primeRank 3 (B ⧸ center B) ≤ 2)
    (hH : 4 ≤ primeRank 3 H) :
    ∃ (z : H) (x : A) (P : Subgroup B) (y : P),
      z ≠ 1 ∧ z ∈ (center A).map A.subtype ∧ (x : H)^3 = z ∧
      IsMulCommutative P ∧ Nat.card P = 27 ∧ center B ≤ P ∧
      (∀ b ∈ P, b ^ 3 ∈ center B) ∧ ((y : B) : H)^3 = z := by
  obtain ⟨⟨PA,_,_,_,_,hrootA⟩,⟨P,hPc,hPcard,hZP,hPcube,hrootB⟩⟩ :=
    exists_factors_of_rank_four A B hc hprod hcenters hAc hBc hA hB hAq hBq hH
  have hZne : center A ≠ ⊥ := by intro h; simp [h] at hAc
  have hex : ∃ z : A, z ∈ center A ∧ z ≠ 1 := by
    by_contra! h
    exact hZne (eq_bot_iff.mpr (fun z hz => h z hz))
  obtain ⟨z,hz,hzne⟩ := hex
  obtain ⟨x,hx⟩ := hrootA z hz
  have hzB : (z : H) ∈ (center B).map B.subtype :=
    hcenters ▸ mem_map.mpr ⟨z,hz,rfl⟩
  obtain ⟨zb,hzb,hzbeq⟩ := mem_map.mp hzB
  obtain ⟨y,hy⟩ := hrootB zb hzb
  refine ⟨z,x,P,y,?_,mem_map.mpr ⟨z,hz,rfl⟩,?_,hPc,hPcard,hZP,hPcube,?_⟩
  · intro h
    exact hzne (Subtype.ext h)
  · exact congrArg (fun a : A => (a : H)) hx
  · exact (congrArg (fun b : B => (b : H)) hy).trans hzbeq

end CubicProductRankFour
