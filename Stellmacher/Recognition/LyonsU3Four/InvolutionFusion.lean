module

public import Stellmacher.Recognition.LyonsU3Four.Basic
public import Glauberman.ZStar
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Involution fusion in Lyons's Sylow configuration

Simplicity makes the odd core and ambient center trivial. The Z-star theorem
therefore gives each of the three involutions in the Sylow center a distinct
conjugate there. Three elements cannot split into classes of size at least two,
so they form one ambient class. Burnside fusion realizes their conjugacy in the
normalizer of the supplied Sylow subgroup.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 1,
p. 372, first paragraph of the proof.
-/

namespace Stellmacher.Recognition.LyonsU3Four

public theorem oddCore_eq_bot {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) : pPrimeCore 2 G = ⊥ := by
  rcases (pPrimeCore_normal (p := 2) (G := G)).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have hc := pPrimeCore_coprime_card (p := 2) (G := G)
    rw [ht, Subgroup.card_top] at hc
    have hd : 2 ∣ Nat.card G := (by norm_num : 2 ∣ 64).trans
      (h.card ▸ (S : Subgroup G).card_subgroup_dvd_card)
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hc hd).elim

public theorem ambient_center_eq_bot
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) : Subgroup.center G = ⊥ := by
  rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · let : IsMulCommutative G := Subgroup.center_eq_top_iff.mp ht
    have hnormal := (centerImage S).normal_of_isMulCommutative
    exact (normalizer_centerImage_ne_top S h
      (Subgroup.normalizer_eq_top_iff.mpr hnormal)).elim

public theorem centerImage_le_centralizer_sylow {G : Type*} [Group G]
    (S : Sylow 2 G) : centerImage S ≤ Subgroup.centralizer (S : Set G) :=
  Subgroup.le_centralizer_iff.mp (sylow_le_centralizer_centerImage S)

/-- No nonidentity element of the Sylow center is weakly closed. -/
public theorem exists_distinct_conjugate_in_centerImage
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) {x : G}
    (hx : x ∈ centerImage S) (hx1 : x ≠ 1) :
    ∃ y ∈ centerImage S, y ≠ x ∧ IsConj x y := by
  classical
  let := centerImage_elementary S h
  have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  by_contra! hn
  have hweak : Glauberman.ZStar.IsWeaklyClosedInSylow x (S : Subgroup G) := by
    refine ⟨centerImage_le S hx, ?_⟩
    intro g hg
    have hg2 : (g * x * g⁻¹) ^ 2 = 1 := by
      simpa only [map_pow, map_one, MulAut.conj_apply] using
        congrArg (MulAut.conj g) hx2
    have hgz := involution_mem_centerImage S h hg hg2
    by_contra hne
    exact hn _ hgz hne (isConj_iff.mpr ⟨g, rfl⟩)
  have hc := Glauberman.ZStar.glauberman_zstar_corefree (oddCore_eq_bot S h)
    S x ⟨hx1, hx2⟩ (centerImage_le S hx)
    (fun s hs => (Subgroup.mem_centralizer_iff.mp
      (centerImage_le_centralizer_sylow S hx) s hs)) hweak
  rw [ambient_center_eq_bot S h, Subgroup.mem_bot] at hc
  exact hx1 hc

/-- The three nonidentity center elements belong to a single ambient class. -/
public theorem centerImage_nonidentity_isConj
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) {x y : G}
    (hx : x ∈ centerImage S) (hy : y ∈ centerImage S)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : IsConj x y := by
  classical
  by_contra hn
  obtain ⟨u, hu, hux, hxu⟩ := exists_distinct_conjugate_in_centerImage S h hx hx1
  obtain ⟨v, hv, hvy, hyv⟩ := exists_distinct_conjugate_in_centerImage S h hy hy1
  have hu1 : u ≠ 1 := fun he => hx1 (isConj_one_left.mp (he ▸ hxu))
  have hv1 : v ≠ 1 := fun he => hy1 (isConj_one_left.mp (he ▸ hyv))
  have hxy : x ≠ y := fun he => hn (he ▸ IsConj.refl x)
  have hxu' : x ≠ u := Ne.symm hux
  have hxv : x ≠ v := fun he => hn ((he ▸ hyv).symm)
  have hyu : y ≠ u := fun he => hn (he ▸ hxu)
  have hyv' : y ≠ v := Ne.symm hvy
  have huv : u ≠ v := fun he => hn (hxu.trans (he ▸ hyv.symm))
  let := Fintype.ofFinite (centerImage S)
  let a : centerImage S := ⟨x, hx⟩
  let b : centerImage S := ⟨y, hy⟩
  let c : centerImage S := ⟨u, hu⟩
  let d : centerImage S := ⟨v, hv⟩
  have hcard := Finset.card_le_univ ({1, a, b, c, d} : Finset (centerImage S))
  have hnat : Fintype.card (centerImage S) = 4 := by
    rw [← Nat.card_eq_fintype_card, centerImage_card S h]
  have hfive : ({1, a, b, c, d} : Finset (centerImage S)).card = 5 := by
    simp [a, b, c, d, Subtype.ext_iff, hxy, hxu', hxv,
      hyu, hyv', huv, Ne.symm hx1, Ne.symm hy1, Ne.symm hu1, Ne.symm hv1]
  omega

/-- Burnside fusion realizes the transitive center action inside the Sylow normalizer. -/
public theorem centerImage_nonidentity_normalizer_conjugate
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) {x y : G}
    (hx : x ∈ centerImage S) (hy : y ∈ centerImage S)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (S : Set G), n⁻¹ * x * n = y := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (centerImage_nonidentity_isConj S h hx hy hx1 hy1)
  obtain ⟨n, hn, he⟩ := S.conj_eq_normalizer_conj_of_mem_centralizer x g⁻¹
    (centerImage_le_centralizer_sylow S hx)
    (by simpa only [inv_inv, hg] using centerImage_le_centralizer_sylow S hy)
  exact ⟨n, hn, he.symm.trans (by simpa only [inv_inv] using hg)⟩

/-- Every ambient involution has a conjugate in the supplied Sylow center. -/
public theorem involution_isConj_centerImage
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) {x : G} (hx : orderOf x = 2) :
    ∃ y ∈ centerImage S, y ≠ 1 ∧ IsConj x y := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hxy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1)
    (by simpa using hx)
  have hx1 : x ≠ 1 := by
    intro he
    simp [he] at hx
  have hy1 : (y : G) ≠ 1 := fun he => hx1 (isConj_one_left.mp (he ▸ hxy))
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have hy2 : (y : G) ^ 2 = 1 :=
    isConj_one_right.mp (by simpa only [hx2] using IsConj.pow 2 hxy)
  exact ⟨y, involution_mem_centerImage S h y.property hy2, hy1, hxy⟩

/-- Lemma 1(a), the unique ambient class of involutions. -/
public theorem involutions_isConj
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) {x y : G}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨u, hu, hu1, hxu⟩ := involution_isConj_centerImage S h hx
  obtain ⟨v, hv, hv1, hyv⟩ := involution_isConj_centerImage S h hy
  exact hxu.trans ((centerImage_nonidentity_isConj S h hu hv hu1 hv1).trans hyv.symm)

end Stellmacher.Recognition.LyonsU3Four
