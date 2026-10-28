module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Normalizer

/-!
# Unequal cyclic tori and their Sylow-three normalizers

For a homomorphic image of two finite cyclic groups, a reflection fixing
one factor and inverting the other supplies the alternating-pairing detector
on its Sylow-three subgroup. The factors may have different orders and
arbitrary three-adic valuations. The primary subgroup is constructed from
the actual factor Sylows, transported into the image, and is characteristic
there. A cycle normalizing the full torus therefore normalizes its primary part.

The concrete application is in `ThreeLocal.Nonsplit`, after a square-root
change of the nonsplit coroot parameters. The generator-image proof adapts
the pattern in G₂ `Nondefining/ThreePrimary/NonsplitNormalizer.lean`; its
model attribution is recorded in `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`. No G₂ model identification is used.
Source: the torus-normalizer argument underlying GLS3 §6.1.
-/

public section

open Subgroup PerfectCentralCovering.OddSylow
namespace Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit

private theorem pair_generates_image {U V G : Type*} [Group U] [Group V] [Group G]
    (j : U × V →* G) (P : Subgroup U) (Q : Subgroup V)
    (u : P) (hu : ∀ a : P, a ∈ zpowers u)
    (v : Q) (hv : ∀ b : Q, b ∈ zpowers v) :
    closure ({j (1, v), j (u, 1)} : Set G) = (P.prod Q).map j := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨(1, v), ⟨P.one_mem, v.property⟩, rfl⟩
    · exact ⟨(u, 1), ⟨u.property, Q.one_mem⟩, rfl⟩
  · rintro g ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hu ⟨a, ha⟩)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hv ⟨b, hb⟩)
    have hi' : (u : U) ^ i = a := congrArg Subtype.val hi
    have hk' : (v : V) ^ k = b := congrArg Subtype.val hk
    have hrep : j (a, b) = j (1, v) ^ k * j (u, 1) ^ i := by
      rw [← map_zpow, ← map_zpow, ← map_mul]
      congr 1
      ext <;> simp [hi', hk']
    rw [hrep]
    exact mul_mem (zpow_mem (subset_closure (by simp)) k)
      (zpow_mem (subset_closure (by simp)) i)

private theorem three_power_coprime (k : ℕ) :
    (3 ^ k).Coprime (2 * 3 ^ k - 2) := by
  cases k with
  | zero => simp
  | succ k =>
    apply Nat.Coprime.pow_left
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    rw [pow_succ]
    rintro ⟨a, ha⟩
    have hp : 0 < 3 ^ k := pow_pos (by decide) _
    omega

/-- Diagonal reflection on unequal cyclic factors constructs the primary pair
and its Sylow subgroup, without any restriction on their three-adic valuations. -/
theorem configuration_of_diagonal_normalizer
    {U V G : Type*} [CommGroup U] [CommGroup V] [Group G]
    [Finite U] [Finite V] [Finite G] [IsCyclic U] [IsCyclic V]
    (j : U × V →* G) (s c r : G)
    (hs : ∀ a b, s * j (a, b) * s⁻¹ = j (a, b⁻¹))
    (hc : orderOf c = 3) (hout : c ∉ j.range)
    (hn : c ∈ normalizer (j.range : Set G))
    (hr : ∀ a, r * j a * r⁻¹ = (j a)⁻¹) (hfix : Commute r c) :
    Nonempty (Configuration j.range) := by
  let P : Sylow 3 U := Classical.choice inferInstance
  let Q : Sylow 3 V := Classical.choice inferInstance
  let H : Subgroup (U × V) := (P : Subgroup U).prod (Q : Subgroup V)
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  obtain ⟨l, hl⟩ := Q.isPGroup'.exists_card_eq
  have hH : IsPGroup 3 H := by
    apply IsPGroup.of_card (n := k + l)
    rw [Nat.card_congr (Subgroup.prodEquiv (P : Subgroup U) (Q : Subgroup V)).toEquiv,
      Nat.card_prod, hk, hl, pow_add]
  have hHi : ¬ 3 ∣ H.index := by
    rw [index_prod]
    exact Nat.prime_three.not_dvd_mul P.not_dvd_index Q.not_dvd_index
  let R := (hH.toSylow hHi).mapSurjective j.rangeRestrict_surjective
  have hR : (R : Subgroup j.range).map j.range.subtype = H.map j := by
    rw [Sylow.coe_mapSurjective, map_map]
    rfl
  let : IsMulCommutative j.range := ⟨⟨fun x y => by
    obtain ⟨a, rfl⟩ := j.rangeRestrict_surjective x
    obtain ⟨b, rfl⟩ := j.rangeRestrict_surjective y
    exact (Commute.all a b).map j.rangeRestrict⟩⟩
  let : (R : Subgroup j.range).Characteristic := R.characteristic_of_normal inferInstance
  have hnR : c ∈ normalizer (((R : Subgroup j.range).map j.range.subtype : Subgroup G) : Set G) := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      let e := j.range.normalizerMonoidHom ⟨c, hn⟩
      exact ⟨e y, characteristic_iff_le_comap.mp inferInstance e hy, rfl⟩
    · intro hx
      obtain ⟨y, hy, he⟩ := hx
      let e := j.range.normalizerMonoidHom ⟨c, hn⟩
      refine ⟨e.symm y, characteristic_iff_le_comap.mp inferInstance e.symm hy, ?_⟩
      apply (MulAut.conj c).injective
      change (e (e.symm y)).val = c * x * c⁻¹
      simpa using he
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := P)
  obtain ⟨v, hv⟩ := IsCyclic.exists_generator (α := Q)
  have hpow : j (1, (v : V)) ^ (3 ^ l) = 1 := by
    rw [← map_pow]
    have hvpow : (v : V) ^ (3 ^ l) = 1 := by
      have h := pow_card_eq_one' (x := v)
      rw [hl] at h
      exact congrArg Subtype.val h
    simp only [Prod.pow_mk, one_pow, hvpow]
    exact j.map_one
  have hlpos : 0 < 3 ^ l := pow_pos (by decide) _
  refine ⟨{
    primary := R
    pair := {
      left := j (1, v)
      right := j (u, 1)
      actor := s
      generates := (pair_generates_image j _ _ u hu v hv).trans hR.symm
      commute := (Commute.all (1, (v : V)) ((u : U), 1)).map j
      exponent := 3 ^ l
      leftPower := 2 * 3 ^ l - 1
      rightPower := 1
      positive := by omega
      coprime := by simpa only [mul_one, Nat.sub_sub] using three_power_coprime l
      pow_eq_one := hpow
      conjugate_left := ?_
      conjugate_right := ?_ }
    cycle := c
    inverter := r
    cycle_order := hc
    cycle_outside := fun h => hout (map_subtype_le _ h)
    normalizes := hnR
    inverts := ?_
    fixes := hfix }⟩
  · rw [hs]
    have he : j (1, (v : V)) ^ (2 * 3 ^ l - 1) = (j (1, (v : V)))⁻¹ := by
      rw [pow_sub _ (by omega), pow_mul', hpow]
      simp
    rw [he]
    simpa only [Prod.inv_mk, inv_one] using (j.map_inv (1, (v : V)))
  · simpa using hs (u : U) 1
  · intro t ht
    obtain ⟨a, rfl⟩ := map_subtype_le _ ht
    exact hr a

end Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit
