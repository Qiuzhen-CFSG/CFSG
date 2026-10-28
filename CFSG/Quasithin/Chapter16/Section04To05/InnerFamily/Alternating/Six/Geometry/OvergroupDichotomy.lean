module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Setup
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Geometry.ModelFacts
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Geometry.ActionImage
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.NormalizedSupCard
import Mathlib.Tactic

/-!
# The ordinary or full automorphism overgroup for A₆

The marked product model realizes LE as S₆ × C₂. If the actual normalizer
image on L is the natural S₆, the image of T is a Sylow subgroup of order
16. Its kernel is T ∩ C_G(L) = ⟨z⟩, of order two, so |T| = 32.
Restricting T inside N_G(L) to its normal subgroup L gives |T ∩ L| = 8.
The normalized product formula therefore gives |LT| = 1440 = |LE|;
the marked generators r,z lie in T, so LE ≤ LT and equality follows.

Combining this equality with the actual action-image alternative gives
LT = LE or surjectivity onto Aut(A₆), in any supplied coordinates for L.
Only normality of L inside N_G(L) is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.Six
open AlternatingSix.ShadowLocal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G} {z r : G}

private theorem ordinary_sylow_card (h : StandardSetup T z L)
    (hTC : commutingSylow T L = zpowers z) (M : AlternatingProductModel L z r 6)
    (hnatural : (modelNormalizerAction M).range = natural) : Nat.card T = 32 := by
  let f := (modelNormalizerAction M).rangeRestrict
  let a := f.comp (inclusion h.sylow_normalizes)
  let P := (T.subtype h.sylow_normalizes).mapSurjective
    (modelNormalizerAction M).rangeRestrict_surjective
  have hP : (P : Subgroup (modelNormalizerAction M).range) = a.range := by
    ext b
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨(n : G), hn⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨inclusion h.sylow_normalizes t, t.property, rfl⟩
  have hk : a.ker = (centralizer (L : Set G)).subgroupOf (T : Subgroup G) := by
    change (f.comp _).ker = _
    rw [← MonoidHom.comap_ker, MonoidHom.ker_rangeRestrict]
    change (((MulAut.congr (modelComponentEquiv M)).toMonoidHom.comp
      L.normalizerMonoidHom).ker).comap _ = _
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.congr _).injective,
      normalizerMonoidHom_ker]
    rfl
  have hK : Nat.card a.ker = 2 := by
    have he : a.ker.map (T : Subgroup G).subtype = zpowers z := by
      rw [hk, subgroupOf_map_subtype, inf_comm]
      exact hTC
    rw [← card_map_of_injective (T : Subgroup G).subtype_injective, he,
      Nat.card_zpowers, h.involution]
  have hI : Nat.card a.range = 16 := by
    rw [← hP, P.card_eq_multiplicity, hnatural, card_natural]
    rw [show 720 = 2 ^ 4 * 45 by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
    rfl
  have hh := a.ker.card_mul_index
  rw [index_ker, hK, hI] at hh
  exact hh.symm

private theorem component_intersection_card (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) :
    Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) = 8 := by
  let N := normalizer (L : Set G)
  let LN := L.subgroupOf N
  let P := T.subtype h.sylow_normalizes
  obtain ⟨Q, hQ⟩ := P.exists_sylow_map_eq_inf_of_normal LN
  have hLN : Nat.card LN = 360 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe L.le_normalizer).toEquiv,
      Nat.card_congr e.toEquiv, card_A6]
  have hQc : Nat.card Q = 8 := by
    rw [Q.card_eq_multiplicity, hLN]
    rw [show 360 = 2 ^ 3 * 45 by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
    rfl
  have hmap : ((Q : Subgroup LN).map LN.subtype).map N.subtype =
      (T : Subgroup G) ⊓ L := by
    rw [hQ, map_inf _ _ _ N.subtype_injective]
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le h.sylow_normalizes,
      map_subgroupOf_eq_of_le L.le_normalizer]
  rw [← hmap, card_map_of_injective N.subtype_injective,
    card_map_of_injective LN.subtype_injective, hQc]

/-- When the actual normalizer image is the natural S₆, the marked product
already exhausts LT. No placement of a model Sylow subgroup is assumed. -/
theorem sup_sylow_eq_overgroup_of_natural (h : StandardSetup T z L) (hr : r ∈ T)
    (hTC : commutingSylow T L = zpowers z)
    (M : AlternatingProductModel L z r 6)
    (hnatural : (modelNormalizerAction M).range = natural) :
    L ⊔ (T : Subgroup G) = AlternatingOvergroup L z r := by
  have hL : Nat.card L = 360 := by
    rw [Nat.card_congr (modelComponentEquiv M).toEquiv, card_A6]
  have hT := ordinary_sylow_card h hTC M hnatural
  have hTL := component_intersection_card h (modelComponentEquiv M)
  have hLT : Nat.card (L ⊔ (T : Subgroup G) : Subgroup G) = 1440 := by
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes L
      (T : Subgroup G) h.sylow_normalizes
    rw [hL, hT, inf_comm L, hTL] at hc
    omega
  have hLE : Nat.card (AlternatingOvergroup L z r) = 1440 := by
    rw [Nat.card_congr M.equiv.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  apply Eq.symm
  apply eq_of_le_of_card_ge
  · exact sup_le (sup_le le_sup_left ((zpowers_le.mpr hr).trans le_sup_right))
      ((zpowers_le.mpr h.mem_sylow).trans le_sup_right)
  · omega

/-- The ambient ordinary/full dichotomy in the A₆ branch of 16.4.9(2).
The full case is the genuine normalizer action in the caller's coordinates. -/
theorem overgroup_dichotomy (h : StandardSetup T z L) (hr : r ∈ T)
    (hTC : commutingSylow T L = zpowers z)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6) :
    L ⊔ (T : Subgroup G) = AlternatingOvergroup L z r ∨ FullAutomorphismCase e := by
  rcases modelNormalizerAction_range_alternative M with hnatural | hfull
  · exact Or.inl (sup_sylow_eq_overgroup_of_natural h hr hTC M hnatural)
  · exact Or.inr ((modelNormalizerAction_surjective_iff M e).mp hfull)

end CFSG.Quasithin.Chapter16.Intersections.Six
