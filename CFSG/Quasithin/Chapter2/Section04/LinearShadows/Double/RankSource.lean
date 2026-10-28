module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.Rank

/-!
# The terminal odd-rank contradiction in the double linear source

An odd prime dividing the independent faithful torus contributes rank one.
If the actual conjugate-generated subgroup centralizing that torus has rank
two at the same prime, their disjoint commuting product has rank three in
the two-local normalizer of the nontrivial fixed factor. Quasithinness excludes
it. This is the exact mathematical input needed from component recognition.

Source: Aschbacher–Smith, end of the double linear case, printed p.541.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.LinearDouble
variable {G : Type*} [Group G] [Finite G]

/-- The terminal source contradiction only needs a rank-two section for one
prime dividing the independent torus. No further model identification is used. -/
theorem false_of_conjugate_generated_rank (R D L : Subgroup G) (x : G)
    (hG : IsQuasithin G) (hR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hDN : D ≤ normalizer (R : Set G))
    (hfaith : Function.Injective (R.normalizerMonoidHom.comp (inclusion hDN)))
    (hL : L ≤ centralizer ((R ⊔ D : Subgroup G) : Set G))
    (hxR : x ∈ normalizer (R : Set G)) (hxD : x ∈ normalizer (D : Set G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hdD : p ∣ Nat.card D)
    (hKrank : 2 ≤ primeRank p (L ⊔ L.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G)) :
    False := by
  let : Fact p.Prime := ⟨hp⟩
  let K := L ⊔ L.map (MulAut.conj x⁻¹).toMonoidHom
  have hx : x ∈ normalizer ((R ⊔ D : Subgroup G) : Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup R D ⟨hxR,hxD⟩
  have hK : K ≤ centralizer ((R ⊔ D : Subgroup G) : Set G) := by
    apply sup_le hL
    have hi := normalizer_le_normalizer_centralizer (R ⊔ D) hx
    have hii := (normalizer ((centralizer ((R ⊔ D : Subgroup G) : Set G)) : Set G)).inv_mem hi
    have hm := mem_normalizer_iff_map_conj_eq.mp hii
    exact (map_mono hL).trans hm.le
  have hKD : K ≤ centralizer (D : Set G) := hK.trans
    (centralizer_le (show D ≤ R ⊔ D from le_sup_right))
  have hKR : K ≤ centralizer (R : Set G) := hK.trans
    (centralizer_le (show R ≤ R ⊔ D from le_sup_left))
  have hd : Disjoint K D := by
    apply disjoint_def.mpr
    intro a haK haD
    have hk : (⟨a,hDN haD⟩ : normalizer (R : Set G)) ∈ R.normalizerMonoidHom.ker := by
      rw [normalizerMonoidHom_ker]
      exact hKR haK
    have he : R.normalizerMonoidHom.comp (inclusion hDN) ⟨a,haD⟩ = 1 := hk
    exact congrArg Subtype.val (hfaith (he.trans (map_one _).symm))
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := D) p hdD
  let : IsElementaryAbelian p (zpowers a) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (ha ▸ pow_orderOf_eq_one a)
  have hD : 1 ≤ primeRank p D := IsElementaryAbelian.primeRank_ge_of_card (zpowers a)
    (by simp only [Nat.card_zpowers,ha,pow_one])
  change 2 ≤ primeRank p K at hKrank
  have hsum := primeRank_sup_eq_add_of_disjoint_commuting K D hd hKD p
  have hloc : IsTwoLocal (normalizer (R : Set G)) := ⟨R,hne,hR,rfl⟩
  have hbound := CFSG.Quasithin.isQuasithin_iff_twoLocal.mp hG
    (normalizer (R : Set G)) hloc p hp ho
  have hle := primeRank_mono p (sup_le (hKR.trans (centralizer_le_normalizer _)) hDN)
  omega

end CFSG.Quasithin.Chapter2.LinearDouble
