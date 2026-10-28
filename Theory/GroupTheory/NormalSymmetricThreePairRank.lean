module

public import Theory.GroupTheory.NormalSymmetricThreePairRank.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Rank-two placement in a normal symmetric-three pair

Let K ≅ S₃ × S₃ be normal in a finite group A of three-rank at most two.
A two-perfect {2, 3}-subgroup B preserving both actual coordinate factors
lies in K and is a three-group.

Factor preservation gives B ≤ K C_A(K). The rank bound excludes the prime
three from the order of C_A(K), hence from the image of B in A/K. That
image is therefore a two-group, so two-perfectness kills it. Inside K,
the two sign maps vanish on B and every element of B has cube one.

Source: the placement step in Aschbacher–Smith, proof of 13.8.5,
combined manuscript of 1 March 2004, printed p.947 (PDF p.964).
-/

public section

open Subgroup
namespace Theory.GroupTheory.NormalSymmetricThreePairRank
local notation "S3" => Equiv.Perm (Fin 3)
variable {A : Type*} [Group A] [Finite A] (K : Subgroup A) [K.Normal]

/-- Two-perfect {2, 3}-subgroups preserving both factors lie in the normal pair
when the ambient three-rank is at most two. -/
theorem le_pair (e : K ≃* (S3 × S3)) (B : Subgroup A)
    (hB : IsPPerfect 2 B) (hrank : primeRank 3 A ≤ 2)
    (horder : ∃ m n : ℕ, Nat.card B ∣ 2 ^ m * 3 ^ n)
    (h₁ : B ≤ normalizer (firstFactor K e : Set A))
    (h₂ : B ≤ normalizer (secondFactor K e : Set A)) : B ≤ K := by
  obtain ⟨m, n, horder⟩ := horder
  let C := centralizer (K : Set A)
  let q : A →* A ⧸ K := QuotientGroup.mk' K
  let f := q.comp B.subtype
  have hle : f.range ≤ C.map q := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨k, hk, c, hc, he⟩ := normalizing_pair_decomposition K e b (h₁ b.property) (h₂ b.property)
    refine ⟨c, hc, ?_⟩
    change q c = q b
    rw [he, map_mul, show q k = 1 from (QuotientGroup.eq_one_iff k).mpr hk, one_mul]
  have hnot : ¬ 3 ∣ Nat.card f.range := by
    intro hd
    exact three_not_dvd_card_centralizer K e hrank
      (hd.trans ((card_dvd_of_le hle).trans (card_map_dvd C q)))
  have hcop : (Nat.card f.range).Coprime (3 ^ n) :=
    ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr hnot).symm.pow_right n
  have hp : IsPGroup 2 f.range := IsPGroup.of_card_dvd_pow
    (hcop.dvd_of_dvd_mul_right ((card_range_dvd f).trans horder))
  have he := hB.hom_eq_one_of_isPGroup hp f.rangeRestrict
  intro b hb
  apply (QuotientGroup.eq_one_iff b).mp
  exact congrArg Subtype.val (DFunLike.congr_fun he (⟨b, hb⟩ : B))

private theorem sign_cube : ∀ x : S3, Equiv.Perm.sign x = 1 → x ^ 3 = 1 := by
  decide +kernel

omit [Finite A] [K.Normal] in
/-- Inside a symmetric-three pair, a two-perfect subgroup has exponent three. -/
theorem cube_eq_one_of_le_pair (e : K ≃* (S3 × S3)) (B : Subgroup A)
    (hB : IsPPerfect 2 B) (hBK : B ≤ K) (b : B) : b ^ 3 = 1 := by
  let f : B →* S3 × S3 := e.toMonoidHom.comp (inclusion hBK)
  have hf : Function.Injective f := e.injective.comp (inclusion_injective hBK)
  have hu : IsPGroup 2 ℤˣ := IsPGroup.of_card (n := 1) (by
    simp [Nat.card_eq_fintype_card, Fintype.card_units_int])
  have h₁ := hB.hom_eq_one_of_isPGroup hu
    (Equiv.Perm.sign.comp ((MonoidHom.fst S3 S3).comp f))
  have h₂ := hB.hom_eq_one_of_isPGroup hu
    (Equiv.Perm.sign.comp ((MonoidHom.snd S3 S3).comp f))
  apply hf
  rw [map_pow, map_one]
  apply Prod.ext
  · exact sign_cube (f b).1 (DFunLike.congr_fun h₁ b)
  · exact sign_cube (f b).2 (DFunLike.congr_fun h₂ b)

/-- Rank-two placement and the resulting three-group assertion, with no
centralizer or inner-action assumptions. -/
theorem le_pair_and_isThreeGroup (e : K ≃* (S3 × S3)) (B : Subgroup A)
    (hB : IsPPerfect 2 B) (hrank : primeRank 3 A ≤ 2)
    (horder : ∃ m n : ℕ, Nat.card B ∣ 2 ^ m * 3 ^ n)
    (h₁ : B ≤ normalizer (firstFactor K e : Set A))
    (h₂ : B ≤ normalizer (secondFactor K e : Set A)) :
    B ≤ K ∧ IsPGroup 3 B := by
  have hBK := le_pair K e B hB hrank horder h₁ h₂
  exact ⟨hBK, fun b => ⟨1, by simpa using cube_eq_one_of_le_pair K e B hB hBK b⟩⟩

end Theory.GroupTheory.NormalSymmetricThreePairRank
