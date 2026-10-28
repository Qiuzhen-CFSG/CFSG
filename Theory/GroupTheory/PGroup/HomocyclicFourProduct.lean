module

public import Theory.GroupTheory.PGroup.Homocyclic
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Products of homocyclic groups of exponent four

Two commuting copies of (C₄)ⁿ with their common involutions identified
have a product of order 2^(3n) and two-rank 2n. The order follows from the
intersection formula. Every involution in a homocyclic factor is a square,
so the product's square image is exactly the common subgroup. Counting
the square kernel gives its elementary abelian subgroup of order 2^(2n),
which contains every involution and therefore computes the exact two-rank.

Source: GLS, volume 4, Chapter 2, construction after Lemma 13.4.
-/

open Subgroup
open scoped Pointwise

namespace Subgroup

/-- In (C₄)ⁿ, the squares are exactly the elements whose square is one. -/
public theorem square_iff_square_one_of_homocyclic_four
    {H : Type*} [Group H] {n : ℕ}
    (e : H ≃* StandardHomocyclicCover (Fin n) 4) (x : H) :
    (∃ y : H, y ^ 2 = x) ↔ x ^ 2 = 1 := by
  have coord : ∀ a : ZMod 4, (∃ b : ZMod 4, 2 • b = a) ↔ 2 • a = 0 := by decide
  constructor
  · rintro ⟨y, rfl⟩
    apply e.injective
    rw [map_pow, map_pow, map_one]
    apply Multiplicative.toAdd.injective
    funext i
    exact (coord _).mp ⟨Multiplicative.toAdd (e y) i, rfl⟩
  · intro hx
    have hx' : (e x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
    have hcoord : ∀ i : Fin n, ∃ b : ZMod 4, 2 • b = Multiplicative.toAdd (e x) i := by
      intro i
      apply (coord _).mpr
      exact congrFun (congrArg Multiplicative.toAdd hx') i
    choose y hy using hcoord
    refine ⟨e.symm (Multiplicative.ofAdd y), ?_⟩
    apply e.injective
    rw [map_pow, e.apply_symm_apply]
    exact Multiplicative.toAdd.injective (funext hy)

/-- The order of a homocyclic group of rank n and exponent four. -/
public theorem homocyclic_four_card
    {H : Type*} [Group H] {n : ℕ}
    (e : H ≃* StandardHomocyclicCover (Fin n) 4) : Nat.card H = 2 ^ (2 * n) := by
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Multiplicative (Fin n → ZMod 4)) = _
  simp [Nat.card_eq_fintype_card, pow_mul]

/-- The exact two-rank and order of the commuting product along common involutions. -/
public theorem rank_card_sup_homocyclic_four
    {G : Type*} [Group G] [Finite G] (S U A : Subgroup G) {n : ℕ}
    (eS : S ≃* StandardHomocyclicCover (Fin n) 4)
    (eU : U ≃* StandardHomocyclicCover (Fin n) 4)
    (hc : S ≤ centralizer (U : Set G)) (hi : S ⊓ U = A)
    (hAc : Nat.card A = 2 ^ n)
    (hSA : ∀ x : S, (x : G) ∈ A ↔ x ^ 2 = 1)
    (hUA : ∀ x : U, (x : G) ∈ A ↔ x ^ 2 = 1) :
    IsPGroup 2 (S ⊔ U : Subgroup G) ∧ IsMulCommutative (S ⊔ U : Subgroup G) ∧
      primeRank 2 (S ⊔ U : Subgroup G) = 2 * n ∧
      Nat.card (S ⊔ U : Subgroup G) = (2 ^ n) ^ 3 := by
  let : IsMulCommutative S := ⟨⟨fun x y => eS.injective (by simp only [map_mul, mul_comm])⟩⟩
  let : IsMulCommutative U := ⟨⟨fun x y => eU.injective (by simp only [map_mul, mul_comm])⟩⟩
  have hSc := homocyclic_four_card eS
  have hUc := homocyclic_four_card eU
  have hUS : U ≤ centralizer (S : Set G) := le_centralizer_iff.mp hc
  have hn : U ≤ normalizer (S : Set G) := hUS.trans (centralizer_le_normalizer _)
  let R := S ⊔ U
  have hRp : IsPGroup 2 R :=
    (IsPGroup.of_card hSc).to_sup_of_normal_left' (IsPGroup.of_card hUc) hn
  have hRc : IsMulCommutative R := by
    apply le_centralizer_iff_isMulCommutative.mp
    apply sup_le
    · apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff_isMulCommutative.mpr inferInstance) hUS
    · apply le_centralizer_iff.mpr
      exact sup_le hc (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  let : IsMulCommutative R := hRc
  let : CommGroup R := IsMulCommutative.instCommGroup
  have hcard : Nat.card R = 2 ^ (3 * n) := by
    have he := card_mul_eq_card_inf_mul_card_sup_of_normalizes S U hn
    rw [hi, hAc, hSc, hUc] at he
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) n)
    calc
      2 ^ n * Nat.card R = 2 ^ (2 * n) * 2 ^ (2 * n) := he.symm
      _ = 2 ^ n * 2 ^ (3 * n) := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hAR : A ≤ R := hi ▸ (inf_le_left.trans le_sup_left : S ⊓ U ≤ S ⊔ U)
  let square : R →* R := powMonoidHom 2
  have hsquare : square.range = A.subgroupOf R := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      have hy : (y : G) ∈ (S : Set G) * (U : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left S U hn]
        exact y.property
      obtain ⟨s, hs, v, hv, he⟩ := hy
      change (y : G) ^ 2 ∈ A
      rw [← he, (show Commute s v from (hc hs v hv).symm).mul_pow]
      apply A.mul_mem
      · apply (hSA (⟨s ^ 2, S.pow_mem hs 2⟩ : S)).mpr
        exact (square_iff_square_one_of_homocyclic_four eS _).mp ⟨⟨s, hs⟩, rfl⟩
      · apply (hUA (⟨v ^ 2, U.pow_mem hv 2⟩ : U)).mpr
        exact (square_iff_square_one_of_homocyclic_four eU _).mp ⟨⟨v, hv⟩, rfl⟩
    · intro x hx
      have hxS : (x : G) ∈ S := (hi ▸ inf_le_left : A ≤ S) hx
      obtain ⟨y, hy⟩ := (square_iff_square_one_of_homocyclic_four eS
        (⟨x, hxS⟩ : S)).mpr ((hSA _).mp hx)
      refine ⟨⟨y, mem_sup_left y.property⟩, ?_⟩
      apply Subtype.ext
      change (y : G) ^ 2 = (x : G)
      exact congrArg (fun a : S => (a : G)) hy
  have hrange : Nat.card square.range = 2 ^ n := by
    rw [hsquare, Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv, hAc]
  have hker : Nat.card square.ker = 2 ^ (2 * n) := by
    have he := square.ker.card_mul_index
    rw [index_eq_card, Nat.card_congr (QuotientGroup.quotientKerEquivRange square).toEquiv,
      hrange, hcard] at he
    apply Nat.eq_of_mul_eq_mul_right (pow_pos (by decide : 0 < 2) n)
    calc
      Nat.card square.ker * 2 ^ n = 2 ^ (3 * n) := he
      _ = 2 ^ (2 * n) * 2 ^ n := by rw [← pow_add]; congr 1; omega
  let : IsElementaryAbelian 2 square.ker :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
        Subtype.ext x.property) }
  have hrank : primeRank 2 R = 2 * n := by
    apply le_antisymm
    · apply primeRank_le_of_pow_eq_one_subset square.ker hker.le
      exact fun x hx => hx
    · exact IsElementaryAbelian.primeRank_ge_of_card square.ker hker
  exact ⟨hRp, hRc, hrank, by simpa [pow_mul, Nat.mul_comm] using hcard⟩

end Subgroup
