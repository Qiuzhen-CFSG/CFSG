module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24.Orders
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24.Cubic
public import Theory.Mathieu.M23.Properties.NoOrderTen
public import Theory.Mathieu.M23.Properties.PointStabilizer
public import Theory.GroupTheory.PrimeOrderSylowArithmetic

/-!
# Odd abelian orders and the fifteen obstruction in M₂₃

The literal point-stabilizer embedding in M₂₄ transfers the odd abelian
order bounds. Its fixed point excludes the cubic class forced by an element
of order 21. For a proposed Cartan product of order 1920, the centralizer of
its Sylow five-subgroup has order 15: an involution centralizing it would
contradict the native involution-centralizer order. Its automizer divides
four, and none of the resulting Sylow counts is one modulo five.

Source: Aschbacher--Smith, Definition E.3.37 and Proposition 7.3.4,
printed pp.239 and 699.
-/

public section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M23Cartan
open Subgroup Sporadic.Mathieu
open scoped IsMulCommutative
noncomputable def embedding : M23 →* M24 :=
  (MulAction.stabilizer M24 (24 : Fin 24)).subtype.comp m23EquivM24PointStabilizer.toMonoidHom

theorem embedding_injective : Function.Injective embedding :=
  Subtype.val_injective.comp m23EquivM24PointStabilizer.injective

theorem embedding_fixed (g : M23) : (embedding g).val (24 : Fin 24) = 24 :=
  (m23EquivM24PointStabilizer g).property

private theorem no_twentyone (g : M23) : orderOf g ≠ 21 := by
  intro hg
  let H := (zpowers g).map embedding
  have hH : Nat.card H = 21 := by rw [card_map_of_injective embedding_injective, Nat.card_zpowers, hg]
  let x : H := ⟨embedding g, mem_map_of_mem _ (mem_zpowers g)⟩
  have hx : orderOf x = 21 := (orderOf_coe x).symm.trans
    ((orderOf_injective embedding embedding_injective g).trans hg)
  have hc := M24Cartan.cubic_fixed_card_zero H (by rw [hH]; decide) x hx (x ^ 7)
    (by rw [orderOf_pow, hx]; decide)
  have hfix : (24 : Fin 24) ∈ ((x ^ 7).val.val).supportᶜ := by
    rw [Finset.mem_compl, Equiv.Perm.mem_support]
    change ¬ (embedding g ^ 7).val (24 : Fin 24) ≠ 24
    rw [← map_pow]
    exact not_not.mpr (embedding_fixed _)
  exact (Finset.card_pos.mpr ⟨_,hfix⟩).ne' hc

private theorem order_twentyone {G : Type*} [Group G] [Finite G] [IsMulCommutative G]
    (hcard : Nat.card G = 21) : ∃ g : G, orderOf g = 21 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hcard]; decide)
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := G) 7 (by rw [hcard]; decide)
  refine ⟨x*y, ?_⟩
  rw [(Commute.all x y).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx,hy]; decide), hx, hy]

theorem abelian_seven_card (B : Subgroup M23) [IsMulCommutative B]
    (ho : Odd (Nat.card B)) (h7 : 7 ∣ Nat.card B) : Nat.card B = 7 := by
  have he : Nat.card (B.map embedding) = Nat.card B := card_map_of_injective embedding_injective
  rcases M24Cartan.abelian_seven_card (B.map embedding) (he ▸ ho) (he ▸ h7) with h | h
  · exact he ▸ h
  · obtain ⟨g,hg⟩ := order_twentyone (he ▸ h)
    exact (no_twentyone g.val ((orderOf_coe g).trans hg)).elim

theorem abelian_five_card (B : Subgroup M23) [IsMulCommutative B]
    (ho : Odd (Nat.card B)) (h5 : 5 ∣ Nat.card B) : Nat.card B = 5 ∨ Nat.card B = 15 := by
  have he : Nat.card (B.map embedding) = Nat.card B := card_map_of_injective embedding_injective
  simpa only [he] using M24Cartan.abelian_five_card (B.map embedding) (he ▸ ho) (he ▸ h5)

/-- The Sylow congruence excludes the product order required by a cyclic fifteen. -/
theorem no_fifteen_overgroup (H : Subgroup M23) (hH : Nat.card H = 1920)
    (g : H) (hg : orderOf g = 15) : False := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : Nat.card (zpowers (g ^ 3)) = 5 := by rw [Nat.card_zpowers, orderOf_pow, hg]; decide
  let P : Sylow 5 H := Sylow.ofCard (zpowers (g ^ 3)) (by rw [hp,hH]; decide +kernel)
  have hP : Nat.card P = 5 := hp
  let C := centralizer (P : Set H)
  have hCodd : ¬ 2 ∣ Nat.card C := by
    apply P.not_two_dvd_centralizer_card hP
    intro t ht hd
    have hle : (centralizer ({t} : Set H)).map H.subtype ≤
        centralizer ({t.val} : Set M23) := by
      rintro a ⟨a,ha,rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))
    have hc := card_dvd_of_le hle
    rw [card_map_of_injective H.subtype_injective] at hc
    exact m23_involution_centralizer_not_five t.val ((orderOf_coe t).trans ht) (hd.trans hc)
  have h15 : 15 ∣ Nat.card C := by
    have hle : zpowers g ≤ C := by
      apply zpowers_le.mpr
      change g ∈ centralizer (zpowers (g ^ 3) : Set H)
      rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
      exact ((Commute.refl g).pow_left 3).eq
    simpa only [Nat.card_zpowers, hg] using card_dvd_of_le hle
  have hC : Nat.card C = 15 := by
    have hd : Nat.card C ∣ 1920 := hH ▸ C.card_subgroup_dvd_card
    have hn : Nat.card C ∈ Nat.divisors 1920 := Nat.mem_divisors.mpr ⟨hd,by decide⟩
    have hcheck : ∀ n ∈ Nat.divisors 1920, ¬ 2 ∣ n → 15 ∣ n → n = 15 := by decide +kernel
    exact hcheck _ hn hCodd h15
  have hm := P.centralizer_relIndex_normalizer_dvd_prime_sub_one hP
  let m := C.relIndex (normalizer (P : Set H))
  have hmle : m ≤ 4 := Nat.le_of_dvd (by decide) hm
  have hN : Nat.card (normalizer (P : Set H)) = 15 * m := by
    have he := (C.subgroupOf (normalizer (P : Set H))).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (P : Set H))).toEquiv,
      hC] at he
    exact he.symm
  have hc := (normalizer (P : Set H)).card_mul_index
  rw [hN, ← P.card_eq_index_normalizer, hH] at hc
  have hmod := card_sylow_modEq_one 5 H
  change Nat.card (Sylow 5 H) % 5 = 1 % 5 at hmod
  interval_cases m <;> omega
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M23Cartan
