module
public import Theory.GroupTheory.OrderNineAutomorphisms
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# Perfect subgroups centralizing a normal elementary nine

The automorphism group of a normal group of order nine is solvable, so every
perfect subgroup centralizes it. Under three-rank at most two, adjoining any
further cubic would produce an elementary twenty-seven. Hence every cubic in
a perfect subgroup is central there. When its center has order at most three,
cyclic Sylow transfer excludes three from the whole perfect subgroup.

Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033. The actual
quotient application is in Chapter14's OddNormalizer closure development.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Perfect subgroups act trivially on a normal group of order nine. -/
theorem normal_nine_perfect_centralizes
    (E : Subgroup G) [E.Normal] (hE : Nat.card E = 9)
    (B : Subgroup G) [Group.IsPerfect B] : B ≤ centralizer (E : Set G) := by
  let : Group.IsSolvable (MulAut E) := MulAut.isSolvable_of_card_nine hE
  let f : B →* MulAut E := (MulAut.conjNormal : G →* MulAut E).comp B.subtype
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hz : f.range = ⊥ := by
    by_contra hn
    let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have hf : f = 1 := MonoidHom.range_eq_bot_iff.mp hz
  intro b hb e he
  have hh := congrArg (fun g : B →* MulAut E => ((g ⟨b,hb⟩ ⟨e,he⟩ : E) : G)) hf
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Saturation of three-rank forces every cubic in a perfect subgroup into its center. -/
theorem normal_elementary_nine_perfect_cubic_central
    (E : Subgroup G) [E.Normal] [IsElementaryAbelian 3 E] (hE : Nat.card E = 9)
    (hr : primeRank 3 G ≤ 2) (B : Subgroup G) [Group.IsPerfect B]
    (x : B) (hx : x ^ 3 = 1) : x ∈ center B := by
  have hBE := normal_nine_perfect_centralizes E hE B
  have hxE : (x : G) ∈ E := by
    by_cases h1 : x = 1
    · simp [h1]
    by_contra hn
    have ho : orderOf (x : G) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime hx h1
    have hfix : E ≤ centralizer ({(x : G)} : Set G) := by
      intro e he
      exact mem_centralizer_singleton_iff.mpr (hBE x.property e he)
    have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join E (x : G) ho hn hfix
      (by simpa using hE : Nat.card E = 3 ^ 2)
    omega
  exact mem_center_iff.mpr fun b => Subtype.ext (hBE b.property x hxE).symm

/-- Cyclic Sylow transfer excludes a central cubic in the small-center case. -/
theorem perfect_three_free_of_cubic_central_of_small_center
    [Group.IsPerfect G] (hc : Nat.card (center G) ≤ 3)
    (hcentral : ∀ x : G, x ^ 3 = 1 → x ∈ center G) :
    ¬ 3 ∣ Nat.card G := by
  have hr : primeRank 3 G ≤ 1 :=
    primeRank_le_of_pow_eq_one_subset (center G) (by simpa using hc) hcentral
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  let C := zpowers x
  have hC : IsPGroup 3 C := IsPGroup.of_card (n := 1)
    (by simp only [C, Nat.card_zpowers,hx,pow_one])
  obtain ⟨P,hCP⟩ := hC.exists_le_sylow
  have hcentralC : C ≤ center G := zpowers_le.mpr
    (hcentral x (hx ▸ pow_orderOf_eq_one x))
  have hz := PerfectCentralCovering.central_subgroup_eq_bot_of_isCyclic_sylow P
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr) (C.subgroupOf P)
    (by simpa only [map_subgroupOf_eq_of_le hCP] using hcentralC)
  have hh : (⟨x,hCP (mem_zpowers x)⟩ : P) ∈ C.subgroupOf P := mem_zpowers x
  rw [hz,mem_bot] at hh
  have hx1 : x = 1 := congrArg Subtype.val hh
  simp [hx1] at hx
end Theory.GroupTheory
