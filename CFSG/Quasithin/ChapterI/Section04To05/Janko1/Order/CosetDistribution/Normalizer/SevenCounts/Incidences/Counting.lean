module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Incidences.Counting

/-!
# Inversion incidences in the seven-centralizer normalizer

The actual incidence pairs consist of an external involution and an element
of prescribed order in `H = N_G(C_G(S))`. Counting by elements uses the local
inverter counts; counting by involutions uses the generators in their literal
cyclic inversion subgroups. Their orders divide six by the supplied geometry.

Source: H. Bender, *Finite groups with large subgroups* (1974), proof of (4.3),
printed p.226. The argument is the four-size version of the later normalizer
incidence identity, with no assumption on that normalizer's distribution.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

private theorem cyclic_order_card {K : Type*} [Group K] [Finite K] [IsCyclic K] (n : ℕ) :
    Nat.card {x : K // orderOf x = n} = if n ∣ Nat.card K then Nat.totient n else 0 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  by_cases hd : n ∣ Nat.card K
  · rw [if_pos hd, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_orderOf_eq_totient (by rwa [← Nat.card_eq_fintype_card])
  · rw [if_neg hd]
    apply Nat.card_eq_zero.mpr
    exact Or.inl ⟨fun x => hd (x.2 ▸ orderOf_dvd_natCard x.1)⟩

private theorem inverted_order_card {S : Subgroup G}
    (geometry : BenderSevenGeometry S)
    (u : BenderOutsideInvolutions (normalizer (centralizer (S : Set G) : Set G))) (n : ℕ) :
    Nat.card {x : normalizer (centralizer (S : Set G) : Set G) // orderOf (x : G) = n ∧
      u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹} =
    if n ∣ Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G))
      (benderRightCoset (normalizer (centralizer (S : Set G) : Set G)) u.1)) then Nat.totient n else 0 := by
  let H := normalizer (centralizer (S : Set G) : Set G)
  obtain ⟨K, hK, hcyc, _⟩ := geometry.inverted_subgroup u.1 u.2.1 u.2.2
  let : IsCyclic K := hcyc
  have hKH : K ≤ H := fun x hx => ((hK x).mp hx).1
  let e : {x : H // orderOf (x : G) = n ∧ u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹} ≃
      {x : K // orderOf x = n} :=
    { toFun := fun x => ⟨⟨x.1, (hK _).mpr ⟨x.1.2, x.2.2⟩⟩,
        (orderOf_coe _).symm.trans x.2.1⟩
      invFun := fun x => ⟨⟨x.1, hKH x.1.2⟩, (orderOf_coe x.1).trans x.2,
        ((hK _).mp x.1.2).2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [Nat.card_congr e, cyclic_order_card,
    bender_fiber_card_of_inverted_subgroup H u.1 u.2.1 u.2.2 K hK]

omit [Finite G] in
private theorem outside_fiber_count (H : Subgroup G) (n : ℕ) :
    Nat.card {u : BenderOutsideInvolutions H //
      Nat.card (BenderFiber H (benderRightCoset H u.1)) = n} =
      Nat.card (BenderInvolutionsInFibers H n) := by
  let e : {u : BenderOutsideInvolutions H //
      Nat.card (BenderFiber H (benderRightCoset H u.1)) = n} ≃
      BenderInvolutionsInFibers H n :=
    { toFun := fun u => ⟨u.1.1, u.1.2.1,
        fun he => u.1.2.2 ((benderRightCoset_eq_base_iff H _).mp he), u.2⟩
      invFun := fun u => ⟨⟨u.1, u.2.1,
        fun hm => u.2.2.1 ((benderRightCoset_eq_base_iff H _).mpr hm)⟩, u.2.2.2⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  exact Nat.card_congr e

/-- Double counting inverted elements by order and by their actual inversion fibers. -/
public theorem bender_seven_inversion_incidence_identity {S : Subgroup G}
    (geometry : BenderSevenGeometry S) (n k : ℕ)
    (hlocal : ∀ x : normalizer (centralizer (S : Set G) : Set G), orderOf (x : G) = n →
      Nat.card {u : BenderOutsideInvolutions (normalizer (centralizer (S : Set G) : Set G)) //
        u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹} = k) :
    let H := normalizer (centralizer (S : Set G) : Set G)
    let c := fun m => if n ∣ m then Nat.totient n else 0
    Nat.card {x : H // orderOf (x : G) = n} * k =
      c 1 * Nat.card (BenderInvolutionsInFibers H 1) +
      c 2 * Nat.card (BenderInvolutionsInFibers H 2) +
      c 3 * Nat.card (BenderInvolutionsInFibers H 3) +
      c 6 * Nat.card (BenderInvolutionsInFibers H 6) := by
  classical
  dsimp only
  let H := normalizer (centralizer (S : Set G) : Set G)
  let E := {x : H // orderOf (x : G) = n}
  let U := BenderOutsideInvolutions H
  let f := fun u : U => Nat.card (BenderFiber H (benderRightCoset H u.1))
  let c := fun m => if n ∣ m then Nat.totient n else 0
  let : Fintype E := Fintype.ofFinite _
  have : Finite U := by unfold U BenderOutsideInvolutions; infer_instance
  let : Fintype U := Fintype.ofFinite _
  let e : (Σ x : E, {u : U // u.1 * (x.1 : G) * u.1⁻¹ = (x.1 : G)⁻¹}) ≃
      (Σ u : U, {x : H // orderOf (x : G) = n ∧ u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹}) :=
    { toFun := fun a => ⟨a.2.1, ⟨a.1.1, a.1.2, a.2.2⟩⟩
      invFun := fun a => ⟨⟨a.2.1, a.2.2.1⟩, ⟨a.1, a.2.2.2⟩⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl }
  have ht := Nat.card_congr e
  rw [Nat.card_sigma, Nat.card_sigma] at ht
  have hl (x : E) : Nat.card {u : U // u.1 * (x.1 : G) * u.1⁻¹ = (x.1 : G)⁻¹} = k :=
    hlocal x.1 x.2
  have hr (u : U) : Nat.card {x : H // orderOf (x : G) = n ∧
      u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹} = c (f u) :=
    inverted_order_card geometry u n
  simp only [hl, hr] at ht
  have hsum (m : ℕ) : (∑ u : U, if f u = m then c m else 0) =
      c m * Nat.card (BenderInvolutionsInFibers H m) := by
    have hs : (∑ u : U, if f u = m then 1 else 0) =
        Nat.card (BenderInvolutionsInFibers H m) := by
      rw [Finset.sum_boole, ← outside_fiber_count]
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl
    rw [← hs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp
  have hf (u : U) : c (f u) =
      (if f u = 1 then c 1 else 0) + (if f u = 2 then c 2 else 0) +
      (if f u = 3 then c 3 else 0) + (if f u = 6 then c 6 else 0) := by
    obtain ⟨K, hK, _, hdiv⟩ := geometry.inverted_subgroup u.1 u.2.1 u.2.2
    have hc := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
    have hd : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide
    rw [hd] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    have he := bender_fiber_card_of_inverted_subgroup H u.1 u.2.1 u.2.2 K hK
    change f u = Nat.card K at he
    rcases hc with hc | hc | hc | hc <;> rw [← he] at hc <;> simp [hc]
  calc
    _ = ∑ u : U, c (f u) := by simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card] using ht
    _ = _ := by
      simp_rw [hf, Finset.sum_add_distrib, hsum]
      rfl




namespace BenderSevenStructure
variable [IsSimpleGroup G] {h : Janko1CentralizerData G} {d : ℕ}
    (localData : BenderPrimeData G d) {S : Subgroup G} (hS : Nat.card S = 7)
    (structureData : BenderSevenStructure h S)

include h localData hS structureData

/-- The product of two internal involutions lies in the odd kernel. -/
public theorem involutions_mul_mem_kernel (u v : G) (hu : orderOf u = 2)
    (hv : orderOf v = 2)
    (huH : u ∈ normalizer (centralizer (S : Set G) : Set G))
    (hvH : v ∈ normalizer (centralizer (S : Set G) : Set G)) :
    u * v ∈ centralizer (S : Set G) := by
  obtain ⟨a, ha, rfl⟩ := structureData.involution_factorization localData hS u hu huH
  obtain ⟨b, hb, rfl⟩ := structureData.involution_factorization localData hS v hv hvH
  have ht2 : structureData.t * structureData.t = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp structureData.involution).1
  have hti : structureData.t⁻¹ = structureData.t := inv_eq_of_mul_eq_one_right ht2
  have hinv := (h.seven_centralizer_inverted localData S hS structureData.t
    structureData.involution structureData.normalizes).1 b hb
  rw [hti] at hinv
  have he : a * structureData.t * (b * structureData.t) = a * b⁻¹ := by
    rw [mul_assoc, ← mul_assoc structureData.t b, hinv]
  rw [he]
  exact mul_mem ha (inv_mem hb)

/-- Internal involutions cannot invert elements of order three or six. -/
public theorem inverter_not_mem (x u : G)
    (hxH : x ∈ normalizer (centralizer (S : Set G) : Set G))
    (hx : orderOf x = 3 ∨ orderOf x = 6)
    (hu : orderOf u = 2) (hinv : u * x * u⁻¹ = x⁻¹) :
    u ∉ normalizer (centralizer (S : Set G) : Set G) := by
  intro huH
  let H := normalizer (centralizer (S : Set G) : Set G)
  let e := MulAut.conj x
  have heH : e u ∈ H := H.mul_mem (H.mul_mem hxH huH) (H.inv_mem hxH)
  have hprod := structureData.involutions_mul_mem_kernel localData hS
    u (e u) hu ((e.orderOf_eq u).trans hu) huH heH
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hu).1)
  have he : u * e u = (x ^ 2)⁻¹ := by
    change u * (x * u * x⁻¹) = (x ^ 2)⁻¹
    rw [hui] at hinv
    calc
      u * (x * u * x⁻¹) = (u * x * u) * x⁻¹ := by group
      _ = (x ^ 2)⁻¹ := by rw [hinv]; group
  rw [he] at hprod
  have hxA : x ^ 2 ∈ centralizer (S : Set G) := by simpa only [inv_inv] using inv_mem hprod
  have ho : orderOf (⟨x ^ 2, hxA⟩ : centralizer (S : Set G)) = 3 := by
    have ho : orderOf (x ^ 2) = 3 := by
      rw [orderOf_pow]
      rcases hx with hx | hx <;> rw [hx] <;> decide
    exact (orderOf_injective _ (centralizer (S : Set G)).subtype_injective _).symm.trans ho
  exact (h.seven_centralizer_small_primes localData S hS).2.1
    (ho ▸ orderOf_dvd_natCard (⟨x ^ 2, hxA⟩ : centralizer (S : Set G)))

/-- All inverters of elements of order three or six are outside H. -/
public theorem outside_inverting_card
    (x : normalizer (centralizer (S : Set G) : Set G))
    (hx : orderOf (x : G) = 3 ∨ orderOf (x : G) = 6) :
    Nat.card {u : BenderOutsideInvolutions (normalizer (centralizer (S : Set G) : Set G)) //
      u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹} =
      Nat.card {u : G // orderOf u = 2 ∧ u * (x : G) * u⁻¹ = (x : G)⁻¹} := by
  let e : {u : BenderOutsideInvolutions (normalizer (centralizer (S : Set G) : Set G)) //
      u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹} ≃
      {u : G // orderOf u = 2 ∧ u * (x : G) * u⁻¹ = (x : G)⁻¹} :=
    { toFun := fun u => ⟨u.1.1, u.1.2.1, u.2⟩
      invFun := fun u => ⟨⟨u.1, u.2.1,
        structureData.inverter_not_mem localData hS x u.1 x.2 hx u.2.1 u.2.2⟩, u.2.2⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  exact Nat.card_congr e

end BenderSevenStructure

/-- The a internal involutions each have thirty external commuting partners. -/
public theorem bender_seven_two_incidence [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)
    {S : Subgroup G} (hS : Nat.card S = 7)
    (structureData : BenderSevenStructure h S) (geometry : BenderSevenGeometry S) :
    Nat.card (BenderInvolutionsInFibers (normalizer (centralizer (S : Set G) : Set G)) 2) +
      Nat.card (BenderInvolutionsInFibers (normalizer (centralizer (S : Set G) : Set G)) 6) =
        30 * Nat.card (centralizer (S : Set G)) := by
  let H := normalizer (centralizer (S : Set G) : Set G)
  have hlocal (x : H) (hx : orderOf (x : G) = 2) :
      Nat.card {u : BenderOutsideInvolutions H //
        u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹} = 30 := by
    have hxinv : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hx).1)
    let e : {u : BenderOutsideInvolutions H //
        u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹} ≃
        {u : G // orderOf u = 2 ∧ Commute u (x : G) ∧ u ∉ H} :=
      { toFun := fun u => ⟨u.1.1, u.1.2.1,
          mul_inv_eq_iff_eq_mul.mp (u.2.trans hxinv), u.1.2.2⟩
        invFun := fun u => ⟨⟨u.1, u.2.1, u.2.2.2⟩,
          (mul_inv_eq_iff_eq_mul.mpr u.2.2.1.eq).trans hxinv.symm⟩
        left_inv := by intro u; rfl
        right_inv := by intro u; rfl }
    exact (Nat.card_congr e).trans
      (structureData.outside_commuting_involutions_card localData hS x hx x.2)
  have he := bender_seven_inversion_incidence_identity geometry 2 30 hlocal
  have hcard : Nat.card {x : H // orderOf (x : G) = 2} =
      Nat.card (centralizer (S : Set G)) := by
    let e : {x : H // orderOf (x : G) = 2} ≃ BenderFiber H (benderBaseCoset H) :=
      { toFun := fun x => ⟨x.1, x.2, (benderRightCoset_eq_base_iff H _).mpr x.1.2⟩
        invFun := fun x => ⟨⟨x.1, (benderRightCoset_eq_base_iff H _).mp x.2.2⟩, x.2.1⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    exact (Nat.card_congr e).trans (structureData.base_fiber localData hS)
  norm_num [show Nat.totient 2 = 1 by decide] at he
  have hc : Nat.card {x : H // orderOf x = 2} = Nat.card (centralizer (S : Set G)) := by
    simpa only [orderOf_coe] using hcard
  change Nat.card {x : H // orderOf x = 2} * 30 = _ at he
  rw [hc] at he
  simpa only [Nat.mul_comm] using he.symm

/-- Counting the generators of the a three-subgroups gives the three/six incidence. -/
public theorem bender_seven_three_incidence [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)
    {S : Subgroup G} (hS : Nat.card S = 7)
    (structureData : BenderSevenStructure h S) (geometry : BenderSevenGeometry S) :
    Nat.card (BenderInvolutionsInFibers (normalizer (centralizer (S : Set G) : Set G)) 3) +
      Nat.card (BenderInvolutionsInFibers (normalizer (centralizer (S : Set G) : Set G)) 6) =
        6 * d * Nat.card (centralizer (S : Set G)) := by
  have he := bender_seven_inversion_incidence_identity geometry 3 (6 * d) (by
    intro x hx
    rw [structureData.outside_inverting_card localData hS x (Or.inl hx)]
    exact localData.inverting_three x hx)
  have hc := bender_order_elements_card (normalizer (centralizer (S : Set G) : Set G)) 3
    (fun _ _ hs => isCyclic_of_prime_card (p := 3) hs)
  rw [geometry.three_subgroups] at hc
  norm_num [show Nat.totient 3 = 2 by decide] at he hc
  rw [hc] at he
  nlinarith

/-- The ambient six-inverter count gives the literal sextuple incidence. -/
public theorem bender_seven_six_incidence_of_local_count [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)
    {S : Subgroup G} (hS : Nat.card S = 7)
    (structureData : BenderSevenStructure h S) (geometry : BenderSevenGeometry S)
    (hsix : ∀ x : G, orderOf x = 6 →
      Nat.card {u : G // orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹} = 6) :
    Nat.card (BenderInvolutionsInFibers (normalizer (centralizer (S : Set G) : Set G)) 6) =
      6 * Nat.card (centralizer (S : Set G)) := by
  have he := bender_seven_inversion_incidence_identity geometry 6 6 (by
    intro x hx
    rw [structureData.outside_inverting_card localData hS x (Or.inr hx)]
    exact hsix x hx)
  have hc := bender_order_elements_card (normalizer (centralizer (S : Set G) : Set G)) 6
    geometry.six_cyclic
  rw [geometry.six_subgroups] at hc
  norm_num [show Nat.totient 6 = 2 by decide] at he hc
  rw [hc] at he
  omega

end CFSG.Quasithin.Janko1CentralizerData
