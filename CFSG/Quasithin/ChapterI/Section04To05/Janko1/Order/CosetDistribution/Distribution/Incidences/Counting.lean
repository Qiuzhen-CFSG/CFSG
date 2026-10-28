module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Commuting
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Double counting Bender's literal inversion incidences

The pairs counted here consist of an outside involution and an element of a
specified order in the actual Sylow normalizer. The geometry identifies each
inverted set with a cyclic subgroup; its generators give the weights in the
fiber sum. A second bijection counts elements from the subgroup census.

Inside involutions cannot invert elements whose order does not divide four:
the inversion equation puts the square in the elementary Sylow subgroup.
Consequently the supplied three-inverter count gives the three/six incidence.
The already proved commuting count gives the two/six incidence, without
assuming that fibers of size two are absent.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, printed pp.226–227, following (4.3).
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

/-- The actual involutions outside the subgroup used for the right cosets. -/
@[expose] public def BenderOutsideInvolutions (H : Subgroup G) :=
  {u : G // orderOf u = 2 ∧ u ∉ H}

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

private theorem subgroup_order_elements_card (S : Subgroup G) [IsCyclic S] (n : ℕ)
    (hS : Nat.card S = n) :
    Nat.card {x : S // orderOf (x : G) = n} = Nat.totient n := by
  have he : {x : S // orderOf (x : G) = n} ≃ {x : S // orderOf x = n} :=
    Equiv.subtypeEquivRight (fun x => by rw [orderOf_coe])
  rw [Nat.card_congr he, cyclic_order_card, hS, if_pos (dvd_refl n)]

/-- Counting generators in the literal subgroups of a fixed order. -/
public theorem bender_order_elements_card (H : Subgroup G) (n : ℕ)
    (hcyc : ∀ S : Subgroup G, S ≤ H → Nat.card S = n → IsCyclic S) :
    Nat.card {x : H // orderOf (x : G) = n} =
      Nat.card (BenderSubgroupsOfOrder H n) * Nat.totient n := by
  classical
  let E := {x : H // orderOf (x : G) = n}
  let S := BenderSubgroupsOfOrder H n
  let F := fun A : S => {x : G // x ∈ A.1 ∧ orderOf x = n}
  let e : (Σ A : S, F A) ≃ E :=
    { toFun := fun a => ⟨⟨a.2.1, a.1.2.1 a.2.2.1⟩, a.2.2.2⟩
      invFun := fun x => ⟨⟨zpowers (x.1 : G), zpowers_le.mpr x.1.2,
        (Nat.card_zpowers _).trans x.2⟩, ⟨x.1, mem_zpowers _, x.2⟩⟩
      left_inv := by
        rintro ⟨⟨A, hAH, hAn⟩, ⟨x, hxA, hxn⟩⟩
        have he : zpowers x = A :=
          eq_of_le_of_card_ge (zpowers_le.mpr hxA) (by rw [Nat.card_zpowers, hxn, hAn])
        exact Sigma.subtype_ext (Subtype.ext he) rfl
      right_inv := by intro x; rfl }
  have : Finite S := by unfold S BenderSubgroupsOfOrder; infer_instance
  let : Fintype S := Fintype.ofFinite _
  have hc (A : S) : Nat.card (F A) = Nat.totient n := by
    let : IsCyclic A.1 := hcyc A.1 A.2.1 A.2.2
    let ea : F A ≃ {x : A.1 // orderOf (x : G) = n} :=
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        invFun := fun x => ⟨x.1, x.1.2, x.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    exact (Nat.card_congr ea).trans (subgroup_order_elements_card A.1 n A.2.2)
  rw [← Nat.card_congr e, Nat.card_sigma]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  rfl

private theorem inverted_order_card (h : Janko1CentralizerData G)
    (geometry : BenderNormalizerGeometry h)
    (u : BenderOutsideInvolutions (normalizer (h.sylow : Set G))) (n : ℕ) :
    Nat.card {x : normalizer (h.sylow : Set G) // orderOf (x : G) = n ∧
      u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹} =
    if n ∣ Nat.card (BenderFiber (normalizer (h.sylow : Set G))
      (benderRightCoset (normalizer (h.sylow : Set G)) u.1)) then Nat.totient n else 0 := by
  let H := normalizer (h.sylow : Set G)
  obtain ⟨K, hK, hc⟩ := geometry.inverted_subgroup u.1 u.2.1 u.2.2
  have hKH : K ≤ H := fun x hx => ((hK x).mp hx).1
  have hcyc : IsCyclic K := by
    rcases hc with hc | hc | hc | hc | hc
    · have : Subsingleton K := (Nat.card_eq_one_iff_unique.mp hc).1
      infer_instance
    · exact isCyclic_of_prime_card (p := 2) hc
    · exact isCyclic_of_prime_card (p := 3) hc
    · exact geometry.six_cyclic K hKH hc
    · let : Fact (Nat.Prime 7) := ⟨by decide⟩
      exact isCyclic_of_prime_card (p := 7) hc
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
public theorem bender_inversion_incidence_identity (h : Janko1CentralizerData G)
    (geometry : BenderNormalizerGeometry h) (n k : ℕ)
    (hlocal : ∀ x : normalizer (h.sylow : Set G), orderOf (x : G) = n →
      Nat.card {u : BenderOutsideInvolutions (normalizer (h.sylow : Set G)) //
        u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹} = k) :
    let H := normalizer (h.sylow : Set G)
    let c := fun m => if n ∣ m then Nat.totient n else 0
    Nat.card {x : H // orderOf (x : G) = n} * k =
      c 1 * Nat.card (BenderInvolutionsInFibers H 1) +
      c 2 * Nat.card (BenderInvolutionsInFibers H 2) +
      c 3 * Nat.card (BenderInvolutionsInFibers H 3) +
      c 6 * Nat.card (BenderInvolutionsInFibers H 6) +
      c 7 * Nat.card (BenderInvolutionsInFibers H 7) := by
  classical
  dsimp only
  let H := normalizer (h.sylow : Set G)
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
    inverted_order_card h geometry u n
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
      (if f u = 3 then c 3 else 0) + (if f u = 6 then c 6 else 0) +
      (if f u = 7 then c 7 else 0) := by
    obtain ⟨K, hK, hc⟩ := geometry.inverted_subgroup u.1 u.2.1 u.2.2
    have he := bender_fiber_card_of_inverted_subgroup H u.1 u.2.1 u.2.2 K hK
    change f u = Nat.card K at he
    rcases hc with hc | hc | hc | hc | hc <;> rw [← he] at hc <;> simp [hc]
  calc
    _ = ∑ u : U, c (f u) := by simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card] using ht
    _ = _ := by
      simp_rw [hf, Finset.sum_add_distrib, hsum]
      rfl



/-- An involution in the Sylow normalizer can only invert elements of order dividing four. -/
public theorem bender_inverter_not_mem_normalizer (h : Janko1CentralizerData G)
    (x t : G) (hxH : x ∈ normalizer (h.sylow : Set G))
    (ht : orderOf t = 2) (hinv : t * x * t⁻¹ = x⁻¹)
    (hx4 : ¬ orderOf x ∣ 4) : t ∉ normalizer (h.sylow : Set G) := by
  intro htH
  have htQ := h.normalizer_involution_mem_sylow t ht htH
  have hconj : x * t⁻¹ * x⁻¹ ∈ (h.sylow : Subgroup G) :=
    (mem_normalizer_iff.mp hxH t⁻¹).mp ((h.sylow : Subgroup G).inv_mem htQ)
  have hv : x⁻¹ * x⁻¹ ∈ (h.sylow : Subgroup G) := by
    have hv := (h.sylow : Subgroup G).mul_mem htQ hconj
    have he : t * (x * t⁻¹ * x⁻¹) = x⁻¹ * x⁻¹ := by
      calc
        _ = (t * x * t⁻¹) * x⁻¹ := by group
        _ = _ := by rw [hinv]
    exact he ▸ hv
  have hv2 := congrArg Subtype.val (h.sylow_square ⟨_, hv⟩)
  change (x⁻¹ * x⁻¹) ^ 2 = 1 at hv2
  have hxpow : x ^ 4 = 1 := by
    have hxi : (x⁻¹) ^ 4 = 1 := by
      calc
        _ = (x⁻¹ * x⁻¹) ^ 2 := by group
        _ = 1 := hv2
    simpa only [inv_pow, inv_eq_one] using hxi
  exact hx4 (orderOf_dvd_of_pow_eq_one hxpow)

/-- For orders not dividing four, every ambient inverting involution is outside the normalizer. -/
public theorem bender_outside_inverting_card (h : Janko1CentralizerData G)
    (x : normalizer (h.sylow : Set G)) (hx4 : ¬ orderOf (x : G) ∣ 4) :
    Nat.card {u : BenderOutsideInvolutions (normalizer (h.sylow : Set G)) //
      u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹} =
      Nat.card {u : G // orderOf u = 2 ∧ u * (x : G) * u⁻¹ = (x : G)⁻¹} := by
  let e : {u : BenderOutsideInvolutions (normalizer (h.sylow : Set G)) //
      u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹} ≃
      {u : G // orderOf u = 2 ∧ u * (x : G) * u⁻¹ = (x : G)⁻¹} :=
    { toFun := fun u => ⟨u.1.1, u.1.2.1, u.2⟩
      invFun := fun u => ⟨⟨u.1, u.2.1,
        h.bender_inverter_not_mem_normalizer x u.1 x.2 u.2.1 u.2.2 hx4⟩, u.2.2⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  exact Nat.card_congr e

/-- The 28 three-subgroups and the ambient prime-data count give the three/six incidence. -/
public theorem bender_three_inversion_incidence (h : Janko1CentralizerData G) (d : ℕ)
    (localData : BenderPrimeData G d) (geometry : BenderNormalizerGeometry h) :
    Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 3) +
      Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 6) = 168 * d := by
  have he := bender_inversion_incidence_identity h geometry 3 (6 * d) (by
    intro x hx
    rw [bender_outside_inverting_card h x (by rw [hx]; decide)]
    exact localData.inverting_three x hx)
  have hcard := bender_order_elements_card (normalizer (h.sylow : Set G)) 3
    (fun _ _ hs => isCyclic_of_prime_card (p := 3) hs)
  rw [geometry.three_subgroups] at hcard
  norm_num [show Nat.totient 3 = 2 by decide] at he hcard
  rw [hcard] at he
  omega

/-- The seven inside involutions and their 24 outside commuting partners give the two/six incidence. -/
public theorem bender_two_inversion_incidence [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (geometry : BenderNormalizerGeometry h) :
    Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 2) +
      Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 6) = 168 := by
  let H := normalizer (h.sylow : Set G)
  have hlocal (x : H) (hx : orderOf (x : G) = 2) :
      Nat.card {u : BenderOutsideInvolutions H //
        u.1 * (x : G) * u.1⁻¹ = (x : G)⁻¹} = 24 := by
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
    exact (Nat.card_congr e).trans (h.bender_outside_commuting_involutions_card x hx x.2)
  have he := bender_inversion_incidence_identity h geometry 2 24 hlocal
  have hcard : Nat.card {x : H // orderOf (x : G) = 2} = 7 := by
    let e : {x : H // orderOf (x : G) = 2} ≃ BenderFiber H (benderBaseCoset H) :=
      { toFun := fun x => ⟨x.1, x.2, (benderRightCoset_eq_base_iff H _).mpr x.1.2⟩
        invFun := fun x => ⟨⟨x.1, (benderRightCoset_eq_base_iff H _).mp x.2.2⟩, x.2.1⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    exact (Nat.card_congr e).trans h.bender_base_fiber_card
  norm_num [show Nat.totient 2 = 1 by decide] at he
  have hc : Nat.card {x : H // orderOf x = 2} = 7 := by
    simpa only [orderOf_coe] using hcard
  change Nat.card {x : H // orderOf x = 2} * 24 = _ at he
  rw [hc] at he
  exact he.symm

end CFSG.Quasithin.Janko1CentralizerData
