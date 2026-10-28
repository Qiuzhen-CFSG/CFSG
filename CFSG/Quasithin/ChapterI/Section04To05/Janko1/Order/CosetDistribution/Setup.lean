module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CountingData

/-!
# Actual coset fibers in Bender's J₁ calculation

The map `x ↦ x⁻¹H` converts Bender's right cosets `Hx` into Mathlib's
left-coset quotient. Its involution fibers partition the actual ambient
involutions. For fibers of sizes zero, one, three, six, or seven, summing
the fibers gives both the occupied-coset bound and the involution count.

Every involution in the Sylow normalizer belongs to its normal Sylow
two-subgroup. Thus its base fiber has cardinality seven, independently
of the still-needed normalizer order and non-base distribution.

The two records at the end specify the remaining group-theoretic steps.
Neither is asserted to exist here. They are consumed by the conditional
assembly in `Order.CosetDistribution`.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §2 and §4, pp.223 and 225–227.
-/

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko1CentralizerData

/-- Bender’s right coset, represented in the left-coset quotient by inversion. -/
@[expose] public noncomputable def benderRightCoset {G : Type*} [Group G]
    (H : Subgroup G) (x : G) : G ⧸ H := QuotientGroup.mk x⁻¹

/-- The base coset represented by the identity. -/
@[expose] public noncomputable def benderBaseCoset {G : Type*} [Group G]
    (H : Subgroup G) : G ⧸ H := QuotientGroup.mk (1 : G)

/-- The actual involutions in one right coset of `H`. -/
@[expose] public def BenderFiber {G : Type*} [Group G] (H : Subgroup G) (ω : G ⧸ H) :=
  {x : G // orderOf x = 2 ∧ benderRightCoset H x = ω}

/-- The number `bₙ` of non-base right cosets containing exactly `n` involutions. -/
@[expose] public noncomputable def benderCosetCount {G : Type*} [Group G]
    (H : Subgroup G) (n : ℕ) : ℕ :=
  Nat.card {ω : G ⧸ H // ω ≠ benderBaseCoset H ∧ Nat.card (BenderFiber H ω) = n}

/-- Equality in the chosen quotient is membership in Bender’s right coset. -/
public theorem benderRightCoset_eq_iff {G : Type*} [Group G] (H : Subgroup G) (x y : G) :
    benderRightCoset H x = benderRightCoset H y ↔ x ∈ (H : Set G) * ({y} : Set G) := by
  rw [benderRightCoset, benderRightCoset, QuotientGroup.eq]
  simp only [inv_inv]
  constructor
  · intro hx
    exact Set.mem_mul.mpr ⟨x * y⁻¹, hx, y, by simp, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    have hb' : b = y := hb
    simpa [hb'] using ha

/-- The base fiber tests membership in the actual subgroup. -/
public theorem benderRightCoset_eq_base_iff {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    benderRightCoset H x = benderBaseCoset H ↔ x ∈ H := by
  simp [benderRightCoset, benderBaseCoset, QuotientGroup.eq]

/-- Occupied cosets fit in the quotient, and their involution fibers partition `J`. -/
public theorem bender_fiber_sums {G : Type*} [Group G] [Finite G]
    (H : Subgroup G)
    (hsizes : ∀ ω : G ⧸ H, ω ≠ benderBaseCoset H →
      Nat.card (BenderFiber H ω) = 0 ∨ Nat.card (BenderFiber H ω) = 1 ∨
      Nat.card (BenderFiber H ω) = 3 ∨ Nat.card (BenderFiber H ω) = 6 ∨
      Nat.card (BenderFiber H ω) = 7) :
    1 + benderCosetCount H 1 + benderCosetCount H 3 +
        benderCosetCount H 6 + benderCosetCount H 7 ≤ H.index ∧
      Nat.card {x : G // orderOf x = 2} = Nat.card (BenderFiber H (benderBaseCoset H)) +
        benderCosetCount H 1 + 3 * benderCosetCount H 3 +
        6 * benderCosetCount H 6 + 7 * benderCosetCount H 7 := by
  classical
  let Ω := G ⧸ H
  let : Fintype Ω := Fintype.ofFinite _
  let N := {ω : Ω // ω ≠ benderBaseCoset H}
  let : Fintype N := Fintype.ofFinite _
  have : ∀ ω : Ω, Finite (BenderFiber H ω) := fun ω => by
    unfold BenderFiber
    infer_instance
  let f : Ω → ℕ := fun ω => Nat.card (BenderFiber H ω)
  have hsum (n : ℕ) : (∑ ω : N, if f ω = n then 1 else 0) = benderCosetCount H n := by
    rw [Finset.sum_boole]
    have he := Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun ω : Ω => ω ≠ benderBaseCoset H) (fun ω => f ω = n))
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at he
    exact he
  have hweighted (n : ℕ) : (∑ ω : N, if f ω = n then n else 0) =
      n * benderCosetCount H n := by
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp
  have hcardN : 1 + Nat.card N = H.index := by
    rw [H.index_eq_card]
    let e : Ω ≃ Option N :=
      { toFun := fun ω => if hω : ω = benderBaseCoset H then none else some ⟨ω, hω⟩
        invFun := fun o => o.elim (benderBaseCoset H) Subtype.val
        left_inv := by intro ω; by_cases hω : ω = benderBaseCoset H <;> simp [hω]
        right_inv := by
          intro o
          cases o with
          | none => simp
          | some ω => simp [dif_neg ω.property] }
    rw [Nat.card_congr e, Finite.card_option, Nat.add_comm]
  have hoccupied : benderCosetCount H 1 + benderCosetCount H 3 +
      benderCosetCount H 6 + benderCosetCount H 7 ≤ Nat.card N := by
    rw [← hsum 1, ← hsum 3, ← hsum 6, ← hsum 7,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ _ω : N, 1 := by
        apply Finset.sum_le_sum
        intro ω _
        split_ifs <;> omega
      _ = Nat.card N := by simp
  have htotal : Nat.card {x : G // orderOf x = 2} =
      f (benderBaseCoset H) + ∑ ω : N, f ω := by
    let e : {x : G // orderOf x = 2} ≃ Σ ω : Ω, BenderFiber H ω :=
      { toFun := fun x => ⟨benderRightCoset H x, ⟨x, x.property, rfl⟩⟩
        invFun := fun y => ⟨y.2.1, y.2.2.1⟩
        left_inv := by intro x; rfl
        right_inv := by rintro ⟨ω, x, hx, rfl⟩; rfl }
    rw [Nat.card_congr e, Nat.card_sigma]
    change (∑ ω : Ω, f ω) = _
    have hs := Finset.sum_subtype (F := inferInstance)
      (Finset.univ.erase (benderBaseCoset H))
      (by intro ω; simp : ∀ ω : Ω,
        ω ∈ Finset.univ.erase (benderBaseCoset H) ↔ ω ≠ benderBaseCoset H) f
    have he := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (benderBaseCoset H))
    rw [← he, hs, Nat.add_comm]
  have hparts : (∑ ω : N, f ω) = benderCosetCount H 1 +
      3 * benderCosetCount H 3 + 6 * benderCosetCount H 6 + 7 * benderCosetCount H 7 := by
    have hf (ω : N) : f ω =
        (if f ω = 1 then 1 else 0) + (if f ω = 3 then 3 else 0) +
        (if f ω = 6 then 6 else 0) + (if f ω = 7 then 7 else 0) := by
      rcases hsizes ω ω.property with ht | ht | ht | ht | ht <;>
        change f ω = _ at ht <;> simp [ht]
    calc
      _ = ∑ ω : N, ((if f ω = 1 then 1 else 0) + (if f ω = 3 then 3 else 0) +
          (if f ω = 6 then 6 else 0) + (if f ω = 7 then 7 else 0)) := by
        exact Finset.sum_congr rfl (fun ω _ => hf ω)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
        rw [hsum, hweighted, hweighted, hweighted]
  exact ⟨by omega, by
    rw [hparts] at htotal
    simpa only [f, Nat.add_assoc] using htotal⟩



/-- Every involution of the Sylow normalizer lies in its normal Sylow subgroup. -/
public theorem normalizer_involution_mem_sylow {G : Type*} [Group G] [Finite G]
    (h : Janko1CentralizerData G) (x : G) (hx : orderOf x = 2)
    (hxN : x ∈ normalizer (h.sylow : Set G)) : x ∈ (h.sylow : Subgroup G) := by
  let H := normalizer (h.sylow : Set G)
  let P := h.sylow.subtype (show (h.sylow : Subgroup G) ≤ H from le_normalizer)
  have : (P : Subgroup H).Normal := normal_in_normalizer
  let : Unique (Sylow 2 H) := P.unique_of_normal inferInstance
  let xH : H := ⟨x, hxN⟩
  have hxH : orderOf xH = 2 := (orderOf_injective H.subtype H.subtype_injective xH).symm.trans hx
  have hp : IsPGroup 2 (zpowers xH) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxH, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hm := hQ (mem_zpowers xH)
  rw [Subsingleton.elim Q P] at hm
  exact hm

/-- The base right coset contains exactly the seven nonidentity Sylow elements. -/
public theorem bender_base_fiber_card {G : Type*} [Group G] [Finite G]
    (h : Janko1CentralizerData G) :
    Nat.card (BenderFiber (normalizer (h.sylow : Set G))
      (benderBaseCoset (normalizer (h.sylow : Set G)))) = 7 := by
  let H := normalizer (h.sylow : Set G)
  let e : BenderFiber H (benderBaseCoset H) ≃ {x : h.sylow // x ≠ 1} :=
    { toFun := fun x => ⟨⟨x.1, h.normalizer_involution_mem_sylow x.1 x.2.1
        ((benderRightCoset_eq_base_iff H x.1).mp x.2.2)⟩, by
          intro he
          have hx := x.2.1
          rw [show x.1 = 1 from congrArg Subtype.val he, orderOf_one] at hx
          omega⟩
      invFun := fun x => ⟨x.1.1, by
        have hx2 : (x.1 : G) ^ 2 = 1 := congrArg Subtype.val (h.sylow_square x.1)
        have hx1 : (x.1 : G) ≠ 1 := fun he => x.2 (Subtype.ext he)
        exact orderOf_eq_prime_iff.mpr ⟨hx2, hx1⟩,
        (benderRightCoset_eq_base_iff H _).mpr (le_normalizer x.1.property)⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  classical
  let : Fintype h.sylow := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (h.sylow : Subgroup G) - 1 = 7
  rw [h.sylow_card]

/-- The two normalizer conclusions used in Bender's §4 distribution.
The second clause is the exact assertion (4.3), including its even-order premise. -/
public structure BenderNormalizerData {G : Type*} [Group G] [Finite G]
    (h : Janko1CentralizerData G) : Prop where
  normalizer_card : Nat.card (normalizer (h.sylow : Set G)) = 168
  seven_centralizer : ∀ S : Subgroup G, S ≤ normalizer (h.sylow : Set G) →
    Nat.card S = 7 → Even (Nat.card (normalizer (S : Set G))) →
      centralizer (S : Set G) = S

/-- Bender's `c`: involutions alone in a non-base right coset whose
centralizer in the actual subgroup `H` is nontrivial. -/
@[expose] public def BenderCentralizedSingletons {G : Type*} [Group G] (H : Subgroup G) :=
  {x : G // orderOf x = 2 ∧ benderRightCoset H x ≠ benderBaseCoset H ∧
    Nat.card (BenderFiber H (benderRightCoset H x)) = 1 ∧
    ∃ a ∈ H, a ≠ 1 ∧ Commute a x}

/-- The literal coset distribution on pp.226–227, before the index inequality
or the fixed-point congruence. Existence is a separate group-theoretic obligation.
In particular, `e_add_one_le_d` prevents truncation of the source subtraction. -/
public structure BenderDistributionData {G : Type*} [Group G] [Finite G]
    (h : Janko1CentralizerData G) (d : ℕ) where
  e : ℕ
  m : ℕ
  e_le_one : e ≤ 1
  e_add_one_le_d : e + 1 ≤ d
  fiber_sizes : ∀ ω : G ⧸ normalizer (h.sylow : Set G),
    ω ≠ benderBaseCoset (normalizer (h.sylow : Set G)) →
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 0 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 1 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 3 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 6 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 7
  centralized_singletons :
    Nat.card (BenderCentralizedSingletons (normalizer (h.sylow : Set G))) =
      56 * (d - 1 - e)
  single_cosets : benderCosetCount (normalizer (h.sylow : Set G)) 1 =
    Nat.card (BenderCentralizedSingletons (normalizer (h.sylow : Set G))) + 168 * m
  triple_cosets : benderCosetCount (normalizer (h.sylow : Set G)) 3 = 56 * (d - 1)
  sextuple_cosets : benderCosetCount (normalizer (h.sylow : Set G)) 6 = 28
  septuple_cosets : benderCosetCount (normalizer (h.sylow : Set G)) 7 = 8 * e

end CFSG.Quasithin.Janko1CentralizerData
