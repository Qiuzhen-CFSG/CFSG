module

public import Theory.GroupTheory.Commutator.CentralElementaryFourQuotient
public import Theory.GroupTheory.CentralBinaryCentralizerCard
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Join
public import Theory.ElementaryAbelian.Quotient

/-!
# Pairing two elementary abelian subgroups of order eight

Two mutually normalizing elementary abelian two-subgroups of order eight
have commutator subgroup of order at most two and equal centralizer indices.
Only the two subgroups must be finite; the ambient group is arbitrary.

Work inside their finite join, where both are normal. Their intersection
contains the commutator subgroup and centralizes the join. Its order is
one, two, four or eight. The first two cases give the bound directly, the
last forces the subgroups to coincide, and the order-four case gives a
central elementary-four quotient. For a nontrivial commutator subgroup,
the actual commutator pairing takes values in a group of order two.
Binary pairing duality equates the two centralizer orders, and hence their
indices. Finally transport the results out of the finite join.

These intrinsic group-theoretic facts supply the binary natural-module
specialization of Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs
of rank two* (1993), (3.5), pp.869–870, and the local commutator bound used
in (3.9), p.879. The geometric applications and their hypotheses are
separate from the results here.
-/

open scoped Pointwise IsMulCommutative commutatorElement
namespace Subgroup

private theorem finite_bound {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) [A.Normal] [B.Normal]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : Nat.card A = 8) (hB : Nat.card B = 8) (hgen : A ⊔ B = ⊤) :
    Nat.card (⁅A, B⁆ : Subgroup G) ≤ 2 := by
  let I := A ⊓ B
  have hDI : ⁅A, B⁆ ≤ I := le_inf (commutator_le_left A B) (commutator_le_right A B)
  have hd : Nat.card I ∣ 8 := hA ▸ card_dvd_of_le (show I ≤ A from inf_le_left)
  have hc : Nat.card I = 1 ∨ Nat.card I = 2 ∨ Nat.card I = 4 ∨ Nat.card I = 8 := by
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card I ∣ 2 ^ 3 from hd)
    interval_cases k <;> simp_all
  rcases hc with hc | hc | hc | hc
  · exact (card_le_of_le hDI).trans (by omega)
  · exact (card_le_of_le hDI).trans (by omega)
  · have hIcenter : I ≤ center G := by
      have hh : A ⊔ B ≤ centralizer (I : Set G) :=
        sup_le ((le_centralizer A).trans (centralizer_le inf_le_left))
          ((le_centralizer B).trans (centralizer_le inf_le_right))
      rw [hgen] at hh
      simpa only [coe_top, centralizer_univ] using le_centralizer_iff.mp hh
    let π := QuotientGroup.mk' I
    have hmap : A.map π ⊔ B.map π = ⊤ := by
      rw [← map_sup, hgen, map_top_of_surjective _ (QuotientGroup.mk'_surjective I)]
    let : IsElementaryAbelian 2 (A.map π) := IsElementaryAbelian.map π
    let : IsElementaryAbelian 2 (B.map π) := IsElementaryAbelian.map π
    have hcomm : A.map π ≤ centralizer (B.map π : Set (G ⧸ I)) := by
      rw [← commutator_eq_bot_iff_le_centralizer, ← map_commutator]
      apply le_bot_iff.mp
      rw [map_le_iff_le_comap, MonoidHom.comap_bot, QuotientGroup.ker_mk']
      exact hDI
    let : IsElementaryAbelian 2 ↥(A.map π ⊔ B.map π) :=
      IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hcomm)
    let : IsElementaryAbelian 2 (⊤ : Subgroup (G ⧸ I)) := hmap ▸ inferInstance
    let : IsElementaryAbelian 2 (G ⧸ I) :=
      IsElementaryAbelian.of_surjective
        (topEquiv : (⊤ : Subgroup (G ⧸ I)) ≃* (G ⧸ I)).toMonoidHom topEquiv.surjective
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B le_normalizer_of_normal
    have hquot := I.card_eq_card_quotient_mul_card_subgroup
    rw [hA, hB, hgen, card_top] at hprod
    change 8 * 8 = Nat.card I * Nat.card G at hprod
    have hq : Nat.card (G ⧸ I) = 4 := by rw [hc] at hprod hquot; omega
    have hb := card_commutator_le_two_of_central_elementary_four_quotient I hIcenter hq
    exact (card_le_of_le (commutator_mono le_top le_top)).trans hb
  · have hIA : I = A := eq_of_le_of_card_ge inf_le_left (by omega)
    have hIB : I = B := eq_of_le_of_card_ge inf_le_right (by omega)
    have hAB : A = B := hIA.symm.trans hIB
    rw [← hAB, commutator_self_eq_bot_iff.mpr inferInstance, card_bot]
    decide

private theorem finite_reciprocity {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) [A.Normal] [B.Normal]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : Nat.card A = 8) (hB : Nat.card B = 8)
    (hbound : Nat.card (⁅A, B⁆ : Subgroup G) ≤ 2) :
    (centralizer (B : Set G)).relIndex A = (centralizer (A : Set G)).relIndex B := by
  by_cases hbot : ⁅A, B⁆ = ⊥
  · have hAB := commutator_eq_bot_iff_le_centralizer.mp hbot
    rw [relIndex_eq_one.mpr hAB, relIndex_eq_one.mpr (le_centralizer_iff.mp hAB)]
  · let D := ⁅A, B⁆
    have hD : Nat.card D = 2 := by
      have := (one_lt_card_iff_ne_bot ⁅A, B⁆).mpr hbot
      change 1 < Nat.card D at this
      change Nat.card D ≤ 2 at hbound
      omega
    have hDA : D ≤ A := commutator_le_left A B
    have hDB : D ≤ B := commutator_le_right A B
    let : IsMulCommutative D := le_centralizer_iff_isMulCommutative.mp
      (hDA.trans ((le_centralizer A).trans (centralizer_le hDA)))
    have hZB : ⁅D, B⁆ ≤ ⊥ := by
      rw [le_bot_iff, commutator_eq_bot_iff_le_centralizer]
      exact hDB.trans (le_centralizer B)
    have hc := card_mul_card_centralizer_restrict_of_central_binary_pairing
      A B D hDA le_rfl hZB hD
    rw [hA, hB] at hc
    have hleft := ((centralizer (B : Set G)).subgroupOf A).index_mul_card
    have hright := ((centralizer (A : Set G)).subgroupOf B).index_mul_card
    rw [hA] at hleft
    rw [hB] at hright
    have hpos : 0 < Nat.card ((centralizer (B : Set G)).subgroupOf A) := Nat.card_pos
    change ((centralizer (B : Set G)).subgroupOf A).index =
      ((centralizer (A : Set G)).subgroupOf B).index
    have heq : Nat.card ((centralizer (A : Set G)).subgroupOf B) =
        Nat.card ((centralizer (B : Set G)).subgroupOf A) := by omega
    rw [heq] at hright
    nlinarith

private theorem finite_join {G : Type*} [Group G] (A B : Subgroup G)
    [Finite A] [Finite B] (hn : B ≤ normalizer (A : Set G)) : Finite ↥(A ⊔ B) := by
  let m : A × B → ↥(A ⊔ B) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), mul_mem_sup p.1.property p.2.property⟩
  apply Finite.of_surjective m
  intro x
  have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hn]
    exact x.property
  obtain ⟨a, ha, b, hb, he⟩ := hx
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext he⟩

private theorem centralizer_restrict {G : Type*} [Group G]
    (A S : Subgroup G) (hAS : A ≤ S) :
    centralizer (A.subgroupOf S : Set S) = (centralizer (A : Set G)).subgroupOf S := by
  ext x
  constructor
  · intro hx a ha
    exact congrArg Subtype.val (hx ⟨a, hAS ha⟩ ha)
  · intro hx a ha
    exact Subtype.ext (hx a ha)

private theorem elementary_eight_pair {G : Type*} [Group G]
    (A B : Subgroup G) [Finite A] [Finite B]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : Nat.card A = 8) (hB : Nat.card B = 8)
    (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G)) :
    Nat.card (⁅A, B⁆ : Subgroup G) ≤ 2 ∧
      (centralizer (B : Set G)).relIndex A = (centralizer (A : Set G)).relIndex B := by
  let S := A ⊔ B
  let A₀ := A.subgroupOf S
  let B₀ := B.subgroupOf S
  let : Finite S := finite_join A B hBA
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hBA)
  let : B₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le hAB B.le_normalizer)
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf le_sup_left
  let : IsElementaryAbelian 2 B₀ := IsElementaryAbelian.subgroupOf le_sup_right
  have hA₀ : Nat.card A₀ = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show A ≤ S from le_sup_left)).toEquiv).trans hA
  have hB₀ : Nat.card B₀ = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show B ≤ S from le_sup_right)).toEquiv).trans hB
  have hgen : A₀ ⊔ B₀ = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self _
  have hbound := finite_bound A₀ B₀ hA₀ hB₀ hgen
  have hrecip := finite_reciprocity A₀ B₀ hA₀ hB₀ hbound
  have hmap : (⁅A₀, B₀⁆ : Subgroup S).map S.subtype = ⁅A, B⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right]
  constructor
  · rw [← hmap, card_map_of_injective S.subtype_injective]
    exact hbound
  · change (centralizer (B.subgroupOf S : Set S)).relIndex (A.subgroupOf S) =
      (centralizer (A.subgroupOf S : Set S)).relIndex (B.subgroupOf S) at hrecip
    rwa [centralizer_restrict B S le_sup_right, centralizer_restrict A S le_sup_left,
      relIndex_subgroupOf le_sup_left, relIndex_subgroupOf le_sup_right] at hrecip

/-- Two mutually normalizing elementary abelian subgroups of order eight have
commutator subgroup of order at most two. The ambient group need not be finite. -/
public theorem card_commutator_le_two_of_elementary_eight
    {G : Type*} [Group G] (A B : Subgroup G) [Finite A] [Finite B]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : Nat.card A = 8) (hB : Nat.card B = 8)
    (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G)) :
    Nat.card (⁅A, B⁆ : Subgroup G) ≤ 2 :=
  (elementary_eight_pair A B hA hB hAB hBA).1

/-- The two centralizer indices of mutually normalizing elementary abelian
subgroups of order eight are equal, even in an infinite ambient group. -/
public theorem centralizer_relIndex_eq_of_elementary_eight
    {G : Type*} [Group G] (A B : Subgroup G) [Finite A] [Finite B]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : Nat.card A = 8) (hB : Nat.card B = 8)
    (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G)) :
    (centralizer (B : Set G)).relIndex A = (centralizer (A : Set G)).relIndex B :=
  (elementary_eight_pair A B hA hB hAB hBA).2

/-- In the noncommuting case the commutator subgroup has order exactly two. -/
public theorem card_commutator_eq_two_of_elementary_eight
    {G : Type*} [Group G] (A B : Subgroup G) [Finite A] [Finite B]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : Nat.card A = 8) (hB : Nat.card B = 8)
    (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G))
    (hne : ⁅A, B⁆ ≠ ⊥) : Nat.card (⁅A, B⁆ : Subgroup G) = 2 := by
  have hDA : ⁅A, B⁆ ≤ A := le_normalizer_iff_commutator_le_left.mp hBA
  let : Finite (⁅A, B⁆ : Subgroup G) :=
    Finite.of_injective (inclusion hDA) (inclusion_injective hDA)
  have hlow := (one_lt_card_iff_ne_bot ⁅A, B⁆).mpr hne
  have hupp := card_commutator_le_two_of_elementary_eight A B hA hB hAB hBA
  omega

end Subgroup
