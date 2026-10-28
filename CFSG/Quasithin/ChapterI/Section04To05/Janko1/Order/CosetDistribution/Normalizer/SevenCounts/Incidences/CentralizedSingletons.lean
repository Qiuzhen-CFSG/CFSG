module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.Incidences.Centralizers

/-!
# The literal centralized-singleton incidence

Count pairs consisting of a three-element of H and an external commuting
involution. Each three-element has 2d-2 such involutions, all in singleton
fibers. Conversely a centralized singleton has centralizer of order three
in H, so it occurs with exactly two three-elements. This proves the source
count c = 2(d-1)a without assuming singleton counts or uniqueness.

Source: Bender, *Finite groups with large subgroups* (1974), proof of (4.3),
printed p.226.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

private theorem singleton_three_elements_card
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)
    {S : Subgroup G} (hS : Nat.card S = 7) (structureData : BenderSevenStructure h S)
    (u : BenderCentralizedSingletons (normalizer (centralizer (S : Set G) : Set G))) :
    Nat.card {x : normalizer (centralizer (S : Set G) : Set G) //
      orderOf (x : G) = 3 ∧ Commute u.1 (x : G)} = 2 := by
  classical
  let H := normalizer (centralizer (S : Set G) : Set G)
  let C := H ⊓ centralizer ({u.1} : Set G)
  have hc : Nat.card C = 3 := structureData.singleton_centralizer_card localData hS u
  let : IsCyclic C := isCyclic_of_prime_card (p := 3) hc
  let : Fintype C := Fintype.ofFinite _
  have hcount : Nat.card {x : C // orderOf x = 3} = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hh := IsCyclic.card_orderOf_eq_totient (α := C) (d := 3)
      (by rw [← Nat.card_eq_fintype_card, hc])
    exact hh.trans (by decide)
  let e : {x : H // orderOf (x : G) = 3 ∧ Commute u.1 (x : G)} ≃
      {x : C // orderOf x = 3} := {
    toFun := fun x => ⟨⟨x.1, x.1.2, mem_centralizer_singleton_iff.mpr x.2.2.symm.eq⟩,
      (orderOf_injective _ C.subtype_injective _).symm.trans x.2.1⟩
    invFun := fun x => ⟨⟨x.1, x.1.2.1⟩,
      (orderOf_injective _ C.subtype_injective _).trans x.2,
      (mem_centralizer_singleton_iff.mp x.1.2.2).symm⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  exact (Nat.card_congr e).trans hcount

/-- The actual commuting-three incidences count the centralized singleton fibers. -/
public theorem bender_seven_centralized_singleton_incidence
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)
    {S : Subgroup G} (hS : Nat.card S = 7)
    (structureData : BenderSevenStructure h S) (geometry : BenderSevenGeometry S) :
    Nat.card (BenderCentralizedSingletons (normalizer (centralizer (S : Set G) : Set G))) =
      2 * (d - 1) * Nat.card (centralizer (S : Set G)) := by
  classical
  let H := normalizer (centralizer (S : Set G) : Set G)
  let E := {x : H // orderOf (x : G) = 3}
  let U := BenderOutsideInvolutions H
  let J := BenderCentralizedSingletons H
  let F := fun u : J => {x : H // orderOf (x : G) = 3 ∧ Commute u.1 (x : G)}
  let : Fintype E := Fintype.ofFinite _
  have : Finite J := by unfold J BenderCentralizedSingletons; infer_instance
  let : Fintype J := Fintype.ofFinite _
  have : Finite U := by unfold U BenderOutsideInvolutions; infer_instance
  let e : (Σ x : E, {u : U // Commute u.1 (x.1 : G)}) ≃ (Σ u : J, F u) := {
    toFun := fun p =>
      ⟨⟨p.2.1.1, p.2.1.2.1,
        fun he => p.2.1.2.2 ((benderRightCoset_eq_base_iff H _).mp he),
        bender_seven_commuting_three_singleton h geometry p.1.1 p.2.1.1 p.1.1.2
          p.1.2 p.2.1.2.1 p.2.1.2.2 p.2.2,
        ⟨p.1.1, p.1.1.2, (orderOf_eq_prime_iff.mp p.1.2).2, p.2.2.symm⟩⟩,
        ⟨p.1.1, p.1.2, p.2.2⟩⟩
    invFun := fun p => ⟨⟨p.2.1, p.2.2.1⟩,
      ⟨⟨p.1.1, p.1.2.1, fun he => p.1.2.2.1 ((benderRightCoset_eq_base_iff H _).mpr he)⟩,
        p.2.2.2⟩⟩
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl }
  have hc := Nat.card_congr e
  rw [Nat.card_sigma, Nat.card_sigma] at hc
  have hl (x : E) : Nat.card {u : U // Commute u.1 (x.1 : G)} = 2 * (d - 1) := by
    let eu : {u : U // Commute u.1 (x.1 : G)} ≃
        {u : G // orderOf u = 2 ∧ Commute u (x.1 : G) ∧ u ∉ H} := {
      toFun := fun u => ⟨u.1.1, u.1.2.1, u.2, u.1.2.2⟩
      invFun := fun u => ⟨⟨u.1, u.2.1, u.2.2.2⟩, u.2.2.1⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
    exact (Nat.card_congr eu).trans
      (bender_seven_outside_commuting_three_card localData geometry x.1 x.1.2 x.2)
  have hr (u : J) : Nat.card (F u) = 2 :=
    singleton_three_elements_card h localData hS structureData u
  simp only [hl, hr, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card] at hc
  have hE : Nat.card E = Nat.card (centralizer (S : Set G)) * 2 := by
    have he := bender_order_elements_card H 3
      (fun _ _ hs => isCyclic_of_prime_card (p := 3) hs)
    rw [geometry.three_subgroups, show Nat.totient 3 = 2 by decide] at he
    exact he
  rw [hE] at hc
  change Nat.card J = _
  nlinarith

end CFSG.Quasithin.Janko1CentralizerData
