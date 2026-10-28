module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Bookkeeping

/-!
# The commuting-involution incidence in Bender's count

Fusion transports the checked 31-involution count in `C_G(z)` to the
centralizer of every involution. Every involution in `H = N_G(Q)` lies in
the elementary abelian `Q`. Thus each of the seven involutions in `H`
commutes with all seven inside involutions and exactly 24 outside ones.
This is the source incidence used to eliminate fibers of size two.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, printed p.227, immediately before the collected distribution.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

include h in
/-- Each involution commutes with exactly 31 ambient involutions. -/
public theorem bender_commuting_involutions_card [IsSimpleGroup G]
    (u : G) (hu : orderOf u = 2) :
    Nat.card {t : G // orderOf t = 2 ∧ Commute t u} = 31 := by
  obtain ⟨g, hg⟩ := h.involutions_conjugate u hu
  let e := MulAut.conj g
  have he : e u = h.z := hg
  let ec : {t : G // orderOf t = 2 ∧ Commute t u} ≃
      {t : G // orderOf t = 2 ∧ Commute t h.z} :=
    e.toEquiv.subtypeEquiv (fun t => by
      change (orderOf t = 2 ∧ Commute t u) ↔ (orderOf (e t) = 2 ∧ Commute (e t) h.z)
      rw [e.orderOf_eq, ← he]
      apply and_congr_right
      intro _
      change t * u = u * t ↔ e t * e u = e u * e t
      rw [← map_mul, ← map_mul, e.injective.eq_iff])
  let ez : {t : G // orderOf t = 2 ∧ Commute t h.z} ≃
      {t : centralizer ({h.z} : Set G) // orderOf t = 2} :=
    { toFun := fun t => ⟨⟨t.1, mem_centralizer_singleton_iff.mpr t.2.2.eq⟩,
        (orderOf_injective _ (centralizer ({h.z} : Set G)).subtype_injective _).symm.trans t.2.1⟩
      invFun := fun t => ⟨t.1.1,
        (orderOf_injective _ (centralizer ({h.z} : Set G)).subtype_injective _).trans t.2,
        mem_centralizer_singleton_iff.mp t.1.2⟩
      left_inv := by intro t; rfl
      right_inv := by intro t; rfl }
  exact (Nat.card_congr (ec.trans ez)).trans h.centralizer_involution_count

/-- Each of the seven involutions in `H` commutes with 24 outside involutions,
the commuting-incidence total used to eliminate the size-two fibers. -/
public theorem bender_outside_commuting_involutions_card [IsSimpleGroup G]
    (u : G) (hu : orderOf u = 2) (huH : u ∈ normalizer (h.sylow : Set G)) :
    Nat.card {t : G // orderOf t = 2 ∧ Commute t u ∧
      t ∉ normalizer (h.sylow : Set G)} = 24 := by
  classical
  let H := normalizer (h.sylow : Set G)
  let J := {t : G // orderOf t = 2 ∧ Commute t u}
  let p : J → Prop := fun t => t.1 ∈ H
  have hcomm (t : G) (ht : orderOf t = 2) (htH : t ∈ H) : Commute t u := by
    let tQ : h.sylow := ⟨t, h.normalizer_involution_mem_sylow t ht htH⟩
    let uQ : h.sylow := ⟨u, h.normalizer_involution_mem_sylow u hu huH⟩
    exact congrArg Subtype.val (Commute.of_orderOf_dvd_two
      (fun a => orderOf_dvd_of_pow_eq_one (h.sylow_square a)) tQ uQ).eq
  let ei : {t : J // p t} ≃ BenderFiber H (benderBaseCoset H) :=
    { toFun := fun t => ⟨t.1.1, t.1.2.1, (benderRightCoset_eq_base_iff H _).mpr t.2⟩
      invFun := fun t => ⟨⟨t.1, t.2.1,
        hcomm t.1 t.2.1 ((benderRightCoset_eq_base_iff H _).mp t.2.2)⟩,
        (benderRightCoset_eq_base_iff H _).mp t.2.2⟩
      left_inv := by intro t; rfl
      right_inv := by intro t; rfl }
  let eo : {t : J // ¬ p t} ≃
      {t : G // orderOf t = 2 ∧ Commute t u ∧ t ∉ H} :=
    { toFun := fun t => ⟨t.1.1, t.1.2.1, t.1.2.2, t.2⟩
      invFun := fun t => ⟨⟨t.1, t.2.1, t.2.2.1⟩, t.2.2.2⟩
      left_inv := by intro t; rfl
      right_inv := by intro t; rfl }
  have hc := Nat.card_congr (Equiv.sumCompl p).symm
  rw [Nat.card_sum, Nat.card_congr ei, Nat.card_congr eo] at hc
  have hi : Nat.card (BenderFiber H (benderBaseCoset H)) = 7 := h.bender_base_fiber_card
  have hJ : Nat.card J = 31 := h.bender_commuting_involutions_card u hu
  change Nat.card {t : G // orderOf t = 2 ∧ Commute t u ∧ t ∉ H} = 24
  omega

end CFSG.Quasithin.Janko1CentralizerData
