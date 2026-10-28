module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.Fusion

/-!
# Centralizers of four-groups in the J₁ local configuration

Involution fusion transports the common-centralizer calculation at `z`
to any pair of distinct commuting involutions. A four-group lies in an
elementary abelian Sylow two-subgroup of order eight. That Sylow subgroup
centralizes the four-group, while two of its involutions bound the whole
centralizer above by eight. Thus the centralizer is exactly that Sylow
subgroup, and its intersection with every odd subgroup is trivial.

These are the assertions `C_G(V)` is Sylow and `C_A(V) = 1` used in
Bender, *Finite groups with large subgroups* (1974), (4.1), printed p.225,
in the exclusion of the elementary abelian order-27 configuration.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)
include h
/-- Fusion transports the common-centralizer calculation to any pair
of distinct commuting involutions. -/
public theorem common_centralizer_card_of_involutions [IsSimpleGroup G]
    (t u : G) (ht : orderOf t = 2) (hcomm : Commute t u)
    (hu : u ^ 2 = 1) (hne : u ∉ zpowers t) :
    Nat.card (centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G) = 8 := by
  obtain ⟨g, hg⟩ := h.involutions_conjugate t ht
  let e := MulAut.conj g
  have he : e t = h.z := hg
  have huC : e u ∈ centralizer ({h.z} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← he, ← map_mul, ← map_mul, hcomm.eq]
  have hu2 : (e u) ^ 2 = 1 := by rw [← map_pow, hu, map_one]
  have hun : e u ∉ zpowers h.z := by
    intro huZ
    have hmap : (zpowers t).map e.toMonoidHom = zpowers h.z := by
      rw [MonoidHom.map_zpowers]
      exact congrArg zpowers he
    rw [← hmap] at huZ
    obtain ⟨v, hv, hev⟩ := huZ
    exact hne ((e.injective hev) ▸ hv)
  let ec : (centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G) ≃
      (centralizer ({h.z} : Set G) ⊓ centralizer ({e u} : Set G) : Subgroup G) :=
    e.toEquiv.subtypeEquiv (fun y => by
      simp only [mem_inf, mem_centralizer_singleton_iff, ← he]
      change (y * t = t * y ∧ y * u = u * y) ↔
        (e y * e t = e t * e y ∧ e y * e u = e u * e y)
      simp only [← map_mul, e.injective.eq_iff])
  exact (Nat.card_congr ec).trans (h.common_centralizer_card (e u) huC hu2 hun)

/-- The centralizer of any four-group is an ambient Sylow two-subgroup. -/
public theorem four_centralizer_is_sylow [IsSimpleGroup G]
    (V : Subgroup G) (hV : Nat.card V = 4) :
    ∃ S : Sylow 2 G, centralizer (V : Set G) = (S : Subgroup G) := by
  have hpV : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by simpa using hV)
  obtain ⟨S, hS⟩ := hpV.exists_le_sylow
  obtain ⟨tV, htV⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 (by rw [hV]; decide)
  let t : G := tV
  have ht : orderOf t = 2 :=
    (orderOf_injective V.subtype Subtype.val_injective tV).trans htV
  have hnle : ¬ V ≤ zpowers t := by
    intro hle
    have hc := card_le_of_le hle
    rw [hV, Nat.card_zpowers, ht] at hc
    omega
  obtain ⟨u, huV, hune⟩ := SetLike.not_le_iff_exists.mp hnle
  have hcomm : Commute t u := congrArg Subtype.val
    (Commute.of_orderOf_dvd_two
      (fun a => orderOf_dvd_of_pow_eq_one (h.any_sylow_square S a))
      (⟨t, hS tV.property⟩ : S) ⟨u, hS huV⟩).eq
  have hu2 : u ^ 2 = 1 := congrArg Subtype.val
    (h.any_sylow_square S ⟨u, hS huV⟩)
  have hCbound : Nat.card (centralizer (V : Set G)) ≤ 8 := by
    calc
      Nat.card (centralizer (V : Set G)) ≤
          Nat.card (centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G) :=
        card_le_of_le (le_inf
          (centralizer_le (Set.singleton_subset_iff.mpr tV.property))
          (centralizer_le (Set.singleton_subset_iff.mpr huV)))
      _ = 8 := h.common_centralizer_card_of_involutions t u ht hcomm hu2 hune
  have hle : (S : Subgroup G) ≤ centralizer (V : Set G) := by
    let _ := h.any_sylow_elementaryAbelian S
    exact (Subgroup.le_centralizer (S : Subgroup G)).trans (centralizer_le hS)
  refine ⟨S, (eq_of_le_of_card_ge hle ?_).symm⟩
  rwa [h.any_sylow_card S]

/-- Bender's four-group centralizer has order eight. -/
public theorem four_centralizer_card [IsSimpleGroup G]
    (V : Subgroup G) (hV : Nat.card V = 4) : Nat.card (centralizer (V : Set G)) = 8 := by
  obtain ⟨S, hS⟩ := h.four_centralizer_is_sylow V hV
  rw [hS, h.any_sylow_card S]

/-- In particular, a four-group has trivial fixed subgroup in every odd subgroup. -/
public theorem odd_inf_four_centralizer_eq_bot [IsSimpleGroup G]
    (A V : Subgroup G) (hA : Odd (Nat.card A)) (hV : Nat.card V = 4) :
    A ⊓ centralizer (V : Set G) = ⊥ := by
  apply Disjoint.eq_bot
  apply disjoint_of_coprime_natCard
  rw [h.four_centralizer_card V hV]
  exact hA.coprime_two_right.pow_right 3

end CFSG.Quasithin.Janko1CentralizerData
