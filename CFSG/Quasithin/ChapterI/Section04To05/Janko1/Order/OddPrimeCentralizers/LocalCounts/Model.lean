module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.LocalCounts.Orders

/-!
# Odd-prime common centralizers in the actual local model

Two kernel-checked calculations, for one three-cycle and one five-cycle in
`A₅ × C₂`, give centralizer orders six and ten. Sylow conjugacy extends
these calculations to every element of the corresponding order. The actual
source equivalence then identifies `C_G(z) ∩ C_G(x)` and its cardinality.

Source: Bender, *Finite groups with large subgroups* (1974), §4, printed
pp.225–226. These are stabilizer orders used to count commuting involutions
in (4.2); the counted involutions need not lie in `C_G(z)`.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

private abbrev M := alternatingGroup (Fin 5) × Multiplicative (ZMod 2)

private def three : M :=
  (⟨Equiv.swap 0 1 * Equiv.swap 1 2, by simp [Equiv.Perm.mem_alternatingGroup]⟩, 1)

private def five : M :=
  (⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4,
    by simp [Equiv.Perm.mem_alternatingGroup]⟩, 1)

private theorem three_order : orderOf three = 3 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

private theorem five_order : orderOf five = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

private theorem three_centralizer_card :
    Fintype.card {y : M // y * three = three * y} = 6 := by decide +kernel

private theorem five_centralizer_card :
    Fintype.card {y : M // y * five = five * y} = 10 := by decide +kernel

private theorem model_card : Nat.card M = 120 := by
  rw [Nat.card_prod, nat_card_alternatingGroup]
  norm_num [Nat.factorial, Nat.card_eq_fintype_card]

private theorem model_prime_centralizer_card (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : M) (hx : orderOf x = p) : Nat.card (centralizer ({x} : Set M)) = 2 * p := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  have hP (P : Sylow p M) : Nat.card P = p := by
    rw [P.card_eq_multiplicity, model_card]
    rcases hp with rfl | rfl <;> decide +kernel
  rcases hp with rfl | rfl
  · rw [LocalCounts.prime_centralizer_card_eq 3 hP x three hx three_order]
    have he : centralizer ({three} : Set M) ≃ {y : M // y * three = three * y} :=
      Equiv.subtypeEquivRight (fun _ => mem_centralizer_singleton_iff)
    rw [Nat.card_congr he, Nat.card_eq_fintype_card]
    exact three_centralizer_card
  · rw [LocalCounts.prime_centralizer_card_eq 5 hP x five hx five_order]
    have he : centralizer ({five} : Set M) ≃ {y : M // y * five = five * y} :=
      Equiv.subtypeEquivRight (fun _ => mem_centralizer_singleton_iff)
    rw [Nat.card_congr he, Nat.card_eq_fintype_card]
    exact five_centralizer_card

variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- The local model determines the stabilizer of `z` in the ambient
centralizer of an element of order three or five. -/
public theorem common_prime_centralizer_card (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    Nat.card (centralizer ({h.z} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) =
      2 * p := by
  let C := centralizer ({h.z} : Set G)
  let xC : C := ⟨x, hxC⟩
  let e := h.alternatingCentralizerEquiv
  have hxorder : orderOf (e xC) = p := (e.orderOf_eq xC).trans
    ((orderOf_injective C.subtype Subtype.val_injective xC).symm.trans hx)
  let ec : centralizer ({xC} : Set C) ≃ centralizer ({e xC} : Set M) :=
    e.toEquiv.subtypeEquiv (fun y => by
      rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
      change y * xC = xC * y ↔ e y * e xC = e xC * e y
      rw [← map_mul, ← map_mul, e.injective.eq_iff])
  rw [← map_subtype_centralizer_singleton C xC,
    card_map_of_injective Subtype.val_injective, Nat.card_congr ec]
  exact model_prime_centralizer_card p hp _ hxorder

end CFSG.Quasithin.Janko1CentralizerData
