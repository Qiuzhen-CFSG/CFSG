module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.LocalCounts.Model

/-!
# Ambient involutions commuting with a local odd-prime element

The ambient centralizer of an element of order three or five has Sylow
2-subgroups of order two, by the explicit structural input. Sylow conjugacy
therefore puts all its involutions into the conjugacy class of the marked
involution `z`. Its stabilizer is the actual common centralizer with `z`,
whose order is six or ten by the local `A₅ × C₂` calculation.

Orbit–stabilizer proves the count without identifying an abstract semidirect
product model. Only the element of odd prime order is restricted to `C_G(z)`;
the involutions counted below range over all of `G`.

Source: Bender, *Finite groups with large subgroups* (1974), §4, printed
pp.225–226, the two commuting assertions of (4.2).
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

private theorem involutions_conjugate_of_sylow_two_card
    (hP : ∀ P : Sylow 2 G, Nat.card P = 2) (z : G) (hz : orderOf z = 2)
    (t : G) (ht : orderOf t = 2) : ∃ g : G, g * t * g⁻¹ = z := by
  classical
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow_card_eq_prime (zpowers z) z
    (mem_zpowers z) hz hP t ht
  have he : g * t * g⁻¹ = 1 ∨ g * t * g⁻¹ = z := by
    rw [mem_zpowers_iff_mem_range_orderOf, hz] at hg
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hg
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · exact Or.inl (by simpa using he.symm)
    · exact Or.inr (by simpa using he.symm)
  rcases he with he | he
  · have ho := (MulAut.conj g).orderOf_eq t
    change orderOf (g * t * g⁻¹) = orderOf t at ho
    rw [he, orderOf_one, ht] at ho
    contradiction
  · exact ⟨g, he⟩

private theorem involution_count_mul_centralizer_of_sylow_two_card
    (hP : ∀ P : Sylow 2 G, Nat.card P = 2) (z : G) (hz : orderOf z = 2) :
    Nat.card {t : G // orderOf t = 2} * Nat.card (centralizer ({z} : Set G)) =
      Nat.card G := by
  have he : (ConjClasses.mk z).carrier = {t : G | orderOf t = 2} := by
    ext t
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    constructor
    · intro ht
      obtain ⟨g, hg⟩ := isConj_iff.mp ht
      have hc := (MulAut.conj g).orderOf_eq t
      rw [show (MulAut.conj g) t = z from hg, hz] at hc
      exact hc.symm
    · intro ht
      exact isConj_iff.mpr (involutions_conjugate_of_sylow_two_card hP z hz t ht)
  change Nat.card ({t : G | orderOf t = 2} : Set G) * _ = _
  rw [← he, ConjClasses.nat_card_carrier_eq_index_centralizer]
  exact (centralizer ({z} : Set G)).index_mul_card

omit [Finite G] in
private theorem commuting_count_eq_centralizer_involution_count (x : G) :
    Nat.card {t : G // orderOf t = 2 ∧ Commute t x} =
      Nat.card {t : centralizer ({x} : Set G) // orderOf t = 2} := by
  apply Nat.card_congr
  refine
    { toFun := fun t => ⟨⟨t, mem_centralizer_singleton_iff.mpr t.property.2.eq⟩, ?_⟩
      invFun := fun t => ⟨t.1, ?_, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · exact (orderOf_injective (centralizer ({x} : Set G)).subtype
      Subtype.val_injective _).symm.trans t.property.1
  · exact (orderOf_injective (centralizer ({x} : Set G)).subtype
      Subtype.val_injective _).trans t.property
  · exact mem_centralizer_singleton_iff.mp t.1.property

variable (h : Janko1CentralizerData G) (s : OddPrimeCentralizerStructure h)
include s

/-- The ambient commuting-involution count times its local stabilizer order
is the order of the full odd-prime centralizer. -/
public theorem commuting_prime_count_mul_of_structure (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    Nat.card {t : G // orderOf t = 2 ∧ Commute t x} * (2 * p) =
      Nat.card (centralizer ({x} : Set G)) := by
  let C := centralizer ({x} : Set G)
  have hzC : h.z ∈ C :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hxC).symm
  let zC : C := ⟨h.z, hzC⟩
  have hz : orderOf zC = 2 :=
    (orderOf_injective C.subtype Subtype.val_injective zC).symm.trans h.involution
  have hP (P : Sylow 2 C) : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity]
    change 2 ^ (Nat.card (centralizer ({x} : Set G))).factorization 2 = 2
    rcases s.centralizer_card_cases p hp x hxC hx with hc | hc
    · rw [hc]
      rcases hp with rfl | rfl <;> decide +kernel
    · rw [hc]
      decide +kernel
  have hc : Nat.card (centralizer ({zC} : Set C)) = 2 * p := by
    rw [← card_map_of_injective (K := centralizer ({zC} : Set C)) (f := C.subtype)
      C.subtype_injective, map_subtype_centralizer_singleton]
    change Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({h.z} : Set G) :
      Subgroup G) = 2 * p
    rw [inf_comm]
    exact h.common_prime_centralizer_card p hp x hxC hx
  rw [commuting_count_eq_centralizer_involution_count]
  exact hc ▸ involution_count_mul_centralizer_of_sylow_two_card hP zC hz

end CFSG.Quasithin.Janko1CentralizerData
