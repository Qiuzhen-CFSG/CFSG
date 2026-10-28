module
public import CFSG.Quasithin.ChapterA.Section05To06.DihedralCounts
public import CFSG.Quasithin.ChapterA.Section05To06.Incidence

/-!
# The source two-involution-class order bounds

Thompson's exact order formula and the two dihedral injection bounds give
A.6.4 after the incidence identities eliminate the centralizer ratio.
For a conjugacy class closed under nonidentity products of commuting
members, the established incidence bijections specialize this to A.6.5.
All counts are natural numbers; multiplying by the positive centralizer
order avoids division. The actual Chapter J.3 consumer uses z and s.

Source: Aschbacher--Smith A.6.4--5, printed pp.64--65.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section05To06
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z t : G}

theorem lemma_A_6_4 (h : TwoInvolutionClasses z t) :
    (centralizer ({z} : Set G)).index ≤
      c1 t z * (b1 t + b2 z) + c2 t z * (b2 t + b1 z) := by
  have hz : a z t z ≤ b1 z * c1 z t + b2 z * c2 z t := by
    rw [a_eq_add h.order_z]
    exact add_le_add (a1_z_le h) (a2_z_le h)
  have ht : a z t t ≤ b1 t * c1 t z + b2 t * c2 t z := by
    rw [a_eq_add h.order_t]
    exact add_le_add (a1_t_le h) (a2_t_le h)
  obtain ⟨hc1,hc2⟩ := lemma_A_6_3 h
  refine Nat.le_of_mul_le_mul_left (c := Nat.card (centralizer ({z} : Set G))) ?_
    (Nat.card_pos (α := centralizer ({z} : Set G)))
  calc
    Nat.card (centralizer ({z} : Set G)) * (centralizer ({z} : Set G)).index =
        Nat.card G := (centralizer ({z} : Set G)).card_mul_index
    _ = Nat.card (centralizer ({z} : Set G)) * a z t t +
      Nat.card (centralizer ({t} : Set G)) * a z t z := lemma_A_6_1 h
    _ ≤ Nat.card (centralizer ({z} : Set G)) * (b1 t * c1 t z + b2 t * c2 t z) +
      Nat.card (centralizer ({t} : Set G)) * (b1 z * c1 z t + b2 z * c2 z t) :=
        add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hz)
    _ = Nat.card (centralizer ({z} : Set G)) * (b1 t * c1 t z + b2 t * c2 t z) +
      b1 z * (Nat.card (centralizer ({t} : Set G)) * c1 z t) +
      b2 z * (Nat.card (centralizer ({t} : Set G)) * c2 z t) := by ring
    _ = _ := by rw [← hc1, ← hc2]; ring

theorem lemma_A_6_5 (h : TwoInvolutionClasses z t)
    (closed : ∀ u v : G, IsConj z u → IsConj z v → Commute u v →
      u*v ≠ 1 → IsConj z (u*v)) :
    (centralizer ({z} : Set G)).index ≤
      Nat.card {u : G // IsConj z u ∧ Commute u t} *
        (Nat.card {u : G // IsConj z u ∧ Commute u t} +
          Nat.card {u : G // IsConj z u ∧ Commute u z}) := by
  have hb := lemma_A_6_4 h
  rw [c1_eq_zero_of_closed h closed, zero_mul, zero_add,
    c2_eq_card_of_closed h closed, b2_eq_card_add_one_of_closed h closed] at hb
  have hz := b1_add_one_eq_card_of_closed h closed
  have he : Nat.card {u : G // IsConj z u ∧ Commute u t} + 1 + b1 z =
      Nat.card {u : G // IsConj z u ∧ Commute u t} +
        Nat.card {u : G // IsConj z u ∧ Commute u z} := by omega
  rwa [he] at hb

end CFSG.Quasithin.ChapterA.Section05To06
