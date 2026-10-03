module
public import Mathlib.Combinatorics.Configuration
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.FinCases

/-!
# The incidence table of the plane of order three

Label a quadrangle by 0,1,2,3; its diagonal points by 4,5,6; and the
fourth points of its six sides by 7,...,12. The six sides determine the
entire plane: a further line has four points and meets each side once.
The finite computation below checks that precisely seven subsets qualify.
The certificate is checked by kernel reduction.

This is the elementary small-order coordinatization argument underlying
Wong, *On finite groups whose 2-Sylow subgroups have cyclic subgroups of
index 2*, Theorem 6(b), printed p.111 (10.1017/S1446788700022771).
-/

namespace Configuration.Three

@[expose] public section

def line : Fin 13 → Finset (Fin 13) := ![
  {0,1,4,7}, {0,2,5,8}, {0,3,6,9}, {1,2,6,10}, {1,3,5,11}, {2,3,4,12},
  {4,5,9,10}, {4,6,8,11}, {5,6,7,12}, {0,10,11,12}, {1,8,9,12},
  {2,7,9,11}, {3,7,8,10}]

def compatible (s : Finset (Fin 13)) : Prop :=
  ∀ j : Fin 6, s = line (j.castLE (by decide)) ∨
    (s ∩ line (j.castLE (by decide))).card = 1

instance (s : Finset (Fin 13)) : Decidable (compatible s) :=
  inferInstanceAs (Decidable (∀ _j : Fin 6, _))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem classify_certificate :
    ((Finset.univ : Finset (Fin 13)).powersetCard 4).filter compatible =
      Finset.univ.image line := by
  decide +kernel

theorem classify (s : Finset (Fin 13)) (hc : s.card = 4) (hs : compatible s) :
    ∃ i, s = line i := by
  have hm : s ∈ ((Finset.univ : Finset (Fin 13)).powersetCard 4).filter compatible :=
    Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc⟩, hs⟩
  rw [classify_certificate] at hm
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
  exact ⟨i, hi.symm⟩

theorem line_injective : Function.Injective line := by decide +kernel

theorem distinguish_points : ∀ i k : Fin 13,
    (∀ j : Fin 6, i ∈ line (j.castLE (by decide)) ↔
      k ∈ line (j.castLE (by decide))) → i = k := by
  decide +kernel

/-- Thirteen point labels together with the incidence table of the six sides
of a quadrangle. Distinctness and exhaustiveness follow from this data in an
order-three projective plane. -/
structure SideChart (P L : Type*) [Membership P L] where
  point : Fin 13 → P
  side : Fin 6 → L
  incident : ∀ i j, point i ∈ side j ↔ i ∈ line (j.castLE (by decide))

section Cardinality

variable {P L : Type*} [Membership P L] [Finite P] [Finite L]
  [ProjectivePlane P L] (h : ∀ l : L, pointCount P l = 4)

include h

theorem order_eq_three : ProjectivePlane.order P L = 3 := by
  obtain ⟨_, _, _, l, _⟩ := ProjectivePlane.exists_config (P := P) (L := L)
  have := h l
  rw [ProjectivePlane.pointCount_eq] at this
  omega

theorem card_points : Nat.card P = 13 := by
  let : Fintype P := Fintype.ofFinite P
  rw [Nat.card_eq_fintype_card, ProjectivePlane.card_points P L, order_eq_three h]
  rfl

theorem card_lines : Nat.card L = 13 := by
  let : Fintype L := Fintype.ofFinite L
  rw [Nat.card_eq_fintype_card, ProjectivePlane.card_lines P L, order_eq_three h]
  rfl


end Cardinality

namespace SideChart

variable {P L : Type*} [Membership P L] (c : SideChart P L)

theorem point_injective : Function.Injective c.point := by
  intro i k hik
  apply distinguish_points i k
  intro j
  rw [← c.incident, ← c.incident, hik]

end SideChart

end

end Configuration.Three
