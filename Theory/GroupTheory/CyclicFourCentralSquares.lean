module
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
public import Theory.Frattini.BinarySquares

/-!
# Squares of a cyclic center of order four

The squares of the actual center form its unique subgroup of order two.
Keeping this subgroup inside the original group makes quotient and central
embedding calculations independent of a chosen cyclic generator. In a finite
two-subgroup containing the center, if all squares are central squares, the
square-generation description of Frattini identifies its exact Frattini subgroup.

This is the elementary central-layer calculation used in Aschbacher–Smith
I.2.2(6), printed pp.410 and 412; no sporadic-group assumptions enter here.
-/

@[expose] public section
open scoped IsMulCommutative
namespace Subgroup
variable (G : Type*) [Group G]

/-- Squares of central elements, as a subgroup of the original group. -/
def centralSquares : Subgroup G :=
  (powMonoidHom 2 : center G →* center G).range.map (center G).subtype

variable {G}

theorem centralSquares_le_center : centralSquares G ≤ center G :=
  (map_le_range (center G).subtype _).trans (by rw [range_subtype])

instance centralSquares_normal : (centralSquares G).Normal :=
  ⟨fun x hx g => by
    rw [mem_center_iff.mp (centralSquares_le_center hx) g, mul_inv_cancel_right]
    exact hx⟩

@[simp] theorem mem_centralSquares {x : G} :
    x ∈ centralSquares G ↔ ∃ z : center G, (z : G) ^ 2 = x := by
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z ^ 2, ⟨z, rfl⟩, rfl⟩

theorem centralSquares_card [Finite G] [IsCyclic (center G)]
    (hZ : Nat.card (center G) = 4) : Nat.card (centralSquares G) = 2 := by
  rw [centralSquares, card_map_of_injective (center G).subtype_injective,
    IsCyclic.card_powMonoidHom_range, hZ]
  decide

theorem centralSquares_square [Finite G] (hZ : Nat.card (center G) = 4)
    {x : G} (hx : x ∈ centralSquares G) : x ^ 2 = 1 := by
  obtain ⟨z, rfl⟩ := mem_centralSquares.mp hx
  have hz := congrArg Subtype.val (pow_card_eq_one' (x := z))
  simpa only [hZ, coe_pow, coe_one, ← pow_mul] using hz

/-- The subgroup is precisely the square-one part of the actual cyclic center. -/
theorem mem_centralSquares_iff [Finite G] [IsCyclic (center G)]
    (hZ : Nat.card (center G) = 4) (x : G) :
    x ∈ centralSquares G ↔ x ∈ center G ∧ x ^ 2 = 1 := by
  have he : (powMonoidHom 2 : center G →* center G).range =
      (powMonoidHom 2 : center G →* center G).ker := by
    apply eq_of_le_of_card_ge
    · rintro y ⟨z, rfl⟩
      change (z ^ 2) ^ 2 = 1
      rw [← pow_mul]
      simpa only [hZ] using pow_card_eq_one' (x := z)
    · rw [IsCyclic.card_powMonoidHom_range, IsCyclic.card_powMonoidHom_ker, hZ]
      decide
  rw [centralSquares, he]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.property, congrArg Subtype.val hz⟩
  · rintro ⟨hz, hs⟩
    exact ⟨⟨x, hz⟩, Subtype.ext hs, rfl⟩

/-- Quotienting the actual center by its squares leaves a kernel of order two. -/
theorem centralSquares_center_image_card [Finite G] [IsCyclic (center G)]
    (hZ : Nat.card (center G) = 4) :
    Nat.card ((center G).map (QuotientGroup.mk' (centralSquares G))) = 2 := by
  let q := QuotientGroup.mk' (centralSquares G)
  have hle : q.ker ≤ center G := by
    rw [QuotientGroup.ker_mk']
    exact centralSquares_le_center
  have hc := (q.ker.subgroupOf (center G)).index_mul_card
  change q.ker.relIndex (center G) * Nat.card (q.ker.subgroupOf (center G)) = _ at hc
  rw [relIndex_ker, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
    QuotientGroup.ker_mk', centralSquares_card hZ, hZ] at hc
  change Nat.card ((center G).map q) = 2
  omega

/-- If all squares in a two-subgroup are central squares and the subgroup contains
all central elements, its Frattini subgroup is exactly those central squares. -/
theorem frattini_map_eq_centralSquares [Finite G] (R : Subgroup G)
    (hR : IsPGroup 2 R) (hZR : center G ≤ R)
    (hs : ∀ x : R, (x : G) ^ 2 ∈ centralSquares G) :
    (frattini R).map R.subtype = centralSquares G := by
  apply le_antisymm
  · rw [map_le_iff_le_comap, hR.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    exact hs x
  · intro x hx
    obtain ⟨z, rfl⟩ := mem_centralSquares.mp hx
    let y : R := ⟨z, hZR z.property⟩
    let : Fact (IsPGroup 2 R) := ⟨hR⟩
    exact ⟨y ^ 2, pth_power_mem_frattini_of_isPGroup (p := 2) y, rfl⟩

end Subgroup
