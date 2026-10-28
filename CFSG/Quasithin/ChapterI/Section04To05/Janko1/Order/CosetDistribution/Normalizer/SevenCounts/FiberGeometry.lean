module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.FiberGeometry.Census

/-!
# The seven-normalizer inversion geometry

The supplied local structure suffices for the full geometry of
H = N_G(C_G(S)). The cyclic quotient of order six controls external
normalizer intersections and hence the literal inverted subgroups.
Conjugation into the complement gives the subgroup census and the
centralizers of the order-three subgroups. Applying this geometry to the
actual right-coset fibers supplies their five possible sizes.

The structure witness remains an explicit input, independent of its producer.
No incidence equation, ambient order or recognition theorem is used.
Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), proof of (4.3), printed p.226.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

/-- The local seven-centralizer structure gives every field of the geometry
used in Bender's contrary-case fiber count. -/
public theorem bender_seven_geometry
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)
    (S : Subgroup G) (hS : Nat.card S = 7)
    (structureData : BenderSevenStructure h S) : BenderSevenGeometry S := by
  exact {
    inverted_subgroup := fun u _ huH =>
      structureData.fiber_inverted_subgroup localData hS u huH
    three_subgroups := structureData.fiber_three_subgroups localData hS
    six_subgroups := structureData.fiber_six_subgroups localData hS
    six_cyclic := fun K hK hc =>
      structureData.fiber_small_subgroup_cyclic localData hS K hK (by rw [hc])
    three_centralizer := structureData.fiber_three_centralizer localData hS }

/-- In the literal right-coset convention, every non-base involution fiber
has size zero, one, two, three or six. This discharges the geometric input
to the independent seven-normalizer incidence calculation. -/
public theorem bender_seven_fiber_sizes
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)
    (S : Subgroup G) (hS : Nat.card S = 7)
    (structureData : BenderSevenStructure h S)
    (ω : G ⧸ normalizer (centralizer (S : Set G) : Set G))
    (hω : ω ≠ benderBaseCoset (normalizer (centralizer (S : Set G) : Set G))) :
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 0 ∨
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 1 ∨
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 2 ∨
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 3 ∨
    Nat.card (BenderFiber (normalizer (centralizer (S : Set G) : Set G)) ω) = 6 :=
  (h.bender_seven_geometry localData S hS structureData).fiber_sizes ω hω

end CFSG.Quasithin.Janko1CentralizerData
