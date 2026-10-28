module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FoldedCellGeometry
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.Representation.BinaryPrimeDegree

/-!
# The degree-twelve endpoint for binary triality

The genuine carrier ³D₄(2) has order 211341312. Its prime divisor 13 forces
any faithful binary representation to have degree at least twelve. The entire
carrier order nevertheless divides |GL₁₂(2)|, so this necessary divisibility
condition cannot exclude degree twelve.

The actual two-cell decompositions give orders 258048 and 86016 for the arms
and central parabolics. Neither order is divisible by 49. Consequently a
subgroup whose order is divisible by 49 cannot lie in either root parabolic.
In particular, a proposed degree argument using an elementary subgroup of
order 49 and its normalizer requires a construction beyond these parabolics.
No such subgroup or normalizer action is assumed or constructed here.

All cardinalities use the original elementary graph-field subgroup and its
own-center quotient. These are endpoint and route-obstruction results, not a
proof of the triality exclusion in Aschbacher–Smith G.9.3, printed p.356
(PDF p.367) of `refs/quasithin.pdf`. The root-cell counts are from GLS3 §§2.3–2.4,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section

namespace Triality.BinaryTwoObstruction
open Standard Standard.Parabolics Standard.ConcreteBruhat

local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "T" => BinaryCarrier 1 Nat.zero_lt_one

/-- The order of the genuine smallest binary triality carrier. -/
theorem card_carrier : Nat.card T = 211341312 := by
  rw [FixedCellCount.card_carrier, FixedCellCount.card_borel]
  norm_num [binaryParameters_q]

/-- Whole-group order divisibility is compatible with degree twelve. -/
theorem card_dvd_GL_twelve :
    Nat.card T ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 12) (ZMod 2)) := by
  rw [card_carrier, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]

/-- The order-thirteen obstruction applies without an irreducibility assumption. -/
theorem degree_ge_twelve
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) T V) (hρ : Function.Injective ρ) :
    12 ≤ Module.finrank (ZMod 2) V := by
  rw [← Representation.BinaryPrimeDegree.orderOf_two_mod_thirteen]
  apply Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hρ (by decide) (by decide)
  rw [card_carrier]
  norm_num

/-- Count each actual root parabolic using its two disjoint Bruhat cells. -/
theorem parabolic_card (a : Node) :
    Nat.card (parabolic P a) = (match a with | .arms => 258048 | .central => 86016) := by
  classical
  have he : (parabolic P a : Set T) =
      (borel P : Set T) ∪ cell P rfl (relativeReflection a) := by
    ext g
    exact FoldedCellGeometry.mem_parabolic_iff 1 Nat.zero_lt_one a g
  have hd : Disjoint (borel P : Set T) (cell P rfl (relativeReflection a)) := by
    apply Set.disjoint_left.mpr
    intro g hb hc
    have h1 : g ∈ cell P rfl 1 := (cell_one P rfl).ge hb
    exact (relativeReflection_involution a).1
      (FixedDescent.cell_index_unique 1 Nat.zero_lt_one hc h1)
  have hcard := Nat.card_congr ((Equiv.setCongr he).trans (Equiv.Set.union hd))
  rw [Nat.card_sum] at hcard
  change Nat.card (parabolic P a) = Nat.card (borel P) +
    Nat.card {g : T // g ∈ cell P rfl (relativeReflection a)} at hcard
  rw [FixedCellCount.card_cell, FixedCellCount.card_borel] at hcard
  rw [hcard]
  cases a <;> norm_num [binaryParameters_q, FixedCellCount.inversionCount_table,
    relativeReflection] <;> decide +kernel

/-- Neither root parabolic contains the full factor 7² of the carrier order. -/
theorem fortyNine_not_dvd_parabolic_card (a : Node) :
    ¬ 49 ∣ Nat.card (parabolic P a) := by
  rw [parabolic_card]
  cases a <;> norm_num

/-- A subgroup supplying a factor 7² must be constructed outside both parabolics. -/
theorem not_le_parabolic_of_fortyNine_dvd (R : Subgroup T)
    (hR : 49 ∣ Nat.card R) (a : Node) : ¬ R ≤ parabolic P a := by
  intro hle
  exact fortyNine_not_dvd_parabolic_card a (hR.trans (Subgroup.card_dvd_of_le hle))

end Triality.BinaryTwoObstruction
