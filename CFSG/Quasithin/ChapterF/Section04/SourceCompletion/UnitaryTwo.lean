module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.BinaryOrders
public import Theory.GroupTheory.Amalgam.RankTwoCompletion
public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.GroupAction.RankTwoCosetCover.PathTransport
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon
/-!
# Literal geometry of a faithful binary unitary-four completion

The endpoint injections force orders 576 and 960. Their gcd is the marked
middle order 192, hence their full intersection is already the marked image.
The resulting connected bipartite coset graph has valencies three and five.
Finite ambient orders are multiples of 2880; the bound in F.4.24 leaves nine
numerical possibilities before the short-path and quadrangle argument.

This supplies actual completion consequences, not a recognition certificate.
Source: Aschbacher–Smith F.3.3, F.4.6 and F.4.24, printed pp.270, 276 and 287.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo
open Theory.GroupTheory
open Subgroup.CosetGeometry
open Subgroup.CosetGeometry.RankTwo
local notation "ModelAmalgam" => GreenBook.LieModels.UnitaryFour.amalgam 1 (Nat.le_refl 1)

/-- A faithful completion of the actual marked binary unitary-four amalgam. -/
abbrev Completion (G : Type*) [Group G] :=
  RankTwoAmalgam.FaithfulCompletion ModelAmalgam (G := G)

variable {G : Type*} [Group G] (c : Completion G)
namespace Completion
/-- The point and plane endpoint images, in the source order. -/
def family : Bool → Subgroup G := fun i => bif i then c.right.range else c.left.range
abbrev Vertex := RankTwo.Vertex c.family
abbrev graph := RankTwo.graph c.family

@[simp] theorem family_false : c.family false = c.left.range := rfl
@[simp] theorem family_true : c.family true = c.right.range := rfl

theorem left_card : Nat.card c.left.range = 576 :=
  (RankTwoAmalgam.FaithfulCompletion.left_card c).trans GreenBook.LieModels.UnitaryFour.BinaryCompletion.point_card
theorem right_card : Nat.card c.right.range = 960 :=
  (RankTwoAmalgam.FaithfulCompletion.right_card c).trans GreenBook.LieModels.UnitaryFour.BinaryCompletion.plane_card
theorem middle_card : Nat.card c.middle.range = 192 :=
  (RankTwoAmalgam.FaithfulCompletion.middle_card c).trans GreenBook.LieModels.UnitaryFour.BinaryCompletion.middle_card

/-- Faithfulness already forces the overlap required for the actual coset graph. -/
theorem overlap : c.left.range ⊓ c.right.range = c.middle.range := by
  apply c.overlap_eq_of_gcd
  rw [GreenBook.LieModels.UnitaryFour.BinaryCompletion.point_card,
    GreenBook.LieModels.UnitaryFour.BinaryCompletion.plane_card,
    GreenBook.LieModels.UnitaryFour.BinaryCompletion.middle_card]
  norm_num

theorem connected : c.graph.Connected := RankTwo.connected c.family c.generated

theorem bipartite : c.graph.IsBipartiteWith
    {v : c.Vertex | v.type = false} {v : c.Vertex | v.type = true} :=
  coset_bipartition c.family

theorem graphAction : SimpleGraph.PathTransitivePolygon.GraphAction c.graph G where
  map_adj g := (translationGraphIso c.family g).toHom.map_adj

/-- Both local indices are forced by the original full parabolic orders. -/
theorem local_indices :
    (c.right.range.subgroupOf c.left.range).index = 3 ∧
    (c.left.range.subgroupOf c.right.range).index = 5 := by
  have hleft : Nat.card (c.right.range.subgroupOf c.left.range) = 192 := by
    rw [← Subgroup.inf_subgroupOf_left, c.overlap]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.middle_le_left).toEquiv).trans
      (middle_card c)
  have hright : Nat.card (c.left.range.subgroupOf c.right.range) = 192 := by
    rw [← Subgroup.inf_subgroupOf_right, c.overlap]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.middle_le_right).toEquiv).trans
      (middle_card c)
  have hl := (c.right.range.subgroupOf c.left.range).card_mul_index
  have hr := (c.left.range.subgroupOf c.right.range).card_mul_index
  rw [hleft, left_card c] at hl
  rw [hright, right_card c] at hr
  constructor <;> omega

theorem neighbor_cards :
    Nat.card (c.graph.neighborSet (RankTwo.base c.family false)) = 3 ∧
    Nat.card (c.graph.neighborSet (RankTwo.base c.family true)) = 5 := by
  constructor
  · exact (card_neighbor_base c.family false).trans (local_indices c).1
  · exact (card_neighbor_base c.family true).trans (local_indices c).2

/-- Valence is three or five at every vertex of its respective type. -/
theorem card_neighbors (v : c.Vertex) :
    Nat.card (c.graph.neighborSet v) = (if v.type then 5 else 3) := by
  obtain ⟨g, hg⟩ := exists_smul_base c.family v
  have hh := Nat.card_congr
    ((translationGraphIso c.family g).mapNeighborSet (RankTwo.base c.family v.type))
  change Nat.card (c.graph.neighborSet (RankTwo.base c.family v.type)) =
    Nat.card (c.graph.neighborSet (g • RankTwo.base c.family v.type)) at hh
  rw [hg] at hh
  rw [← hh]
  cases hv : v.type
  · exact (neighbor_cards c).1
  · exact (neighbor_cards c).2

include c

theorem order_multiple [Finite G] : 2880 ∣ Nat.card G := by
  have hl : Nat.card c.left.range ∣ Nat.card G :=
    ⟨c.left.range.index, c.left.range.card_mul_index.symm⟩
  have hr : Nat.card c.right.range ∣ Nat.card G :=
    ⟨c.right.range.index, c.right.range.card_mul_index.symm⟩
  rw [left_card c] at hl
  rw [right_card c] at hr
  have hd := Nat.lcm_dvd hl hr
  norm_num at hd
  exact hd

/-- The given smallness bound leaves nine positive numerical possibilities.
The later geometry is responsible for proving that only the ninth occurs. -/
theorem small_order_alternatives [Finite G] (hsmall : Nat.card G ≤ 25920) :
    ∃ k, 1 ≤ k ∧ k ≤ 9 ∧ Nat.card G = 2880 * k := by
  obtain ⟨k, hk⟩ := order_multiple c
  have hp := Nat.card_pos (α := G)
  exact ⟨k, by omega, by omega, hk⟩

end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo
