module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Metric
public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.OrderTwoFour

/-!
# Native binary Ree valences and point-neighbor counts

The actual Suzuki and linear parabolics meet in the Borel of order4096.
Their orders20480 and12288 give valences five and three at every coset vertex.
Together with the native Weyl geometry this constructs the order(2,4) datum;
its point-neighbor sum supplies the intersection numbers used to reconstruct
adjacency from opposition. No graph recurrence or model marking is assumed.

Source: Aschbacher–Smith F.4.6 and J.5.9–12.
-/

public section
namespace ReeF4.Octagon.Binary
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
open SimpleGraph.OctagonShortPaths
open scoped BigOperators

noncomputable section
instance : Finite (CosetGeometry.Vertex family) :=
  Finite.of_equiv _ (CosetGeometry.RankTwo.vertexEquivSum family).symm


abbrev coloring (v : CosetGeometry.Vertex family) : ZMod 2 := if v.type then 1 else 0

theorem coloring_adj {v w : CosetGeometry.Vertex family} (h : (graph family).Adj v w) :
    coloring v+1=coloring w := by
  have hne := h.1
  cases hv : v.type <;> cases hw : w.type <;> simp_all [coloring]
  decide

theorem card_neighbors (v : CosetGeometry.Vertex family) :
    Nat.card ((graph family).neighborSet v)=(if v.type then 3 else 5) := by
  have hb (i : Bool) :
      Nat.card ((graph family).neighborSet (CosetGeometry.base family i)) =
        (if i then 3 else 5) := by
    change Nat.card ((CosetGeometry.RankTwo.graph family).neighborSet _) = _
    rw [CosetGeometry.RankTwo.card_neighbor_base]
    have hc := ((family (!i)).subgroupOf (family i)).card_mul_index
    have hi : Nat.card ((family (!i)).subgroupOf (family i))=4096 := by
      rw [← Subgroup.inf_subgroupOf_right,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
      have he : family (!i) ⊓ family i=Tits.ExceptionalParabolics.FullRee.B := by
        cases i
        · change Tits.ExceptionalParabolics.FullRee.second ⊓
            Tits.ExceptionalParabolics.FullRee.first=Tits.ExceptionalParabolics.FullRee.B
          rw [inf_comm]
          exact Tits.ExceptionalParabolics.FullRee.overlap_eq_borel
        · exact Tits.ExceptionalParabolics.FullRee.overlap_eq_borel
      rw [he,Tits.ExceptionalParabolics.FullRee.borel_card]
    rw [hi] at hc
    cases i
    · change 4096*_ = Nat.card Tits.ExceptionalParabolics.FullRee.first at hc
      rw [Tits.ExceptionalParabolics.FullRee.first_card] at hc
      change _ = 5
      omega
    · change 4096*_ = Nat.card Tits.ExceptionalParabolics.FullRee.second at hc
      rw [Tits.ExceptionalParabolics.FullRee.second_card] at hc
      change _ = 3
      omega
  obtain ⟨g,hg⟩ := CosetGeometry.exists_smul_base family v
  have hh := Nat.card_congr
    ((CosetGeometry.translationGraphIso family g).mapNeighborSet
      (CosetGeometry.base family v.type))
  change Nat.card ((graph family).neighborSet (CosetGeometry.base family v.type)) =
    Nat.card ((graph family).neighborSet (g • CosetGeometry.base family v.type)) at hh
  rw [hg] at hh
  exact hh.symm.trans (hb v.type)

variable [Fintype (CosetGeometry.Vertex family)]

theorem neighborCard_value (v : CosetGeometry.Vertex family) :
    neighborCard (graph family) v=if v.type then 3 else 5 := by
  classical
  have he : neighborCard (graph family) v=Nat.card ((graph family).neighborSet v) := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype ((graph family).Adj v)).symm
  rw [he,card_neighbors]

/-- The actual full binary Ree geometry has order (2,4). -/
@[expose] def orderTwoFour : OrderTwoFourDatum (graph family) where
  color := coloring
  color_adj := fun _ _ h => coloring_adj h
  connected := graph_connected
  cycle_bound := by
    obtain ⟨D⟩ := exists_datum
    exact D.cycle_bound
  diameter := graph_dist_le_eight
  valence := by
    intro v
    rw [neighborCard_value]
    cases hv : v.type <;> simp [coloring,hv]

theorem point_neighbor_sum (u r : CosetGeometry.Vertex family)
    (hu : u.type=false) (hr : r.type=false) (f : ℕ → ℤ) :
    (∑ v, if (graph family).dist u v=2 then f ((graph family).dist v r) else 0) =
      if (graph family).dist u r=0 then 10*f 2 else
      if (graph family).dist u r=8 then 5*f 6+5*f 8 else
      f ((graph family).dist u r-2)+f ((graph family).dist u r)+
        8*f ((graph family).dist u r+2) :=
  orderTwoFour.double_point_sum u r (by simp [orderTwoFour,coloring,hu])
    (by simp [orderTwoFour,coloring,hr]) f

end
end ReeF4.Octagon.Binary
