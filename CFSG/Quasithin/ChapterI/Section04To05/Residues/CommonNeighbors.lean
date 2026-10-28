module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PointCount

/-!
# The common-neighbor quadrangle on the original points

For two noncollinear points, each line through the first contains exactly
one common neighbor. This gives an actual bijection from their common
neighbors to the first point's fifteen incident lines. Collinearity of
common neighbors is exactly coplanarity in that point residue. Thus the
marked local polar model transfers directly, without replacing the original
point action or choosing a new global geometry.

Source: I.5.11, printed p.423.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

def CommonNeighbors (x z : S.Point) := {y : S.Point // S.Collinear x y ∧ S.Collinear z y}

def commonNeighborLineEquiv (d : S.LocalPolarFacts) {x z : S.Point}
    (hxz : ¬ S.Collinear x z) : S.CommonNeighbors x z ≃ {l : S.Line // S.Inc x l} := by
  let f : S.CommonNeighbors x z → {l : S.Line // S.Inc x l} := fun y =>
    ⟨y.property.1.choose, y.property.1.choose_spec.1⟩
  apply Equiv.ofBijective f
  constructor
  · intro y v h
    have hline : y.property.1.choose = v.property.1.choose := congrArg Subtype.val h
    obtain ⟨u, _, hu⟩ := S.unique_collinear_point_on_line d hxz y.property.1.choose_spec.1
    apply Subtype.ext
    exact (hu y.val ⟨y.property.1.choose_spec.2, y.property.2⟩).trans
      (hu v.val ⟨hline.symm ▸ v.property.1.choose_spec.2, v.property.2⟩).symm
  · rintro ⟨l, hxl⟩
    obtain ⟨y, ⟨hyl, hzy⟩, _⟩ := S.unique_collinear_point_on_line d hxz hxl
    let v : S.CommonNeighbors x z := ⟨y, ⟨l, hxl, hyl⟩, hzy⟩
    refine ⟨v, Subtype.ext ?_⟩
    exact S.unique_line (show x ≠ y from fun h => hxz (h.symm ▸ S.collinear_symm hzy))
      v.property.1.choose_spec.1 v.property.1.choose_spec.2 hxl hyl

theorem commonNeighborLineEquiv_inc (d : S.LocalPolarFacts) {x z : S.Point}
    (hxz : ¬ S.Collinear x z) (y : S.CommonNeighbors x z) :
    S.Inc y.val (S.commonNeighborLineEquiv d hxz y).val :=
  y.property.1.choose_spec.2

theorem commonNeighborLineEquiv_collinear (d : S.LocalPolarFacts) {x z : S.Point}
    (hxz : ¬ S.Collinear x z) (y v : S.CommonNeighbors x z) :
    S.Collinear y.val v.val ↔ S.CoplanarLines
      (S.commonNeighborLineEquiv d hxz y).val (S.commonNeighborLineEquiv d hxz v).val := by
  exact S.collinear_iff_coplanar_at_middle d
    (show x ≠ y.val from fun h => hxz (h.symm ▸ S.collinear_symm y.property.2))
    (show x ≠ v.val from fun h => hxz (h.symm ▸ S.collinear_symm v.property.2))
    (S.commonNeighborLineEquiv d hxz y).property (S.commonNeighborLineEquiv_inc d hxz y)
    (S.commonNeighborLineEquiv d hxz v).property (S.commonNeighborLineEquiv_inc d hxz v)

theorem commonNeighbors_card (d : S.LocalPolarFacts) {x z : S.Point}
    (hxz : ¬ S.Collinear x z) : Nat.card (S.CommonNeighbors x z) = 15 := by
  rw [Nat.card_congr (S.commonNeighborLineEquiv d hxz), S.c3_point_lines_card]

theorem distant_points_transitive (d : S.LocalPolarFacts) {x z w : S.Point}
    (hxz : ¬ S.Collinear x z) (hxw : ¬ S.Collinear x w) :
    ∃ g : G, g • x = x ∧ g • z = w := by
  let l : {l : S.Line // S.Inc x l} :=
    (S.twoLinePathFlagsEquiv x).symm (Classical.choice (S.exists_twoLinePath x)) |>.1
  let p := (S.twoLinePathEndpointLineEquiv d x).symm (⟨z, hxz⟩, l)
  let q := (S.twoLinePathEndpointLineEquiv d x).symm (⟨w, hxw⟩, l)
  have hp : p.endpoint = z := congrArg (fun a => a.1.val)
    ((S.twoLinePathEndpointLineEquiv d x).apply_symm_apply (⟨z, hxz⟩, l))
  have hq : q.endpoint = w := congrArg (fun a => a.1.val)
    ((S.twoLinePathEndpointLineEquiv d x).apply_symm_apply (⟨w, hxw⟩, l))
  obtain ⟨g, hgx, _, hge, _, _⟩ := S.twoLinePaths_transitive d.transporter p q
  exact ⟨g, hgx, by simpa only [hp, hq] using hge⟩

end Quasithin.I5.DSystem
