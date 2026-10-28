module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.NonsingularCounting

/-!
# Nonsingular one-or-all triples in the original C₃ geometry

A double-perp point distinct from an endpoint cannot be collinear with it.
Otherwise every line through the endpoint would be coplanar with their
joining line: its unique common neighbor with the other endpoint forms a
collinear triangle. This contradicts the eight noncoplanar lines in the
local quadrangle. Apply this to the third point produced by the actual
neighbor kernel. The 63-point count then gives the one-or-all rule.

This proves the conclusion of I.5.13–14 directly from the I.5.9 geometry
and the original D5 kernel obstruction, retaining all source subgroups.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup Theory.LinearAlgebra
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem doublePerp_noncollinear_left (d : S.LocalPolarFacts) {x y z : S.Point}
    (hxy : ¬ S.Collinear x y) (hz : z ∈ S.DoublePerp x y) (hxz : x ≠ z) :
    ¬ S.Collinear x z := by
  rintro ⟨l, hxl, hzl⟩
  have hn : Nonempty {m : S.Line // S.Inc x m ∧ ¬ S.CoplanarLines l m} :=
    (Nat.card_pos_iff.mp (by rw [d.noncoplanar_card x l hxl]; decide)).1
  obtain ⟨⟨m, hxm, hlm⟩⟩ := hn
  obtain ⟨u, ⟨hum, hyu⟩, _⟩ := S.unique_collinear_point_on_line d hxy hxm
  have hxu : x ≠ u := fun h => hxy (h.symm ▸ S.collinear_symm hyu)
  have hzu : S.Collinear z u := hz u ⟨m, hxm, hum⟩ hyu
  exact hlm ((S.collinear_iff_coplanar_at_middle d hxz hxu hxl hzl hxm hum).mp hzu)

theorem nonsingular_one_or_all (d : S.LocalPolarFacts) {x y : S.Point}
    (hxy : ¬ S.Collinear x y) :
    ∃ z : S.Point, BinaryPolarGeometry.OneOrAll S.Collinear x y z := by
  obtain ⟨z, hzx, hzy, hz⟩ := S.doublePerp_third d hxy
  have hxz := S.doublePerp_noncollinear_left d hxy hz hzx.symm
  have hyz := S.doublePerp_noncollinear_left d
    (fun h => hxy (S.collinear_symm h))
    (show z ∈ S.DoublePerp y x from fun u hu hv => hz u hv hu) hzy.symm
  exact ⟨z, S.one_or_all_of_doublePerp d hxy hxz hyz hz⟩

theorem source_one_or_all_triples (d : S.LocalPolarFacts) (x y : S.Point) (hxy : x ≠ y) :
    ∃ z : S.Point, BinaryPolarGeometry.OneOrAll S.Collinear x y z := by
  by_cases hc : S.Collinear x y
  · exact S.singular_one_or_all d hxy hc
  · exact S.nonsingular_one_or_all d hc

end Quasithin.I5.DSystem
