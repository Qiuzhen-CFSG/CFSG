module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.FanoPlanes

/-!
# Connectivity of the original point graph

Every generator in G₀ fixes the base point. A generator in G₁ moves it
within the base line, and one in G₂ moves it within the base Fano plane.
Thus every generator sends the base point to a collinear point. D4 and
translation of walks imply that the whole point graph is connected.

Source: the connectivity input in I.5.9, from I.5.3(3), pp.420–422.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] {D : Diagram} (S : DSystem D G)

theorem collinear_reachable {x y : S.Point} (h : S.Collinear x y) :
    S.pointGraph.Reachable x y := by
  by_cases he : x = y
  · rw [he]
  · exact SimpleGraph.Adj.reachable ⟨he, h⟩

theorem pointGraph_reachable_smul (g : G) {x y : S.Point}
    (h : S.pointGraph.Reachable x y) : S.pointGraph.Reachable (g • x) (g • y) :=
  h.map { toFun := (g • ·), map_rel' := fun hx => (S.pointGraph_adj_smul_iff g _ _).mpr hx }

theorem basePoint_reachable_translate (g : G) :
    S.pointGraph.Reachable S.basePoint (g • S.basePoint) := by
  have hg : g ∈ ⨆ i, S.family i := by rw [S.generate]; trivial
  refine Subgroup.iSup_induction S.family (C := fun g =>
    S.pointGraph.Reachable S.basePoint (g • S.basePoint)) hg ?_ ?_ ?_
  · intro i g hg
    apply S.collinear_reachable
    fin_cases i
    · have hf : g • S.basePoint = S.basePoint := by
        apply MulAction.mem_stabilizer_iff.mp
        rwa [S.stabilizer_basePoint]
      rw [hf]
      exact S.collinear_refl _
    · have hf : g • S.baseLine = S.baseLine := by
        apply MulAction.mem_stabilizer_iff.mp
        rwa [S.stabilizer_baseLine]
      have h : S.Inc S.basePoint S.baseLine := ⟨1, rfl, rfl⟩
      exact ⟨S.baseLine, h, by simpa only [hf] using h.smul S g⟩
    · have hf : g • S.basePlane = S.basePlane := by
        apply MulAction.mem_stabilizer_iff.mp
        rwa [S.stabilizer_basePlane]
      have h : S.Inc S.basePoint S.basePlane := ⟨1, rfl, rfl⟩
      exact S.collinear_of_common_plane h (by simpa only [hf] using h.smul S g)
  · simpa only [one_smul] using (SimpleGraph.Reachable.refl (G := S.pointGraph) S.basePoint)
  · intro a b ha hb
    rw [mul_smul]
    exact ha.trans (S.pointGraph_reachable_smul a hb)

theorem pointGraph_connected : S.pointGraph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨S.basePoint, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S.basePoint x
  exact S.basePoint_reachable_translate g

end Quasithin.I5.DSystem
