module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.NeighborKernelOrbit

/-!
# A third original point in each nonsingular double-perp set

A nonidentity neighbor-kernel element fixes every common neighbor of the
base point and a distant point, but some such element moves that distant
point. Its image is a third point collinear with all their common
neighbors. Point transitivity gives the same conclusion for every original
noncollinear pair. This discharges the group-theoretic content of I.5.13;
the local quadrangle bounds this double-perp set by three.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

def DoublePerp (x y : S.Point) : Set S.Point :=
  {z | ∀ u : S.Point, S.Collinear x u → S.Collinear y u → S.Collinear z u}

theorem left_mem_doublePerp (x y : S.Point) : x ∈ S.DoublePerp x y := fun _ hx _ => hx

theorem right_mem_doublePerp (x y : S.Point) : y ∈ S.DoublePerp x y := fun _ _ hy => hy

theorem doublePerp_smul {x y z : S.Point} (g : G) (hz : z ∈ S.DoublePerp x y) :
    g • z ∈ S.DoublePerp (g • x) (g • y) := by
  intro u hxu hyu
  have hxi : S.Collinear x (g⁻¹ • u) := by simpa only [inv_smul_smul] using hxu.smul S g⁻¹
  have hyi : S.Collinear y (g⁻¹ • u) := by simpa only [inv_smul_smul] using hyu.smul S g⁻¹
  simpa only [smul_inv_smul] using (hz _ hxi hyi).smul S g

theorem base_doublePerp_third (d : S.LocalPolarFacts) {y : S.Point}
    (hxy : ¬ S.Collinear S.basePoint y) :
    ∃ z : S.Point, z ≠ S.basePoint ∧ z ≠ y ∧ z ∈ S.DoublePerp S.basePoint y := by
  obtain ⟨g, hg, hgy⟩ := S.neighborCore_moves_distant d hxy
  have hgx := S.point_core_fixes_basePoint hg.1
  refine ⟨g • y, ?_, hgy, ?_⟩
  · intro h
    have hyx : y = S.basePoint := (MulAction.injective g) (h.trans hgx.symm)
    exact hxy (hyx ▸ S.collinear_refl S.basePoint)
  · intro u hxu hyu
    have hgu := S.neighborCore_fixes hg hxu
    simpa only [hgu] using hyu.smul S g

theorem doublePerp_third (d : S.LocalPolarFacts) {x y : S.Point}
    (hxy : ¬ S.Collinear x y) :
    ∃ z : S.Point, z ≠ x ∧ z ≠ y ∧ z ∈ S.DoublePerp x y := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S.basePoint x
  have hi : ¬ S.Collinear S.basePoint (g⁻¹ • y) := fun h => hxy (by
    simpa only [hg, smul_inv_smul] using h.smul S g)
  obtain ⟨z, hzx, hzy, hz⟩ := S.base_doublePerp_third d hi
  refine ⟨g • z, ?_, ?_, ?_⟩
  · exact fun h => hzx ((MulAction.injective g) (h.trans hg.symm))
  · intro h
    exact hzy (by simpa only [inv_smul_smul] using congrArg (g⁻¹ • ·) h)
  · simpa only [hg, smul_inv_smul] using S.doublePerp_smul g hz

end Quasithin.I5.DSystem
