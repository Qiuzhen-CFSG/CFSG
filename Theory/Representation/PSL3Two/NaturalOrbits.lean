module

public import Theory.Representation.PSL3Two.SmallModules
public import Mathlib.LinearAlgebra.Determinant

/-!
# Transitivity of the natural binary SL₃ action

An isomorphism between two nonzero one-dimensional subspaces extends to a
linear automorphism. Its determinant is one because the only nonzero binary
scalar is one. The resulting matrix acts by the literal natural representation.

This supplies the natural-module fusion step in Aschbacher–Smith, J.2.6(4),
printed p.434 (PDF p.445 of `refs/quasithin.pdf`).
-/

public section
noncomputable section
namespace BinaryLinearThree

/-- The natural SL₃(2) action is transitive on its seven nonzero vectors. -/
theorem natural_transitive_nonzero (u v : BinaryLinearThree.Vector) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : BinaryLinearThree.Group, BinaryLinearThree.W g u = v := by
  let eu := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) BinaryLinearThree.Vector u hu
  let ev := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) BinaryLinearThree.Vector v hv
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (eu.symm.trans ev)
  have hgu : g u = v := by
    have h := hg (eu 1)
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
    simpa [eu, ev] using h.symm
  have hdet : (LinearMap.toMatrix' g.toLinearMap).det = 1 := by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ g.isUnit_det'.ne_zero
  refine ⟨⟨LinearMap.toMatrix' g.toLinearMap, hdet⟩, ?_⟩
  change Matrix.toLin' (LinearMap.toMatrix' g.toLinearMap) u = v
  rw [Matrix.toLin'_toMatrix']
  exact hgu



end BinaryLinearThree
