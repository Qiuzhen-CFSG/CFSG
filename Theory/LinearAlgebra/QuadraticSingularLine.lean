module
public import Theory.LinearAlgebra.QuadraticRankOneDisplacement
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
/-!
# Isometries with singular-line displacement

An isometry with displacement in a nonzero singular line is the identity:
the rank-one displacement theorem excludes every nonzero vector in that
range. If an isometry fixes the perpendicular to a singular point,
nondegenerate polarization puts its displacement in the same point line.

These results retain the quadratic form and its actual polar perpendicular.
They supply the commutator lifting and centralizer comparison in
Aschbacher--Smith, 12.6.24(6--7), printed pp.830--831.
-/

public section
namespace QuadraticForm
open Module
variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [Module.Finite F W]

/-- A singular line contains no nonzero displacement of an isometry. -/
theorem eq_one_of_displacement_le_singular_line (q : QuadraticForm F W)
    (hq : q.polarBilin.Nondegenerate) (t : W ≃ₗ[F] W) (ht : ∀ x, q (t x)=q x)
    (z : W) (hz : z ≠ 0) (hs : q z=0)
    (hd : (t.toLinearMap - LinearMap.id).range ≤ Submodule.span F {z}) : t=1 := by
  have hr : finrank F (t.toLinearMap - LinearMap.id).range ≤ 1 := by
    have hh := Submodule.finrank_mono hd
    rwa [finrank_span_singleton hz] at hh
  ext w
  change t w=w
  apply sub_eq_zero.mp
  by_contra hn
  have hw : t w-w ∈ (t.toLinearMap - LinearMap.id).range := ⟨w,rfl⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hd hw)
  have hs' : q (t w-w)=0 := by rw [←hc,q.map_smul,hs,smul_zero]
  exact q.singular_not_mem_displacement hq.1 t ht hr _ hn hs' hw

/-- Fixing a singular point perpendicular pointwise forces an isometry to be trivial. -/
theorem eq_one_of_fixed_singular_perpendicular (q : QuadraticForm F W)
    (hq : q.polarBilin.Nondegenerate) (t : W ≃ₗ[F] W) (ht : ∀ x, q (t x)=q x)
    (z : W) (hz : z ≠ 0) (hs : q z=0)
    (hf : ∀ x, q.polarBilin z x=0 → t x=x) : t=1 := by
  have hsym : q.polarBilin.IsRefl := by
    intro x y hh
    change QuadraticMap.polar q y x=0
    rw [QuadraticMap.polar_comm]
    exact hh
  have hi (x y : W) : q.polarBilin (t x) (t y)=q.polarBilin x y := by
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,←map_add,ht]
  apply q.eq_one_of_displacement_le_singular_line hq t ht z hz hs
  rintro _ ⟨w,rfl⟩
  rw [←LinearMap.BilinForm.orthogonal_orthogonal hq hsym (Submodule.span F {z})]
  intro x hx
  have hx0 : q.polarBilin z x=0 := hx z (Submodule.mem_span_singleton_self z)
  change q.polarBilin x (t w-w)=0
  rw [map_sub,sub_eq_zero]
  calc
    q.polarBilin x (t w)=q.polarBilin (t x) (t w) := by rw [hf x hx0]
    _ = q.polarBilin x w := hi x w
end QuadraticForm
