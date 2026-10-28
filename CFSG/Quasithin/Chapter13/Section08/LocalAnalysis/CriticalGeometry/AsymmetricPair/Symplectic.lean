module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# The strict displacement in the cover argument

An isometry of an alternating form whose displacement is contained in a
nonradical line fixes the line's orthogonal hyperplane pointwise. Thus an
actor nontrivial on that hyperplane has displacement outside the line.
This gives the strictness step in the unipotent-radical paragraph of
Aschbacher–Smith 13.8.7, printed p.949. Applying it requires the actual
invariant form on V^g and the identification of V₃^g with the orthogonal
hyperplane; it does not infer those facts from a group-family name.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W]

/-- A symplectic line displacement fixes the orthogonal hyperplane. -/
theorem fixes_orthogonal_of_displacement_line
    (B : LinearMap.BilinForm k W) (hB : B.IsAlt) (z : W)
    (hn : ∃ y, B z y ≠ 0) (e : W ≃ₗ[k] W)
    (he : ∀ x y, B (e x) (e y) = B x y)
    (hd : ∀ x, e x - x ∈ Submodule.span k {z}) :
    ∀ x, B z x = 0 → e x = x := by
  obtain ⟨y, hy⟩ := hn
  intro x hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hd x)
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hd y)
  have hx' : B x z = 0 := hB.eq_iff.mp hx
  have hex : e x = x + a • z := by rw [ha]; abel
  have hey : e y = y + b • z := by rw [hb]; abel
  have hp := he x y
  rw [hex, hey] at hp
  have hp' : B x y + a * B z y = B x y := by
    simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hx', hB.self_eq_zero z, mul_zero, add_zero] using hp
  have hm : a * B z y = 0 := by
    apply add_left_cancel (a := B x y)
    simpa only [add_zero] using hp'
  have ha0 : a = 0 := (mul_eq_zero.mp hm).resolve_right hy
  simpa only [ha0, zero_smul, add_zero] using hex

/-- Moving an orthogonal vector forces displacement outside the center line. -/
theorem displacement_not_le_line_of_moves_orthogonal
    (B : LinearMap.BilinForm k W) (hB : B.IsAlt) (z : W)
    (hn : ∃ y, B z y ≠ 0) (e : W ≃ₗ[k] W)
    (he : ∀ x y, B (e x) (e y) = B x y)
    (hm : ∃ x, B z x = 0 ∧ e x ≠ x) :
    ¬ LinearMap.range (e.toLinearMap - LinearMap.id) ≤ Submodule.span k {z} := by
  intro hle
  obtain ⟨x, hx, hne⟩ := hm
  apply hne
  apply fixes_orthogonal_of_displacement_line B hB z hn e he _ x hx
  intro w
  exact hle ⟨w, rfl⟩

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
end
