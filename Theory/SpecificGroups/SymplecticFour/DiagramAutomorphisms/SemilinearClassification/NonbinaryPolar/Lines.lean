module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.ProjectiveAction
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.FixedRadical

/-!
# Recovering projective lines from symplectic orthogonality

The double perpendicular of a vector subspace is itself for the actual
nondegenerate alternating form. Applying this to the span of two projective
points recovers every projective line from the polar relation, including the
nonisotropic lines. Thus every polar permutation is a collineation of the
whole projective three-space.

This is the line-recovery step in the geometric proof of the symplectic
automorphism fact used in Aschbacher--Smith F.1.12, printed pp.263--264 of
`refs/quasithin.pdf`. It does not assume a semilinear lift of a collineation.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
open Projectivization
variable {F : Type*} [Field F]

private theorem orthogonal_mk_right_iff (p : ProjectivePoint F)
    (v : Vector F) (hv : v ≠ 0) :
    Orthogonal p (mk F v hv) ↔ v ∈ (form F).orthogonal p.submodule := by
  constructor
  · intro h x hx
    exact h x hx v (Submodule.mem_span_singleton_self v)
  · intro h x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [map_smul, h x hx]

/-- Every projective line, including a nonisotropic line, is recovered from
its common perpendicular points. -/
theorem projective_le_sup_iff_double_orthogonal (p q r : ProjectivePoint F) :
    r.submodule ≤ p.submodule ⊔ q.submodule ↔
      ∀ s, Orthogonal p s → Orthogonal q s → Orthogonal r s := by
  constructor
  · intro h s hp hq x hx y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp (h hx)
    simp [map_add, hp u hu y hy, hq v hv y hy]
  · intro h
    have hr : r.submodule ≤ (form F).orthogonal
        ((form F).orthogonal (p.submodule ⊔ q.submodule)) := by
      intro x hx y hy
      by_cases hy0 : y = 0
      · simp [hy0]
      have hp : Orthogonal p (mk F y hy0) :=
        (orthogonal_mk_right_iff p y hy0).mpr (fun z hz =>
          hy z ((le_sup_left : p.submodule ≤ p.submodule ⊔ q.submodule) hz))
      have hq : Orthogonal q (mk F y hy0) :=
        (orthogonal_mk_right_iff q y hy0).mpr (fun z hz =>
          hy z ((le_sup_right : q.submodule ≤ p.submodule ⊔ q.submodule) hz))
      exact TwoLocalCover.form_alternating.eq_iff.mp
        (h (mk F y hy0) hp hq x hx y (Submodule.mem_span_singleton_self y))
    rwa [LinearMap.BilinForm.orthogonal_orthogonal
      TwoLocalCover.form_nondegenerate TwoLocalCover.form_alternating.isRefl] at hr

/-- A polar permutation preserves all projective lines, not only the totally
isotropic ones that define the polar incidence geometry. -/
theorem polar_permutation_preserves_projective_lines
    (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ p q, Orthogonal (φ p) (φ q) ↔ Orthogonal p q)
    (p q r : ProjectivePoint F) :
    (φ r).submodule ≤ (φ p).submodule ⊔ (φ q).submodule ↔
      r.submodule ≤ p.submodule ⊔ q.submodule := by
  simp only [projective_le_sup_iff_double_orthogonal]
  constructor
  · intro h s hp hq
    exact (hφ r s).mp (h (φ s) ((hφ p s).mpr hp) ((hφ q s).mpr hq))
  · intro h s hp hq
    obtain ⟨t, rfl⟩ := φ.surjective s
    exact (hφ r t).mpr (h t ((hφ p t).mp hp) ((hφ q t).mp hq))
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
