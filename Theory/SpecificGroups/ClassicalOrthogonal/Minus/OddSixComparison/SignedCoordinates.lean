module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Realization

/-!
# Signed norm coordinates for the odd minus-six descent

Let α satisfy α² + α = ι(a), where a is the original anisotropic-plane
parameter, and let conjugation send α to -1-α. Then z = ι(x)-αι(y)
has norm ι(x²+xy-ay²). Put t = 2α+1. The six coordinates
(a, tc, z, conjugate(z), -t⁻¹d, b) have Pfaffian ab+cd+norm(z).

These signs are essential in odd characteristic. This module fixes the
coordinate convention shared by the geometric realization and image proofs;
it does not assume either existence of α or invariance of the descent space.
Source: the exterior-square realization of twisted A₃/D₃, GLS3 §2.7,
used in Aschbacher–Smith A.2.17, printed pp.38–39.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison
open BenderSuzuki.MatrixGroups Atlas.Order20160A8.Bivectors

variable {F E : Type} [Field F] [Finite F] [Field E]

/-- Concrete bivectors, with the original coefficient embedding and plane parameter. -/
def signedBivectors (ι : F →+* E) (σ : E ≃+* E) (α : E) (v : Space F 2) : Six E :=
  ![ι (v.1 0).1, (2 * α + 1) * ι (v.1 1).1,
    ι v.2.1 - α * ι v.2.2, σ (ι v.2.1 - α * ι v.2.2),
    -((2 * α + 1)⁻¹ * ι (v.1 1).2), ι (v.1 0).2]

/-- The norm identity retains the independently chosen anisotropic parameter. -/
theorem norm_plane_coordinates (ι : F →+* E) (σ : E ≃+* E) (α : E)
    (hι : ∀ c, σ (ι c) = ι c) (hα : α ^ 2 + α = ι (parameter F))
    (hσα : σ α = -1 - α) (x y : F) :
    (ι x - α * ι y) * σ (ι x - α * ι y) = ι (plane F (parameter F) (x, y)) := by
  rw [map_sub, map_mul, hι, hι, hσα]
  simp only [plane_apply, map_sub, map_add, map_pow, map_mul]
  linear_combination -(ι y) ^ 2 * hα

/-- The signed bivectors have precisely the original quadratic values. -/
theorem pfaffian_signedBivectors (ι : F →+* E) (σ : E ≃+* E) (α : E)
    (hι : ∀ c, σ (ι c) = ι c) (hα : α ^ 2 + α = ι (parameter F))
    (hσα : σ α = -1 - α) (ht : 2 * α + 1 ≠ 0) (v : Space F 2) :
    pfaffian (signedBivectors ι σ α v) = ι (quadraticForm F 3 v) := by
  have hn := norm_plane_coordinates ι σ α hι hα hσα v.2.1 v.2.2
  have hp : ((2 * α + 1) * ι (v.1 1).1) *
      -((2 * α + 1)⁻¹ * ι (v.1 1).2) = -(ι (v.1 1).1 * ι (v.1 1).2) := by
    field_simp
  simp only [signedBivectors, pfaffian_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at *
  rw [hp, hn]
  simp [quadraticForm, form_apply, Fin.sum_univ_succ]

variable {J : HermitianForm 4 E}

/-- The concrete chart for an exterior realization. Its construction belongs
to geometry; the independent image theorem may take this chart explicitly. -/
structure SignedCoordinates (R : ExteriorRealization F E J) where
  root : E
  coefficient_fixed : ∀ c, J.conj (R.coefficient c) = R.coefficient c
  root_equation : root ^ 2 + root = R.coefficient (parameter F)
  root_conjugate : J.conj root = -1 - root
  skew_ne_zero : 2 * root + 1 ≠ 0
  coordinates_eq : ∀ v, R.coordinates v = signedBivectors R.coefficient J.conj root v

end ClassicalOrthogonal.Minus.OddSixComparison
