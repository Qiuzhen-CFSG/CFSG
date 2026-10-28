module

public import Theory.Representation.BinaryParabolicExteriorSquare.PlaneSpan
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# An odd-order actor generating the exterior plane hyperplane

The order-three rotation of the first natural plane sends the three-space
01,02,03 to a complementary three-space inside the hyperplane with last
coordinate zero. Their sum is that five-space. Unlike the two opposite
Levi transvections, this cubic belongs to the plane parabolic's two-residual.
The source adapter lifts it through the actual parabolic image.

Source: Aschbacher–Smith, 13.8.30, printed p.964. The exterior coordinates
use the existing attributed ATLAS model.
-/

@[expose] public section
open Atlas.Order20160A8.Bivectors
namespace Representation.BinaryParabolicExteriorSquare.PlaneSpan

def planeCubic : Matrix (Fin 4) (Fin 4) Bit :=
  !![0,1,0,0; 1,1,0,0; 0,0,1,0; 0,0,0,1]

theorem planeCubic_cube : planeCubic ^ 3 = 1 := by decide

theorem exterior_planeCubic (x : Six) :
    exteriorMap planeCubic x = ![x 0,x 3,x 4,x 1+x 3,x 2+x 4,x 5] := by
  ext t
  fin_cases t <;>
    simp [exteriorMap, compound, first, second, planeCubic,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem planeSpace_le_of_cubic (P : Submodule Bit Six) (hfirst : firstSpace ≤ P)
    (hcubic : ∀ x ∈ P, exteriorMap planeCubic x ∈ P) : planeSpace ≤ P := by
  intro x hx
  change x 5 = 0 at hx
  let u : Six := ![x 0,x 1,x 2,0,0,0]
  let v : Six := ![0,x 3,x 4,0,0,0]
  have hu : u ∈ P := hfirst (by change _ ∧ _ ∧ _; simp [u])
  have hv : v ∈ P := hfirst (by change _ ∧ _ ∧ _; simp [v])
  have he : x = u + exteriorMap planeCubic v := by
    rw [exterior_planeCubic]
    ext i
    fin_cases i <;> simp [u,v,hx]
  rw [he]
  exact P.add_mem hu (hcubic v hv)
end Representation.BinaryParabolicExteriorSquare.PlaneSpan
