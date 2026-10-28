module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Alternating bivector matrices, orbit separation, and support

The coefficient matrix of a bivector is symmetric with zero diagonal over F₂.
The proved minor formula identifies the exterior action with congruence
B(gv) = g B(v) gᵀ. We prove the polynomial identity once for arbitrary matrix
entries, then reconstruct the matrix from its upper triangle. This avoids
repeating a large exterior-power calculation at every entry.

Consequently rank and support transform intrinsically. The two source vectors
have ranks two and four, so their orbits are disjoint. The support of the second
vector is exactly Γ₄, forcing its stabilizer into the four-space parabolic.
The normal-form existence and symplectic quotient are separate obligations.

Source: Aschbacher–Smith, 12.5.5(2–3), printed p.819/PDF p.836.
-/

@[expose] public section

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
open scoped Matrix

/-- The alternating coefficient matrix of a binary bivector. -/
def alternatingMatrix (c : Coordinates) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of ![![0, c 0, c 1, c 2, c 3],
    ![c 0, 0, c 4, c 5, c 6],
    ![c 1, c 4, 0, c 7, c 8],
    ![c 2, c 5, c 7, 0, c 9],
    ![c 3, c 6, c 8, c 9, 0]]

/-- The alternating matrix of a bivector, with its natural covariant action. -/
noncomputable def bivectorMatrix (v : V) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  alternatingMatrix (coordinates v)

private theorem matrix_congruence_entry (M : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (c : Coordinates) (i j : Fin 5) :
    (M * alternatingMatrix c * M.transpose) i j =
      ∑ t, (M i (pair t 0) * M j (pair t 1) -
        M j (pair t 0) * M i (pair t 1)) * c t := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp [alternatingMatrix, Matrix.of_apply, Fin.sum_univ_succ, pair,
    sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  ring

theorem alternatingMatrix_transpose (c : Coordinates) :
    (alternatingMatrix c).transpose = alternatingMatrix c := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem alternatingMatrix_diagonal (c : Coordinates) (i : Fin 5) :
    alternatingMatrix c i i = 0 := by
  fin_cases i <;> rfl

private theorem alternatingMatrix_reconstruct (A : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (hd : ∀ i, A i i = 0) (hs : ∀ i j, A i j = A j i) :
    alternatingMatrix (fun t => A (pair t 0) (pair t 1)) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact (hd _).symm | exact hs _ _

private theorem alternatingMatrix_minor_action (g : Group) (c : Coordinates) :
    alternatingMatrix ((actionMatrix g).mulVec c) =
      g.val * alternatingMatrix c * g.val.transpose := by
  have hc : (actionMatrix g).mulVec c = fun t =>
      (g.val * alternatingMatrix c * g.val.transpose) (pair t 0) (pair t 1) := by
    funext t
    rw [matrix_congruence_entry]
    rfl
  rw [hc]
  apply alternatingMatrix_reconstruct
  · intro i
    rw [matrix_congruence_entry]
    simp
  · intro i j
    have hs : (g.val * alternatingMatrix c * g.val.transpose).transpose =
        g.val * alternatingMatrix c * g.val.transpose := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
        alternatingMatrix_transpose, Matrix.mul_assoc]
    exact congrArg (fun A => A j i) hs

/-- This is a congruence action on alternating bivectors, not similarity. -/
theorem bivectorMatrix_action (g : Group) (v : V) :
    bivectorMatrix (exteriorAction 2 g v) = g.val * bivectorMatrix v * g.val.transpose := by
  unfold bivectorMatrix
  rw [coordinates_action]
  exact alternatingMatrix_minor_action g (coordinates v)

theorem bivectorMatrix_injective : Function.Injective bivectorMatrix := by
  intro v w h
  apply coordinates.injective
  ext i
  fin_cases i
  · exact congrArg (fun M => M 0 1) h
  · exact congrArg (fun M => M 0 2) h
  · exact congrArg (fun M => M 0 3) h
  · exact congrArg (fun M => M 0 4) h
  · exact congrArg (fun M => M 1 2) h
  · exact congrArg (fun M => M 1 3) h
  · exact congrArg (fun M => M 1 4) h
  · exact congrArg (fun M => M 2 3) h
  · exact congrArg (fun M => M 2 4) h
  · exact congrArg (fun M => M 3 4) h

theorem rank_bivectorMatrix_action (g : Group) (v : V) :
    (bivectorMatrix (exteriorAction 2 g v)).rank = (bivectorMatrix v).rank := by
  rw [bivectorMatrix_action, Matrix.rank_mul_eq_left_of_isUnit_det,
    Matrix.rank_mul_eq_right_of_isUnit_det]
  · rw [g.property]
    exact isUnit_one
  · rw [Matrix.det_transpose, g.property]
    exact isUnit_one


private theorem bivector_decomposable_apply (v : Fin 5 → ZMod 2) :
    (bivectorMatrix decomposable).mulVec v = ![v 1, v 0, 0, 0, 0] := by
  rw [bivectorMatrix, coordinates_decomposable]
  ext i
  fin_cases i <;> simp [alternatingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem bivector_nondecomposable_apply (v : Fin 5 → ZMod 2) :
    (bivectorMatrix nondecomposable).mulVec v = ![v 1, v 0, v 3, v 2, 0] := by
  rw [bivectorMatrix, coordinates_nondecomposable]
  ext i
  fin_cases i <;> simp [alternatingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The support of e₁∧e₂ is the standard two-space. -/
theorem range_bivectorMatrix_decomposable :
    LinearMap.range (bivectorMatrix decomposable).mulVecLin = naturalFlag 2 := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    change ∀ i : Fin 5, 2 ≤ i.val → (bivectorMatrix decomposable).mulVec v i = 0
    rw [bivector_decomposable_apply]
    intro i hi
    fin_cases i <;> simp_all
  · intro x hx
    change ∀ i : Fin 5, 2 ≤ i.val → x i = 0 at hx
    refine ⟨![x 1, x 0, 0, 0, 0], ?_⟩
    change (bivectorMatrix decomposable).mulVec _ = _
    rw [bivector_decomposable_apply]
    ext i
    fin_cases i <;> simp [hx 2 (by decide), hx 3 (by decide), hx 4 (by decide)]

/-- The support of e₁∧e₂ + e₃∧e₄ is the exact source four-space Γ₄. -/
theorem range_bivectorMatrix_nondecomposable :
    LinearMap.range (bivectorMatrix nondecomposable).mulVecLin = naturalFlag 4 := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    change ∀ i : Fin 5, 4 ≤ i.val → (bivectorMatrix nondecomposable).mulVec v i = 0
    rw [bivector_nondecomposable_apply]
    intro i hi
    fin_cases i <;> simp_all
  · intro x hx
    change ∀ i : Fin 5, 4 ≤ i.val → x i = 0 at hx
    refine ⟨![x 1, x 0, x 3, x 2, 0], ?_⟩
    change (bivectorMatrix nondecomposable).mulVec _ = _
    rw [bivector_nondecomposable_apply]
    ext i
    fin_cases i <;> simp [hx 4 (by decide)]

theorem rank_bivectorMatrix_decomposable : (bivectorMatrix decomposable).rank = 2 := by
  rw [Matrix.rank, range_bivectorMatrix_decomposable]
  exact finrank_naturalFlag 2 (by decide)

theorem rank_bivectorMatrix_nondecomposable : (bivectorMatrix nondecomposable).rank = 4 := by
  rw [Matrix.rank, range_bivectorMatrix_nondecomposable]
  exact finrank_naturalFlag 4 (by decide)

/-- The two displayed source points cannot lie in one orbit. -/
theorem not_inExteriorOrbit_decomposable_nondecomposable :
    ¬ InExteriorOrbit decomposable nondecomposable := by
  rintro ⟨g, hg⟩
  have h := rank_bivectorMatrix_action g decomposable
  rw [hg, rank_bivectorMatrix_nondecomposable, rank_bivectorMatrix_decomposable] at h
  omega

/-- Orbit uniqueness, independent of the remaining normal-form existence proof. -/
theorem exterior_orbits_disjoint (v : V) :
    ¬ (InExteriorOrbit decomposable v ∧ InExteriorOrbit nondecomposable v) := by
  rintro ⟨h₁, h₂⟩
  exact not_inExteriorOrbit_decomposable_nondecomposable (h₁.trans h₂.symm)


/-- The support of a bivector transforms by the actual natural action. -/
theorem range_bivectorMatrix_action (g : Group) (v : V) :
    LinearMap.range (bivectorMatrix (exteriorAction 2 g v)).mulVecLin =
      (LinearMap.range (bivectorMatrix v).mulVecLin).map (specialLinearNatural 5 g) := by
  have hu : IsUnit g.val.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [Matrix.det_transpose, g.property]
    exact isUnit_one)
  have hr : LinearMap.range g.val.transpose.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr hu)
  rw [bivectorMatrix_action, Matrix.mulVecLin_mul,
    LinearMap.range_comp_of_range_eq_top _ hr, Matrix.mulVecLin_mul,
    LinearMap.range_comp]
  rfl

/-- Fixing the second source point forces stabilization of Γ₄, the support on
which the symplectic quotient acts. -/
theorem nondecomposableStabilizer_le_parabolic_four :
    nondecomposableStabilizer ≤ parabolic 4 := by
  intro g hg
  have hfix : exteriorAction 2 g nondecomposable = nondecomposable := hg
  have hm : (naturalFlag 4).map (specialLinearNatural 5 g) = naturalFlag 4 := by
    rw [← range_bivectorMatrix_nondecomposable, ← range_bivectorMatrix_action, hfix]
  change ∀ v, specialLinearNatural 5 g v ∈ naturalFlag 4 ↔ v ∈ naturalFlag 4
  intro v
  constructor
  · intro hv
    rw [← hm] at hv
    obtain ⟨w, hw, he⟩ := hv
    have h : w = v := (Matrix.SpecialLinearGroup.toLin' g).injective he
    exact h ▸ hw
  · intro hv
    rw [← hm]
    exact ⟨v, hv, rfl⟩

end Representation.SL5ExteriorSquare
