module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.TrivialTwoCore.NormalizerAction.Coordinates
public import Theory.AtlasPort.ExceptionalIsomorphisms.NineCoordinates

/-!
# Commuting symplectic maps as determinant-one matrices over nine elements

Commutation with `J` gives linearity over the coordinate field. The real part
of the extension-field determinant is the symplectic form; its imaginary part
is the negative of the form after applying `J` in the first argument. A
commuting symplectic map therefore preserves the entire determinant. Taking
its matrix gives an actual element of `SL₂(9)` with the same vector action.

The field model is the ATLAS quadratic-coordinate port, attributed in
`Coordinates`; this comparison is proved directly for the project's matrix
carrier. Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4/482 of `refs/quasithin.pdf`.
-/

@[expose] public section

noncomputable section
open Matrix
open scoped MatrixGroups
namespace Matrix.PSp4Three.TrivialTwoCore.NormalizerAction
open Atlas.Comparisons.Exceptional

/-- The alternating determinant over the extension field. -/
def wedge (u v : W) : Nine.F := u 0 * v 1 - u 1 * v 0

theorem wedge_coordinates_re (x y : V) :
    (wedge (coordinates x) (coordinates y)).re = form x y :=
  (coordinates_form x y).symm

theorem wedge_coordinates_im (x y : V) :
    (wedge (coordinates x) (coordinates y)).im = -form (quadraticOperator x) y := by
  simp [wedge, coordinates, form_apply, Fin.sum_univ_two, quadraticOperator]
  ring

theorem commuting_transport_omega (g : Sp 2 (ZMod 3))
    (hg : ∀ x : V, g • quadraticOperator x = quadraticOperator (g • x)) (w : W) :
    transport g (Nine.omega • w) = Nine.omega • transport g w := by
  have hJ : coordinates.symm (Nine.omega • w) = quadraticOperator (coordinates.symm w) := by
    apply coordinates.injective
    simp [coordinates_quadraticOperator]
  simp only [transport_apply, hJ, hg, coordinates_quadraticOperator]

/-- Commutation with the quadratic operator supplies linearity over the actual field. -/
def commutingLinear (g : Sp 2 (ZMod 3))
    (hg : ∀ x : V, g • quadraticOperator x = quadraticOperator (g • x)) : W →ₗ[Nine.F] W where
  toFun := transport g
  map_add' := (transport g).map_add
  map_smul' a w := by
    change transport g (a • w) = a • transport g w
    calc
      _ = a.re • transport g w + a.im • (Nine.omega • transport g w) := by
        rw [scalar_decomposition a w, map_add, map_smul, map_smul,
          commuting_transport_omega g hg]
      _ = _ := (scalar_decomposition a (transport g w)).symm

theorem commuting_wedge (g : Sp 2 (ZMod 3))
    (hg : ∀ x : V, g • quadraticOperator x = quadraticOperator (g • x)) (u v : W) :
    wedge (transport g u) (transport g v) = wedge u v := by
  obtain ⟨x, rfl⟩ := coordinates.surjective u
  obtain ⟨y, rfl⟩ := coordinates.surjective v
  simp only [transport_apply, coordinates.symm_apply_apply]
  apply QuadraticAlgebra.ext
  · simp only [wedge_coordinates_re]
    exact preserves g x y
  · simp only [wedge_coordinates_im]
    rw [← hg]
    exact congrArg Neg.neg (preserves g (quadraticOperator x) y)

/-- Every commuting symplectic matrix is represented by an actual determinant-one
matrix over the nine-element coordinate field. -/
theorem exists_commuting_matrix (g : Sp 2 (ZMod 3))
    (hg : ∀ x : V, g • quadraticOperator x = quadraticOperator (g • x)) :
    ∃ A : SL(2, Nine.F), ∀ w : W, transport g w = A.val *ᵥ w := by
  let f := commutingLinear g hg
  let A := LinearMap.toMatrix' f
  have hA : A.det = 1 := by
    calc
      A.det = wedge (A *ᵥ ![1, 0]) (A *ᵥ ![0, 1]) := by
        simp [wedge, Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
      _ = wedge ![1, 0] ![0, 1] := by
        simp only [A, LinearMap.toMatrix'_mulVec]
        exact commuting_wedge g hg _ _
      _ = 1 := by simp [wedge]
  exact ⟨⟨A, hA⟩, fun w => (LinearMap.toMatrix'_mulVec f w).symm⟩

end Matrix.PSp4Three.TrivialTwoCore.NormalizerAction
