module

public import Theory.Combinatorics.ProjectivePlaneThreeFrameRealization
public import Theory.Combinatorics.ProjectivePlaneThreeFrameRigidity
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Mathlib.Algebra.Field.ZMod

/-!
# All collineations of PG(2,3) are canonical PSL₃(3) collineations

Points and line covectors are both the projectivization of `(ZMod 3)³`, with
orthogonality incidence. A full collineation is a pair of permutations preserving
that incidence. The canonical matrix homomorphism acts naturally on points and
by inverse transpose on line covectors.

For an arbitrary collineation, frame realization produces a determinant-one
matrix agreeing with it on the coordinate frame. The quotient of these two
collineations fixes the frame, so frame rigidity makes it the identity. This
proves surjectivity of the actual matrix homomorphism; its faithful point action
already proves injectivity. We package this homomorphism as a multiplicative
equivalence and transfer the matrix group order 5616 to the full collineation
group.

Source motivation: Wong, *On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2*, Theorem 6(b), printed p. 111,
DOI 10.1017/S1446788700022771.
-/

namespace Configuration.PlaneThree

open Matrix.PSL3Three

/-- A full collineation of PG(2,3) is determined by its images of the coordinate frame. -/
public theorem ext_frame {c d : FullCollineation}
    (h : ∀ i : Fin 4, Collineation.pointHom PG PG c (frame i) =
      Collineation.pointHom PG PG d (frame i)) : c = d := by
  apply inv_mul_eq_one.mp
  apply frame_fixed_eq_one
  intro i
  simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
  rw [← h i]
  exact (Collineation.pointHom PG PG c).symm_apply_apply _

/-- Every incidence collineation is induced by the canonical projective matrix action. -/
public theorem pslCollineation_surjective : Function.Surjective pslCollineation := by
  intro c
  obtain ⟨A, hA⟩ := exists_specialLinear_frame c
  refine ⟨project A, ext_frame ?_⟩
  intro i
  simpa only [pslCollineation_project, specialLinearCollineation_point] using (hA i).symm

/-- The full incidence collineation group of PG(2,3) is canonically PSL₃(3). -/
public noncomputable def collineationEquivPSL : FullCollineation ≃* PSL :=
  (MulEquiv.ofBijective pslCollineation
    ⟨pslCollineation_injective, pslCollineation_surjective⟩).symm

/-- The inverse equivalence is the actual matrix-induced incidence collineation. -/
@[simp] public theorem collineationEquivPSL_symm_apply (g : PSL) :
    collineationEquivPSL.symm g = pslCollineation g := by
  unfold collineationEquivPSL
  rfl

@[simp] public theorem pslCollineation_collineationEquivPSL (c : FullCollineation) :
    pslCollineation (collineationEquivPSL c) = c :=
  collineationEquivPSL.symm_apply_apply c

@[simp] public theorem collineationEquivPSL_pslCollineation (g : PSL) :
    collineationEquivPSL (pslCollineation g) = g :=
  collineationEquivPSL.apply_symm_apply g

/-- The matrix represented by the equivalence has exactly the given point action. -/
public theorem collineationEquivPSL_point (c : FullCollineation) (p : PG) :
    Collineation.pointHom PG PG c p = collineationEquivPSL c • p := by
  rw [← pslCollineation_point, pslCollineation_collineationEquivPSL]

/-- On line covectors the inverse equivalence acts by inverse transpose. -/
public theorem collineationEquivPSL_symm_line (A : SL) (l : PG) :
    Collineation.lineHom PG PG (collineationEquivPSL.symm (project A)) l =
      Matrix.SpecialLinearGroup.inverseTranspose A • l := by
  rw [collineationEquivPSL_symm_apply, pslCollineation_line]

/-- The full incidence collineation group of PG(2,3) has order 5616. -/
public theorem card_fullCollineation : Nat.card FullCollineation = 5616 := by
  rw [Nat.card_congr collineationEquivPSL.toEquiv, Matrix.PSL3Three.card_PSL]

end Configuration.PlaneThree
