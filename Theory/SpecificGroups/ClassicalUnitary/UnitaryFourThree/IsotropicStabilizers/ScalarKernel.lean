module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
public import Mathlib.GroupTheory.Solvable
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The scalar kernel in dimension four over Nine

For any nondegenerate Hermitian form with cube conjugation, a scalar belongs
to SU₄ exactly when its fourth power is one. The scalar homomorphism identifies
the entire kernel of the actual SU₄ image in PGL with these fourth roots of
unity. Its order is four, and it is solvable. These results apply to both the
identity form and the hyperbolic coordinate form.

The determinant gives necessity; cube conjugation gives sufficiency in the
unitary equation. The kernel description then follows from the center of GL.
Source: GLS3, chapter 2, classical-group conventions, especially the distinction
between SU and its image PSU in PGL. This kernel must be retained in the
stabilizers used for Aschbacher–Smith, Theorem 0.1.2(4), condition K.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers

variable (J : HermitianForm 4 FiniteField.Nine)
    (hc : ∀ x, J.conj x = x ^ 3)

include hc in
/-- The determinant restriction on a scalar is also sufficient for unitarity. -/
theorem scalar_mem_specialSubgroup_iff (u : FiniteField.Nineˣ) :
    GeneralLinearGroup.scalar (Fin 4) u ∈ J.specialSubgroup ↔ u ^ 4 = 1 := by
  rw [J.mem_specialSubgroup_iff]
  constructor
  · intro h
    simpa using h.2
  · intro h
    refine ⟨?_, by simpa using h⟩
    have hu : (u : FiniteField.Nine) ^ 4 = 1 := congrArg Units.val h
    have hadj : J.conjTranspose (GeneralLinearGroup.scalar (Fin 4) u).val =
        Matrix.diagonal (fun _ : Fin 4 => J.conj (u : FiniteField.Nine)) := by
      apply Matrix.ext
      intro i j
      by_cases hij : i = j <;>
        simp [HermitianForm.conjTranspose, GeneralLinearGroup.coe_scalar,
          Matrix.scalar, hij, Ne.symm]
    rw [hadj]
    apply Matrix.ext
    intro i j
    change (Matrix.diagonal (fun _ : Fin 4 => J.conj (u : FiniteField.Nine)) *
      J.form * Matrix.diagonal (fun _ : Fin 4 => (u : FiniteField.Nine))) i j = J.form i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hc]
    calc
      (↑u ^ 3 * J.form i j) * ↑u = ↑u ^ 4 * J.form i j := by ring
      _ = J.form i j := by rw [hu, one_mul]


omit hc in
/-- Every element killed in PGL is literally a fourth-root scalar. -/
theorem mem_project_kernel_iff (g : J.specialSubgroup) :
    g ∈ (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project FiniteField.Nine J).ker ↔
      ∃ u : FiniteField.Nineˣ, u ^ 4 = 1 ∧ GeneralLinearGroup.scalar (Fin 4) u = g.val := by
  constructor
  · intro hg
    have hh : ProjGenLinGroup.mk g.val = 1 := congrArg Subtype.val hg
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hh
    obtain ⟨u, hu⟩ := hh
    refine ⟨u, ?_, hu⟩
    have hd := (J.mem_specialSubgroup_iff g.val).mp g.property |>.2
    rw [← hu] at hd
    simpa using hd
  · rintro ⟨u, _, hu⟩
    apply Subtype.ext
    change ProjGenLinGroup.mk g.val = 1
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, hu⟩

/-- The scalar embedding, with its codomain restricted to the actual projection kernel. -/
@[expose] def scalarKernelHom : rootsOfUnity 4 FiniteField.Nine →*
    (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project FiniteField.Nine J).ker where
  toFun u := ⟨⟨GeneralLinearGroup.scalar (Fin 4) u.val,
      (scalar_mem_specialSubgroup_iff J hc u.val).mpr u.property⟩,
    (mem_project_kernel_iff J _).mpr ⟨u.val, u.property, rfl⟩⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
  map_mul' u v := by apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _

theorem scalarKernelHom_bijective : Function.Bijective (scalarKernelHom J hc) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    apply Units.ext
    have hh := congrArg (fun g => g.val.val.val 0 0) huv
    exact hh
  · intro g
    obtain ⟨u, hu, hug⟩ := (mem_project_kernel_iff J g.val).mp g.property
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hug

/-- The complete scalar kernel, as a multiplicative equivalence. -/
def scalarKernelEquiv : rootsOfUnity 4 FiniteField.Nine ≃*
    (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project FiniteField.Nine J).ker :=
  MulEquiv.ofBijective (scalarKernelHom J hc) (scalarKernelHom_bijective J hc)


/-- The kernel equivalence sends a fourth root to its scalar matrix. -/
theorem scalarKernelEquiv_apply (u : rootsOfUnity 4 FiniteField.Nine) :
    (scalarKernelEquiv J hc u).val.val = GeneralLinearGroup.scalar (Fin 4) u.val := by
  unfold scalarKernelEquiv
  rfl

private def rootValueEquiv : rootsOfUnity 4 FiniteField.Nine ≃
    {x : FiniteField.Nine // x ^ 4 = 1} where
  toFun u := ⟨u.val.val, (mem_rootsOfUnity' 4 u.val).mp u.property⟩
  invFun x := rootsOfUnity.mkOfPowEq x.val x.property
  left_inv u := by apply Subtype.ext; apply Units.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

include hc in
/-- In characteristic three this scalar kernel has order four. -/
theorem scalarKernel_card :
    Nat.card (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project FiniteField.Nine J).ker = 4 := by
  rw [← Nat.card_congr (scalarKernelEquiv J hc).toEquiv,
    Nat.card_congr rootValueEquiv, Nat.card_eq_fintype_card]
  decide

include hc in
/-- The scalar kernel is a solvable central layer. -/
theorem scalarKernel_solvable :
    Group.IsSolvable (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project FiniteField.Nine J).ker :=
  Group.isSolvable_of_surjective (f := scalarKernelHom J hc) (scalarKernelHom_bijective J hc).surjective

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers
