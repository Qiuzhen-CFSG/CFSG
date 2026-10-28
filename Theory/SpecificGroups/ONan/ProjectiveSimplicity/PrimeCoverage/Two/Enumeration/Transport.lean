module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Setup
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Enumeration.BasisData
import Mathlib.Tactic.FinCases

/-!
# Transport of the binary O'Nan matrix certificates

The fixed words lift to GL(45,7), and their images in PGL are exactly the
specified elements of `ONan.Model`. Thus full matrix collection identities
suffice for division closure, and separation of first rows up to nonzero
scalar suffices for projective injectivity. Neither statement assumes a group
order, a presentation, or an external identification.

The matrix arithmetic is deliberately separate from this transport: the nine
candidate matrices are in `BasisData`, with provenance in `../source/README.md`.
-/

@[expose] public section

namespace ONan.Simplicity.TwoCertificate.Enumeration
/-- The matrix algebra of the supplied representation. -/
abbrev Mat := Matrix (Fin 45) (Fin 45) (ZMod 7)
/-- Invertible linear lifts of projective elements. -/
abbrev Linear := Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)

/-- The exact nine words, evaluated in the fixed linear lifts. -/
def linearGenerators : Fin 9 → Linear := basis linearA linearB

/-- Ordered binary forms in the linear lifts. -/
def linearForm : (Fin 9 → Bool) → Linear :=
  Subgroup.BinaryNormalForm.product linearGenerators

/-- Ordered optional products in the matrix monoid; no invertibility is required. -/
def matrixForm (g : Fin 9 → Mat) (v : Fin 9 → Bool) : Mat :=
  (List.ofFn (fun i => if v i then g i else 1)).prod

private theorem map_local {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) (i : Fin 2) :
    f (localGenerators a b i) = localGenerators (f a) (f b) i := by
  fin_cases i <;> simp [localGenerators]

private theorem map_basis {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) (i : Fin 9) :
    f (basis a b i) = basis (f a) (f b) i := by
  simp only [basis, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  exact map_local f a b j

private theorem map_product {G H : Type*} [Group G] [Group H]
    (f : G →* H) (g : Fin 9 → G) (v : Fin 9 → Bool) :
    f (Subgroup.BinaryNormalForm.product g v) =
      Subgroup.BinaryNormalForm.product (fun i => f (g i)) v := by
  simp only [Subgroup.BinaryNormalForm.product, map_list_prod, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  split <;> simp_all

/-- Each linear word projects to the corresponding generator of the model. -/
theorem project_linearGenerators (i : Fin 9) :
    Matrix.ProjGenLinGroup.mk (linearGenerators i) = (generators i).val := by
  rw [linearGenerators, map_basis]
  have h := map_basis matrixSubgroup.subtype generatorA generatorB i
  exact h.symm

/-- Binary products commute with projection to the actual model. -/
theorem project_linearForm (v : Fin 9 → Bool) :
    Matrix.ProjGenLinGroup.mk (linearForm v) = (normalForm v).val := by
  rw [linearForm, map_product]
  simp only [project_linearGenerators]
  exact (map_product matrixSubgroup.subtype generators v).symm

/-- Evaluation of the nine words determines all binary matrix products. -/
theorem coe_linearForm (g : Fin 9 → Mat)
    (heval : ∀ i, (linearGenerators i : Mat) = g i) (v : Fin 9 → Bool) :
    (linearForm v : Mat) = matrixForm g v := by
  change (Units.coeHom Mat) ((List.ofFn (fun i => if v i then linearGenerators i else 1)).prod) = _
  rw [map_list_prod, List.map_ofFn]
  unfold matrixForm
  congr 1
  apply congrArg List.ofFn
  funext i
  split <;> simp_all

/-- Full matrix right-generator transitions imply division closure in the model. -/
theorem divisionClosed_of_matrix_steps (g : Fin 9 → Mat)
    (heval : ∀ i, (linearGenerators i : Mat) = g i)
    (hstep : ∀ v i, ∃ w, matrixForm g w = matrixForm g v * g i) :
    Subgroup.BinaryNormalForm.DivisionClosed generators := by
  apply Subgroup.BinaryNormalForm.divisionClosed_of_mul_generator
  intro v i
  obtain ⟨w, hw⟩ := hstep v i
  refine ⟨w, ?_⟩
  have hlin : linearForm w = linearForm v * linearGenerators i := by
    apply Units.ext
    simpa only [Matrix.GeneralLinearGroup.coe_mul, coe_linearForm g heval, heval] using hw
  apply Subtype.ext
  change (normalForm w).val = (normalForm v).val * (generators i).val
  rw [← project_linearForm, ← project_linearForm, ← project_linearGenerators, ← map_mul, hlin]

/-- Separation of first rows modulo scalars implies projective uniqueness. -/
theorem injective_of_matrix_separation (g : Fin 9 → Mat)
    (heval : ∀ i, (linearGenerators i : Mat) = g i)
    (hsep : ∀ v w (u : (ZMod 7)ˣ),
      (∀ j, matrixForm g v 0 j * u.val = matrixForm g w 0 j) → v = w) :
    Function.Injective normalForm := by
  intro v w hvw
  have hp : Matrix.ProjGenLinGroup.mk (linearForm v) =
      Matrix.ProjGenLinGroup.mk (linearForm w) := by
    rw [project_linearForm, project_linearForm, hvw]
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp
  apply hsep v w u
  intro j
  have he := congrArg (fun a : Linear => (a : Mat) 0 j) hu
  change (((linearForm v : Mat) * Matrix.scalar (Fin 45) u.val) 0 j) =
    (linearForm w : Mat) 0 j at he
  simpa only [Matrix.scalar_apply, Matrix.mul_diagonal, coe_linearForm g heval] using he
end ONan.Simplicity.TwoCertificate.Enumeration
