module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Basic
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Presentation

/-!
# The ATLAS presentation evaluated in the literal binary symplectic group

The ATLAS natural six-dimensional generators are changed to the standard
symplectic basis. In that basis the first is a transvection. Membership in
the literal matrix group and all seven source relations are checked below.

The original row masks are A = [2,1,7,11,16,35] and
B = [4,6,8,16,32,23], where the least significant bit is coordinate zero.
The change-of-basis matrix has columns [47,3,4,1,24,35]; the matrices below
are P⁻¹AP and P⁻¹BP. No identification of an abstract group is assumed:
the matrix membership and word identities are checked independently.

Source: R. A. Wilson, S. J. Nickerson and J. N. Bray, *ATLAS of Finite Group
Representations*, https://brauer.maths.qmul.ac.uk/Atlas/v3/matrep/S62G1-f2r6B0,
files `S62G1-f2r6B0.m1` and `.m2`, retrieved 8 October 2026.
The seven words are from the Magma file cited in `Presentation`.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation

abbrev Coordinate := Fin 3 ⊕ Fin 3

/-- Order the standard hyperbolic basis as e₀,e₁,e₂,f₀,f₁,f₂. -/
def coordinate : Coordinate → Fin 6 :=
  Sum.elim (fun i => ⟨i, by omega⟩) (fun i => ⟨i + 3, by omega⟩)

def matrixOfRows (r : Fin 6 → Fin 6 → ZMod 2) : Matrix Coordinate Coordinate (ZMod 2) :=
  fun i j => r (coordinate i) (coordinate j)

def matrixA : Matrix Coordinate Coordinate (ZMod 2) := matrixOfRows
  ![![1,0,0,1,0,0], ![0,1,0,0,0,0], ![0,0,1,0,0,0],
    ![0,0,0,1,0,0], ![0,0,0,0,1,0], ![0,0,0,0,0,1]]

def matrixB : Matrix Coordinate Coordinate (ZMod 2) := matrixOfRows
  ![![1,0,0,0,1,1], ![1,1,0,1,1,1], ![0,0,0,0,0,1],
    ![1,1,0,0,0,1], ![1,0,0,0,0,1], ![0,0,1,1,0,1]]

private theorem matrixA_mem : matrixA ∈ Matrix.symplecticGroup (Fin 3) (ZMod 2) := by
  change matrixA * Matrix.J _ _ * matrixA.transpose = Matrix.J _ _
  decide +kernel

private theorem matrixB_mem : matrixB ∈ Matrix.symplecticGroup (Fin 3) (ZMod 2) := by
  change matrixB * Matrix.J _ _ * matrixB.transpose = Matrix.J _ _
  decide +kernel

def a : Base := ⟨matrixA, by exact matrixA_mem⟩
def b : Base := ⟨matrixB, by exact matrixB_mem⟩

def matrixGenerator : Bool → Base
  | false => a
  | true => b

/-- Every sourced word is an identity in the actual six-dimensional matrices. -/
theorem matrix_word (i : Fin 7) : word a b i = 1 := by
  fin_cases i <;> apply Subtype.ext <;> decide +kernel

def matrixEvaluation : Free →* Base := FreeGroup.lift matrixGenerator

@[simp] theorem matrixEvaluation_relator (i : Fin 7) : matrixEvaluation (relator i) = 1 := by
  rw [relator, map_word]
  simp only [matrixEvaluation, FreeGroup.lift_apply_of, matrixGenerator]
  exact matrix_word i

/-- The actual map whose faithfulness is needed to certify the presentation. -/
def matrixMap : Presented →* Base :=
  PresentedGroup.toGroup (f := matrixGenerator) (by
    rintro _ ⟨i, rfl⟩
    exact matrixEvaluation_relator i)

@[simp] theorem matrixMap_generator (i : Bool) : matrixMap (generator i) = matrixGenerator i :=
  PresentedGroup.toGroup.of _

theorem matrixMap_toPresented (x : Free) : matrixMap (toPresented x) = matrixEvaluation x := by
  have h : matrixMap.comp toPresented = matrixEvaluation := by
    apply FreeGroup.ext_hom
    intro i
    simpa only [MonoidHom.comp_apply, matrixEvaluation, FreeGroup.lift_apply_of,
      toPresented, generator, PresentedGroup.of]
      using matrixMap_generator i
  exact DFunLike.congr_fun h x

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation
