module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Inputs
public import Mathlib.GroupTheory.IsPerfect

/-!
# Matrix factors and determinant one for a perfect local group

Two arbitrary two-by-two matrices act on (0,5) and on both (1,3) and (2,4).
Extracting coefficients from four basis vectors is a left inverse to this
action. Consequently a block formula for an additive group representation
gives a matrix-pair homomorphism. Perfectness kills the two determinant
characters, producing the required SL₂ pair with the literal action formula.

`Factorization` applies this to the actual local A₅. No projection is assumed
faithful or surjective.
Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, p.284.
-/

open Matrix Atlas.Conway Atlas.Algebra
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Factorization

abbrev MatrixPair := Matrix (Fin 2) (Fin 2) F × Matrix (Fin 2) (Fin 2) F

def matrixAction (p : MatrixPair) (v : Fin 6 → F) : Fin 6 → F :=
  ![p.1 0 0 * v 0 + p.1 0 1 * v 5,
    p.2 0 0 * v 1 + p.2 0 1 * v 3,
    p.2 0 0 * v 2 + p.2 0 1 * v 4,
    p.2 1 0 * v 1 + p.2 1 1 * v 3,
    p.2 1 0 * v 2 + p.2 1 1 * v 4,
    p.1 1 0 * v 0 + p.1 1 1 * v 5]

def coefficients (f : (Fin 6 → F) → (Fin 6 → F)) : MatrixPair :=
  (!![f (Pi.single 0 1) 0, f (Pi.single 5 1) 0;
      f (Pi.single 0 1) 5, f (Pi.single 5 1) 5],
   !![f (Pi.single 1 1) 1, f (Pi.single 3 1) 1;
      f (Pi.single 1 1) 3, f (Pi.single 3 1) 3])

theorem matrixAction_mul (p q : MatrixPair) (v : Fin 6 → F) :
    matrixAction (p * q) v = matrixAction p (matrixAction q v) := by
  funext i
  fin_cases i <;>
    simp [matrixAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem matrixAction_one (v : Fin 6 → F) : matrixAction 1 v = v := by
  funext i
  fin_cases i <;> simp [matrixAction]

theorem coefficients_matrixAction (p : MatrixPair) : coefficients (matrixAction p) = p := by
  apply Prod.ext <;> apply Matrix.ext <;> intro i j <;>
    fin_cases i <;> fin_cases j <;> simp [coefficients, matrixAction]

theorem matrixAction_injective : Function.Injective matrixAction := by
  intro p q h
  simpa only [coefficients_matrixAction] using congrArg coefficients h

variable {H : Type*} [Group H]

def matrixHom (ρ : H →* Multiplicative (AddAut (Fin 6 → F)))
    (hρ : ∀ a v, ρ a v = matrixAction (coefficients (ρ a)) v) : H →* MatrixPair where
  toFun a := coefficients (ρ a)
  map_one' := by
    apply matrixAction_injective
    funext v
    rw [← hρ, map_one, matrixAction_one]
    rfl
  map_mul' a b := by
    apply matrixAction_injective
    funext v
    rw [matrixAction_mul, ← hρ, ← hρ, ← hρ, map_mul]
    rfl

theorem det_eq_one [Group.IsPerfect H] (f : H →* Matrix (Fin 2) (Fin 2) F) (a : H) :
    (f a).det = 1 := by
  let χ : H →* Fˣ := (Matrix.detMonoidHom.comp f).toHomUnits
  have h : χ a = 1 := Abelianization.commutator_subset_ker χ Group.IsPerfect.mem_commutator
  exact congrArg (fun u : Fˣ => (u : F)) h

def specialLinearHom [Group.IsPerfect H] (f : H →* Matrix (Fin 2) (Fin 2) F) :
    H →* SL(2,F) where
  toFun a := ⟨f a, det_eq_one f a⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' a b := Subtype.ext (map_mul f a b)

def specialLinearPair [Group.IsPerfect H] (ρ : H →* Multiplicative (AddAut (Fin 6 → F)))
    (hρ : ∀ a v, ρ a v = matrixAction (coefficients (ρ a)) v) :
    H →* (SL(2,F) × SL(2,F)) :=
  (specialLinearHom ((MonoidHom.fst _ _).comp (matrixHom ρ hρ))).prod
    (specialLinearHom ((MonoidHom.snd _ _).comp (matrixHom ρ hρ)))

theorem specialLinearPair_action [Group.IsPerfect H] (ρ : H →* Multiplicative (AddAut (Fin 6 → F)))
    (hρ : ∀ a v, ρ a v = matrixAction (coefficients (ρ a)) v) (a : H) (v : Fin 6 → F) :
    pairRepresentation (specialLinearPair ρ hρ a) v = ρ a v := (hρ a v).symm

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Factorization
