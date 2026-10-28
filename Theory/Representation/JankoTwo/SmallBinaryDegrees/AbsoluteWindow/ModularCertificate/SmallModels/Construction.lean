module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.Models
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation
public import Theory.Representation.JacobsonDensity
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Character

/-!
# Matrix actions of the literal Hall--Janko carrier

The five ATLAS relations make the two matrices into units satisfying the
published presentation. Injectivity of the presentation's surjection then
transports its universal action to the original degree-100 permutation group.
The generator equations are proved explicitly, so density and traces refer
to that same carrier. Full matrix-algebra generation implies irreducibility.

Source: ATLAS J2G1-P2, as transcribed in the imported Presentation module;
J2G1-f4r6aB0 and J2G1-f4r14aB0, attributed in ../Source.md. Presentation
injectivity remains the independent input owned by the exact-presentation task.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
open Sporadic.LeechRelated.J2
open G2FourModule.Embedding.InnerRealization
variable {F : Type*} [Field F] {n : ℕ}

def MatrixRelations (A B : Matrix (Fin n) (Fin n) F) : Prop :=
  A ^ 2 = 1 ∧ B ^ 3 = 1 ∧ (A * B) ^ 7 = 1 ∧
    (A * B ^ 2 * A * B) ^ 12 = 1 ∧
    (A * B * A * B * A * B ^ 2 * A * B * A * B ^ 2) ^ 6 = 1

def unitA (A B : Matrix (Fin n) (Fin n) F) (h : MatrixRelations A B) :
    (Matrix (Fin n) (Fin n) F)ˣ :=
  ⟨A, A, by simpa only [pow_two] using h.1, by simpa only [pow_two] using h.1⟩

def unitB (A B : Matrix (Fin n) (Fin n) F) (h : MatrixRelations A B) :
    (Matrix (Fin n) (Fin n) F)ˣ :=
  ⟨B, B ^ 2, by simpa only [← pow_succ'] using h.2.1,
    by simpa only [← pow_succ] using h.2.1⟩

theorem units_relations (A B : Matrix (Fin n) (Fin n) F) (h : MatrixRelations A B) :
    Presentation.Relations (unitA A B h) (unitB A B h) := by
  intro i
  apply Units.ext
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

def carrierEquiv (hp : Function.Injective Presentation.toCarrier) : Presentation.UniversalGroup ≃* Carrier :=
  MulEquiv.ofBijective Presentation.toCarrier ⟨hp, Presentation.toCarrier_surjective⟩

def matrixAction (hp : Function.Injective Presentation.toCarrier)
    (A B : Matrix (Fin n) (Fin n) F) (h : MatrixRelations A B) :
    Carrier →* Matrix (Fin n) (Fin n) F :=
  (Units.coeHom _).comp ((Presentation.toGroup (unitA A B h) (unitB A B h)
    (units_relations A B h)).comp (carrierEquiv hp).symm.toMonoidHom)

theorem matrixAction_a (hp : Function.Injective Presentation.toCarrier)
    (A B : Matrix (Fin n) (Fin n) F) (h : MatrixRelations A B) :
    matrixAction hp A B h GeneratorPair.a = A := by
  change ((Presentation.toGroup (unitA A B h) (unitB A B h) (units_relations A B h)) ((carrierEquiv hp).symm GeneratorPair.a)).val = A
  have he : carrierEquiv hp (PresentedGroup.of 0) = GeneratorPair.a := Presentation.toCarrier_zero
  rw [← he, MulEquiv.symm_apply_apply, Presentation.toGroup_zero]
  rfl

theorem matrixAction_b (hp : Function.Injective Presentation.toCarrier)
    (A B : Matrix (Fin n) (Fin n) F) (h : MatrixRelations A B) :
    matrixAction hp A B h GeneratorPair.b = B := by
  change ((Presentation.toGroup (unitA A B h) (unitB A B h) (units_relations A B h)) ((carrierEquiv hp).symm GeneratorPair.b)).val = B
  have he : carrierEquiv hp (PresentedGroup.of 1) = GeneratorPair.b := Presentation.toCarrier_one
  rw [← he, MulEquiv.symm_apply_apply, Presentation.toGroup_one]
  rfl

def action (hp : Function.Injective Presentation.toCarrier)
    (A B : Matrix (Fin n) (Fin n) F) (h : MatrixRelations A B) :
    Representation F Carrier (Fin n → F) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp (matrixAction hp A B h)

theorem toMatrix_action (hp : Function.Injective Presentation.toCarrier)
    (A B : Matrix (Fin n) (Fin n) F) (h : MatrixRelations A B) (g : Carrier) :
    LinearMap.toMatrix' (action hp A B h g) = matrixAction hp A B h g :=
  LinearMap.toMatrix'_toLin' _

theorem action_a (hp : Function.Injective Presentation.toCarrier)
    (A B : Matrix (Fin n) (Fin n) F) (h : MatrixRelations A B) :
    LinearMap.toMatrix' (action hp A B h GeneratorPair.a) = A := by
  rw [toMatrix_action, matrixAction_a]

theorem action_b (hp : Function.Injective Presentation.toCarrier)
    (A B : Matrix (Fin n) (Fin n) F) (h : MatrixRelations A B) :
    LinearMap.toMatrix' (action hp A B h GeneratorPair.b) = B := by
  rw [toMatrix_action, matrixAction_b]

theorem action_dense (hp : Function.Injective Presentation.toCarrier)
    (A B : Matrix (Fin n) (Fin n) F) (h : MatrixRelations A B)
    (hd : Algebra.adjoin F ({A, B} : Set (Matrix (Fin n) (Fin n) F)) = ⊤) :
    Algebra.adjoin F (Set.range (action hp A B h)) = ⊤ := by
  let S := Algebra.adjoin F (Set.range (action hp A B h))
  have hle : Algebra.adjoin F ({A, B} : Set (Matrix (Fin n) (Fin n) F)) ≤
      S.comap Matrix.toLinAlgEquiv'.toAlgHom := by
    apply Algebra.adjoin_le
    intro M hM
    rcases hM with rfl | hM
    · change Matrix.toLin' M ∈ S
      rw [← action_a hp M B h, Matrix.toLin'_toMatrix']
      exact Algebra.subset_adjoin (Set.mem_range_self GeneratorPair.a)
    · have hM' : M = B := hM
      subst M
      change Matrix.toLin' B ∈ S
      rw [← action_b hp A B h, Matrix.toLin'_toMatrix']
      exact Algebra.subset_adjoin (Set.mem_range_self GeneratorPair.b)
  apply top_unique
  intro f _
  have hm : LinearMap.toMatrix' f ∈ Algebra.adjoin F
      ({A, B} : Set (Matrix (Fin n) (Fin n) F)) := by rw [hd]; trivial
  have hf := hle hm
  change Matrix.toLin' (LinearMap.toMatrix' f) ∈ S at hf
  simpa only [Matrix.toLin'_toMatrix'] using hf

theorem action_irreducible [NeZero n] (hp : Function.Injective Presentation.toCarrier)
    (A B : Matrix (Fin n) (Fin n) F) (h : MatrixRelations A B)
    (hd : Algebra.adjoin F ({A, B} : Set (Matrix (Fin n) (Fin n) F)) = ⊤) :
    IsIrreducible (action hp A B h) :=
  irreducible_of_jacobson_density_surjective _ (action_dense hp A B h hd)

def wordValue {M : Type*} [Monoid M] (a b : M) (w : List Bool) : M :=
  (w.map fun s => if s then b else a).prod

theorem map_wordValue {M N : Type*} [Monoid M] [Monoid N]
    (f : M →* N) (a b : M) (w : List Bool) :
    f (wordValue a b w) = wordValue (f a) (f b) w := by
  simp only [wordValue, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  cases s <;> rfl

theorem character_word (hp : Function.Injective Presentation.toCarrier)
    (A B : Matrix (Fin n) (Fin n) F) (h : MatrixRelations A B) (w : List Bool) :
    (action hp A B h).character (wordValue GeneratorPair.a GeneratorPair.b w) =
      (wordValue A B w).trace := by
  rw [Representation.character, LinearMap.trace_eq_matrix_trace F (Pi.basisFun F (Fin n))]
  change (LinearMap.toMatrix' (action hp A B h _)).trace = _
  rw [toMatrix_action, map_wordValue, matrixAction_a, matrixAction_b]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
