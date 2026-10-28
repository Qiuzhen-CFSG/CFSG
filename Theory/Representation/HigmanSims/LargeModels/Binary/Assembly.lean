module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Data
public import Theory.Representation.HigmanSims.LargeModels.ScalarExtension

/-!
# From marked binary HS actions and matrix density to the four models

Two independent calculations suffice. First construct an action of the literal
permutation-generated HS carrier with the specified matrices on its generators.
Then prove that those two matrices generate the full matrix algebra. The latter
identity transports to the action algebra, survives scalar extension, and proves
absolute irreducibility. The final lemma applies the existing coefficient-field
extension theorem to these four actions.

Neither calculation is assumed to follow from the ATLAS description or a check
of presentation relations. They remain explicit below. Source: the four ATLAS
binary HS candidates documented in `Binary/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary

open Sporadic.LeechRelated.HS

def permutationA : Carrier := ⟨generatorA, Subgroup.subset_closure (by simp)⟩
def permutationB : Carrier := ⟨generatorB, Subgroup.subset_closure (by simp)⟩

/-- An actual action of the literal HS carrier, with both source generators marked.
The homomorphism laws, including descent from words, are part of `action`. -/
structure MarkedAction (i : Fin 4) where
  action : Representation (ZMod 2) Carrier (Vector i)
  matrix_a : LinearMap.toMatrix' (action permutationA) = aMatrix i
  matrix_b : LinearMap.toMatrix' (action permutationB) = bMatrix i

/-- The algebra-generation calculation, independent of carrier descent. -/
def MatrixAlgebraFull (i : Fin 4) : Prop :=
  Algebra.adjoin (ZMod 2) ({aMatrix i, bMatrix i} : Set (Mat i)) = ⊤

namespace MarkedAction

variable {i : Fin 4} (C : MarkedAction i)

/-- A certificate in the published matrix basis fills the actual action algebra. -/
theorem density (h : MatrixAlgebraFull i) :
    Algebra.adjoin (ZMod 2) (Set.range C.action) = ⊤ := by
  let P := Algebra.adjoin (ZMod 2) (Set.range C.action)
  let e : Module.End (ZMod 2) (Vector i) ≃ₐ[ZMod 2] Mat i :=
    LinearMap.toMatrixAlgEquiv'
  let Q := P.map e.toAlgHom
  have ha : aMatrix i ∈ Q := by
    rw [← C.matrix_a]
    exact ⟨C.action permutationA, Algebra.subset_adjoin (Set.mem_range_self _), rfl⟩
  have hb : bMatrix i ∈ Q := by
    rw [← C.matrix_b]
    exact ⟨C.action permutationB, Algebra.subset_adjoin (Set.mem_range_self _), rfl⟩
  have hQ : Q = ⊤ := by
    apply top_unique
    rw [← h]
    apply Algebra.adjoin_le
    intro M hM
    rcases Set.mem_insert_iff.mp hM with rfl | hM
    · exact ha
    · exact Set.mem_singleton_iff.mp hM ▸ hb
  apply top_unique
  intro f _
  have hf : e f ∈ Q := by rw [hQ]; trivial
  obtain ⟨f', hf', he⟩ := hf
  exact e.injective he ▸ hf'

/-- Density proves irreducibility over the algebraic closure, as required by the
tensor-product definition of absolute irreducibility. -/
theorem absolutelyIrreducible (h : MatrixAlgebraFull i) :
    C.action.IsAbsolutelyIrreducible := by
  have hpos : ∀ j, 0 < binaryDegree j := by decide
  let : NeZero (binaryDegree i) := ⟨Nat.ne_of_gt (hpos i)⟩
  refine ⟨?_⟩
  apply irreducible_of_jacobson_density_surjective
  exact (extendScalars_surj_iff (AlgebraicClosure (ZMod 2)) C.action).mp (C.density h)

end MarkedAction

/-- Assemble the four finite models from separately proved carrier descent and
matrix-algebra calculations. Simplicity is available to the descent producer. -/
theorem binaryModelsExist_of_marked_actions
    (hdesc : IsSimpleGroup Carrier → ∀ i, Nonempty (MarkedAction i))
    (hfull : ∀ i, MatrixAlgebraFull i) : BinaryModelsExist := by
  intro hs
  let C : ∀ i, MarkedAction i := fun i => Classical.choice (hdesc hs i)
  exact ⟨fun i => (C i).action, fun i => (C i).absolutelyIrreducible (hfull i)⟩

/-- The marked finite constructions supply the four models over every
characteristic-two field, with the exact dimensions required by saturation. -/
theorem binaryModels_over_field_of_marked_actions
    (hdesc : IsSimpleGroup Carrier → ∀ i, Nonempty (MarkedAction i))
    (hfull : ∀ i, MatrixAlgebraFull i) (hs : IsSimpleGroup Carrier)
    (F : Type*) [Field F] [CharP F 2] :
    ∃ ρ : ∀ i, Representation F Carrier (Fin (binaryDegree i) → F),
      ∀ i, (ρ i).IsIrreducible :=
  binaryModels_over_field (binaryModelsExist_of_marked_actions hdesc hfull) hs F

end Representation.HigmanSims.LargeModels.Binary
