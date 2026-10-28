module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.Forms
public import Theory.Representation.BinaryOffender.NormalizerImage
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.Actors
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.Parameters

/-!
# Reducing simultaneous graph forms to root placement

The original outer-image hypothesis and the actual adjoint matrix forms give
one common change of basis with a marked Gram-transpose actor. This construction
is proved here as `normalized_graph_action`; it does not require faithfulness
on the covering SL₃ or a new normal-form premise.

The remaining `RootPlacement` contract asks only for pointwise root/graph forms
after a Gram-preserving change of ternary basis. `graph_forms_of_rootPlacement`
then constructs the full published `GraphForms` output: the parameter group law,
injectivity and marked `(0,1)` actor are all proved by the coordinate adapter.
Root placement itself is not asserted in this module. The owner of
`Outer.Adjoint.graph_forms` must discharge it before claiming that theorem.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8,
step 3A, author manuscript p.27; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer
open Matrix
variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V)

/-- An actual change of adjoint coordinates putting one actor in the prescribed
graph form while retaining actual standard matrix forms for all actors.
It contains neither a root placement nor a parameter homomorphism. -/
structure NormalizedGraphAction (A : Subgroup (linearNormalizer σ)) where
  equiv : V ≃ₗ[ZMod 2] AdjointSpace B.Carrier
  standard : ∀ t : A, ∃ g : GL (Fin 3) B.Carrier,
    (∀ v : V, matrix (equiv (t.val.val.val v)) = inner g (matrix (equiv v))) ∨
    (∀ v : V, matrix (equiv (t.val.val.val v)) = graph g (matrix (equiv v)))
  graph_mem : ∃ t : A, ∀ v : V, matrix (equiv (t.val.val.val v)) =
    gram B.Carrier * (matrix (equiv v)).transpose * gram B.Carrier

/-- Normalize a graph actor selected by the original outer-image hypothesis.
All hypotheses here are precisely the published `GraphForms` inputs. -/
theorem normalized_graph_action (e : σ.Equiv (binaryRep B))
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (houter : ¬ A.map (linearNormalizer σ).subtype ≤ actionImage σ)
    (hforms : ∀ t ∈ A, HasStandardAction B σ e t) :
    Nonempty (NormalizedGraphAction B σ A) := by
  obtain ⟨t, g, hg, C, hC⟩ := exists_graph_actor B σ e A hA houter hforms
  let E := e.toLinearEquiv.trans ((adjointConj C).restrictScalars (ZMod 2))
  refine ⟨{ equiv := E, standard := ?_, graph_mem := ?_ }⟩
  · intro u
    obtain ⟨k, hi | hj⟩ := hforms u.val u.property
    · refine ⟨C * k * C⁻¹, Or.inl ?_⟩
      intro v
      change matrix (adjointConj C (e (u.val.val.val v))) =
        inner (C * k * C⁻¹) (matrix (adjointConj C (e v)))
      rw [matrix_adjointConj, matrix_adjointConj]
      change ∀ v : V, matrix (e (u.val.val.val v)) = inner k (matrix (e v)) at hi
      rw [hi, inner_conj]
    · refine ⟨C * k * transposeGL C, Or.inr ?_⟩
      intro v
      change matrix (adjointConj C (e (u.val.val.val v))) =
        graph (C * k * transposeGL C) (matrix (adjointConj C (e v)))
      rw [matrix_adjointConj, matrix_adjointConj]
      change ∀ v : V, matrix (e (u.val.val.val v)) = graph k (matrix (e v)) at hj
      rw [hj, graph_conj]
  · refine ⟨t, fun v => ?_⟩
    change matrix (adjointConj C (e (t.val.val.val v))) =
      gram B.Carrier * (matrix (adjointConj C (e v))).transpose * gram B.Carrier
    rw [matrix_adjointConj, matrix_adjointConj, hg, graph_conj_gram C g hC]

namespace NormalizedGraphAction
variable {B σ} {A : Subgroup (linearNormalizer σ)} (N : NormalizedGraphAction B σ A)

/-- The binary coordinates after a further change of ternary basis. -/
def coordinateEquiv (C : GL (Fin 3) B.Carrier) : V ≃ₗ[ZMod 2] Eight B.Carrier :=
  N.equiv.trans (((adjointConj C).trans (coordinates B.Carrier)).restrictScalars (ZMod 2))

private theorem matrixOf_injective : Function.Injective (matrixOf B.Carrier) := by
  intro x y h
  apply (coordinates B.Carrier).symm.injective
  apply matrix_injective
  simpa only [← matrixOf_coordinates, LinearEquiv.apply_symm_apply] using h

/-- Changes of basis in the graph centralizer retain the marked graph actor. -/
theorem coordinate_graph_mem (C : GL (Fin 3) B.Carrier)
    (hC : C.val * gram B.Carrier * C.val.transpose = gram B.Carrier) :
    ∃ t : A, ∀ v : V,
      N.coordinateEquiv C (normalizerRepresentation σ t.val v) =
      graphCoordinates B.Carrier (N.coordinateEquiv C v) := by
  obtain ⟨t, ht⟩ := N.graph_mem
  refine ⟨t, fun v => ?_⟩
  apply matrixOf_injective
  change matrixOf B.Carrier (coordinates B.Carrier (adjointConj C (N.equiv (t.val.val.val v)))) =
    matrixOf B.Carrier (graphCoordinates B.Carrier
      (coordinates B.Carrier (adjointConj C (N.equiv v))))
  rw [matrixOf_coordinates, matrixOf_graphCoordinates, matrixOf_coordinates]
  change matrix (adjointConj C (N.equiv (t.val.val.val v))) =
    gram B.Carrier * (matrix (adjointConj C (N.equiv v))).transpose * gram B.Carrier
  rw [matrix_adjointConj, matrix_adjointConj, ht]
  let J : GL (Fin 3) B.Carrier :=
    ⟨gram B.Carrier, gram B.Carrier, gram_sq B.Carrier, gram_sq B.Carrier⟩
  exact graph_conj_gram C J hC (matrix (N.equiv v))
end NormalizedGraphAction

/-- Remaining matrix geometry, isolated after graph-involution conjugacy.
An elementary family containing the literal graph operator can be moved,
by an isometry of its Gram matrix, into one root group times the graph bit.
The parameterization need only be pointwise: its homomorphism and injectivity
are proved by `form_of_pointwise`, not assumed here. -/
def RootPlacement : Prop :=
  ∀ (A : Subgroup (linearNormalizer σ)), IsElementaryTwo A →
    ∀ N : NormalizedGraphAction B σ A,
      ∃ C : GL (Fin 3) B.Carrier,
        C.val * gram B.Carrier * C.val.transpose = gram B.Carrier ∧
        ∀ t : A, ∃ p : B.Carrier × ZMod 2, ∀ v : V,
          N.coordinateEquiv C (normalizerRepresentation σ t.val v) =
            operator B.Carrier p (N.coordinateEquiv C v)

/-- The remaining root placement supplies every field of the literal
`GraphForm`; in particular the group parameter is proved faithful. -/
theorem graph_forms_of_rootPlacement (hroot : RootPlacement B σ) : GraphForms B σ := by
  intro e A hA houter hforms
  obtain ⟨N⟩ := normalized_graph_action B σ e A hA houter hforms
  obtain ⟨C, hC, hp⟩ := hroot A hA N
  apply form_of_pointwise B (normalizerRepresentation σ) A
    (normalizerRepresentation_injective σ) (N.coordinateEquiv C) hp
  exact N.coordinate_graph_mem C hC

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer
