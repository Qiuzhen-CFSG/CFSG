module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.CoefficientBrackets.PolynomialTransfer

/-!
# The nonopposite D4 coefficient interface

The actual root-sum exchanges imply exact first-coefficient relations, by
mixed coefficient extraction. Every root coefficient lies in the triangular
operator sum. Thus the nonopposite part of positive-negative commutation
follows, and the remaining opposite-root premise is isolated explicitly.

The group exchanges and the opposite-root Cartan calculation are not asserted
here: they are the independent geometric and Jacobi steps still required for
the unconditional bracket containments. All operators remain the coefficients
of the given rational representation and the given regular pinned curves.

Sources: GLS3 §1.12; Steinberg, *Representations of Algebraic Groups* (1963),
§§2 and 4.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
@[expose] public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Actual simply laced root exchanges, with characteristic-two signs.
`S.addition` identifies the option-valued sum with vector addition in D4. -/
def HasNonoppositeRootExchanges (S : D4Geometry K) : Prop :=
  ∀ α β : S.roots.Root, β ≠ S.roots.neg α →
    match S.roots.add α β with
    | none => ∀ a b : k, Commute (S.chevalley.x α a) (S.chevalley.x β b)
    | some γ => ∀ a b : k, S.chevalley.x α a * S.chevalley.x β b =
        S.chevalley.x β b * S.chevalley.x α a * S.chevalley.x γ (a * b)

/-- Exact nonopposite relations for the actual first root coefficients. -/
def HasNonoppositeCoefficientRelations (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ) : Prop :=
  ∀ α β : S.roots.Root, β ≠ S.roots.neg α →
    rootOperator S ρ hρ α * rootOperator S ρ hρ β -
      rootOperator S ρ hρ β * rootOperator S ρ hρ α =
        match S.roots.add α β with
        | none => 0
        | some γ => rootOperator S ρ hρ γ

/-- Actual group exchanges transfer to actual coefficient relations. -/
theorem nonopposite_coefficients_of_exchanges (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (hx : HasNonoppositeRootExchanges S) : HasNonoppositeCoefficientRelations S ρ hρ := by
  intro α β hne
  have h := hx α β hne
  cases he : S.roots.add α β with
  | none =>
    exact rootOperator_commutator_of_commute S ρ hρ α β (by simpa only [he] using h)
  | some γ =>
    simpa only [one_smul] using rootOperator_commutator_of_exchange S ρ hρ α β γ 1 (by
      simpa only [he, one_mul] using h)

/-- Every actual root coefficient belongs to the full triangular operator sum. -/
theorem rootOperator_mem_triangular (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α : S.roots.Root) :
    rootOperator S ρ hρ α ∈ nonnegativeOperators S ρ hρ ⊔ negativeOperators S ρ hρ := by
  have hsign : α ∈ S.roots.positive ∨ S.roots.neg α ∈ S.roots.positive := by
    exact (Set.ext_iff.mp S.bigCell.data.positive.2.1 α).mpr (Set.mem_univ α)
  rcases hsign with hp | hn
  · exact (show nonnegativeOperators S ρ hρ ≤ _ from le_sup_left)
      ((show positiveOperators S ρ hρ ≤ nonnegativeOperators S ρ hρ from le_sup_left)
        (Submodule.subset_span ⟨⟨α, hp⟩, rfl⟩))
  · apply (show negativeOperators S ρ hρ ≤ _ from le_sup_right)
    exact Submodule.subset_span ⟨⟨S.roots.neg α, hn⟩, by
      change rootOperator S ρ hρ (S.roots.neg (S.roots.neg α)) = _
      rw [S.realized.neg_neg]⟩

/-- The nonopposite coefficient relations give triangular commutator membership. -/
theorem nonopposite_commutator_mem_of_relations (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (hc : HasNonoppositeCoefficientRelations S ρ hρ)
    (α β : S.roots.Root) (hne : β ≠ S.roots.neg α) :
    rootOperator S ρ hρ α * rootOperator S ρ hρ β -
      rootOperator S ρ hρ β * rootOperator S ρ hρ α ∈
        nonnegativeOperators S ρ hρ ⊔ negativeOperators S ρ hρ := by
  rw [hc α β hne]
  cases S.roots.add α β with
  | none => exact Submodule.zero_mem _
  | some γ => exact rootOperator_mem_triangular S ρ hρ γ

/-- Assemble positive-negative membership from nonopposite relations and the
opposite-root Cartan calculation. Both mathematical inputs remain explicit. -/
theorem positive_negative_commutator_mem_of_relations (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (hc : HasNonoppositeCoefficientRelations S ρ hρ)
    (hop : ∀ α : S.roots.Root,
      rootOperator S ρ hρ α * rootOperator S ρ hρ (S.roots.neg α) -
        rootOperator S ρ hρ (S.roots.neg α) * rootOperator S ρ hρ α ∈
          cartanOperators S ρ hρ)
    (α β : PositiveRoot S) :
    rootOperator S ρ hρ α.val * rootOperator S ρ hρ (S.roots.neg β.val) -
      rootOperator S ρ hρ (S.roots.neg β.val) * rootOperator S ρ hρ α.val ∈
        nonnegativeOperators S ρ hρ ⊔ negativeOperators S ρ hρ := by
  by_cases he : β.val = α.val
  · rw [he]
    exact (show nonnegativeOperators S ρ hρ ≤ _ from le_sup_left)
      ((show cartanOperators S ρ hρ ≤ nonnegativeOperators S ρ hρ from le_sup_right)
        (hop α.val))
  · apply nonopposite_commutator_mem_of_relations S ρ hρ hc
    intro h
    apply he
    have h' := congrArg S.roots.neg h
    simpa only [S.realized.neg_neg] using h'

end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
