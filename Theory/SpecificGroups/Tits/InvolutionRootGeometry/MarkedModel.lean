module

public import Theory.SpecificGroups.ReeF4.DerivedTits

/-!
# A root-marked comparison for the Tits group

The faithful Parrott realization identifies the derived binary Ree group with
Parrott's group while retaining the images of all ten generators. In particular,
s₁ is the square of a type-V relative root element and s₄ is the nonzero element
of a type-VI relative root group. These equations attach the two root classes to
actual fixed matrices, independently of any involution enumeration.

Source: Parrott (1972), §5, p.683; GLS3, Table 2.4 and §§2.3–2.4;
Aschbacher–Smith 16.1.4 and 16.1.6, printed pp.1171–1172.
-/

public section
noncomputable section
namespace Tits.InvolutionRootGeometry
open ReeF4 ReeF4.DerivedTits

private theorem relations : SatisfiesParrottRelations Realization.assignment := by
  obtain ⟨e, he⟩ := Realization.exists_simpleMatrixComparison
  exact Realization.assignment_relations_of_matrixComparison e
    (Realization.matrixComparison_of_simpleMatrixComparison e he)

private theorem nontrivial_assignment : ∃ i, Realization.assignment i ≠ 1 := by
  obtain ⟨e, he⟩ := Realization.exists_simpleMatrixComparison
  exact Realization.assignment_nontrivial_of_matrixComparison e
    (Realization.matrixComparison_of_simpleMatrixComparison e he)

/-- The specified root and Weyl matrices, as elements of the full fixed group. -/
def fixedGenerator : ParrottGenerator → Model 0 :=
  fixedAssignment Realization.assignment Realization.assignment_fixed

private theorem fixed_relations : SatisfiesParrottRelations fixedGenerator :=
  fixedAssignment_relations _ _ relations

private theorem fixed_nontrivial : ∃ i, fixedGenerator i ≠ 1 := by
  obtain ⟨i, hi⟩ := nontrivial_assignment
  refine ⟨i, fun h => hi ?_⟩
  simpa only [fixedGenerator, toSplitGroup_fixedAssignment, map_one] using
    congrArg (toSplitGroup 0) h

/-- The actual embedding of the presentation into the binary Ree matrix group. -/
def embedding : ParrottGroup →* Model 0 := parrottLift fixedGenerator fixed_relations

theorem embedding_injective : Function.Injective embedding :=
  parrottLift_injective _ _ fixed_nontrivial

theorem embedding_range : embedding.range = commutator (Model 0) :=
  range_eq_commutator_of_card_lt embedding embedding_injective binary_card_lt

/-- The comparison keeps the marked presentation, rather than choosing an
unspecified isomorphism of the two simple groups. -/
@[expose] def derivedEquiv : ParrottGroup ≃* commutator (Model 0) :=
  (MonoidHom.ofInjective embedding_injective).trans (MulEquiv.subgroupCongr embedding_range)

@[simp] theorem derivedEquiv_coe (x : ParrottGroup) :
    (derivedEquiv x : Model 0) = embedding x := rfl

@[simp] theorem embedding_generator (i : ParrottGenerator) :
    embedding (parrottGenerator i) = fixedGenerator i :=
  parrottLift_generator _ _ i

/-- The marking gives an equation of the underlying split matrices. -/
theorem derivedEquiv_generator_matrix (i : ParrottGenerator) :
    toSplitGroup 0 (derivedEquiv (parrottGenerator i) : Model 0) =
      Realization.assignment i := by
  rw [derivedEquiv_coe, embedding_generator]
  exact toSplitGroup_fixedAssignment _ _ i

/-- The type-V root representative in the derived subgroup. -/
@[expose] def longRoot : commutator (Model 0) := derivedEquiv (parrottGenerator .s1)

/-- The type-VI root representative in the derived subgroup. -/
@[expose] def shortRoot : commutator (Model 0) := derivedEquiv (parrottGenerator .s4)

/-- The long representative is the square in the explicit B₂ fixed root block. -/
theorem longRoot_matrix :
    toSplitGroup 0 (longRoot : Model 0) = Realization.quartetElement 0 ^ 2 := by
  rw [longRoot, derivedEquiv_generator_matrix]
  simp [Realization.assignment, Realization.u, pow_two]

/-- The short representative is the explicit commuting-pair fixed root element. -/
theorem shortRoot_matrix :
    toSplitGroup 0 (shortRoot : Model 0) = Realization.pairElement 3 := by
  rw [shortRoot, derivedEquiv_generator_matrix]
  rfl

/-- Long-root class, transported through the marked matrix equivalence. -/
@[expose] def IsLongRoot (x : ParrottGroup) : Prop := IsConj longRoot (derivedEquiv x)

/-- Short-root class, transported through the marked matrix equivalence. -/
@[expose] def IsShortRoot (x : ParrottGroup) : Prop := IsConj shortRoot (derivedEquiv x)

theorem isLongRoot_iff (x : ParrottGroup) :
    IsLongRoot x ↔ IsConj (parrottGenerator .s1) x := by
  constructor
  · intro h
    simpa only [longRoot, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using derivedEquiv.symm.toMonoidHom.map_isConj h
  · intro h
    exact derivedEquiv.toMonoidHom.map_isConj h

theorem isShortRoot_iff (x : ParrottGroup) :
    IsShortRoot x ↔ IsConj (parrottGenerator .s4) x := by
  constructor
  · intro h
    simpa only [shortRoot, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using derivedEquiv.symm.toMonoidHom.map_isConj h
  · intro h
    exact derivedEquiv.toMonoidHom.map_isConj h

end Tits.InvolutionRootGeometry
