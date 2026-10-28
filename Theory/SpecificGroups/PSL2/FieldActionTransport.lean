module

public import Theory.SpecificGroups.PSL2.FieldActionComparison
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws

/-!
# Field transport preserves the actual projective coefficient action

An intertwining ring equivalence intertwines entrywise matrix maps. Descending
that identity through the scalar center preserves the literal PSL₂ field action.
This is used to lift source field witnesses into the universe of the ambient
finite group without losing the Frobenius conjugation formula.
-/

public section
open scoped MatrixGroups
namespace Theory.PSL2

theorem projectiveFieldAutHom_fieldEquiv
    {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) (σ : F ≃+* F) (τ : K ≃+* K)
    (h : ∀ x, e (σ x) = τ (e x)) (x : PSL(2,F)) :
    Atlas.fieldEquivPSL 2 e (OuterSolvable.projectiveFieldAutHom σ x) =
      OuterSolvable.projectiveFieldAutHom τ (Atlas.fieldEquivPSL 2 e x) := by
  obtain ⟨A,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2,F)) x
  simp only [projectiveFieldAutHom_eq_psl2FieldAut, GorensteinWalter.psl2FieldAut_apply,
    GorensteinWalter.psl2RingEquiv_mk, Atlas.fieldEquivPSL_mk]
  congr 1
  ext i j
  exact h (A i j)

end Theory.PSL2
