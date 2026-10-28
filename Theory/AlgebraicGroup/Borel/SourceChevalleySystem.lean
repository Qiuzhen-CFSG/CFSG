module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_11_4
public import Theory.AlgebraicGroup.RootData.Chevalley

/-!
This module converts the source-form Chevalley relation package into the
uniform `IsChevalleySystem` interface.  The conversion is projection-only:
the source package contains all fields of the target, plus torus generation;
its reflection package supplies the three conjugation relations and the sign
condition.  The coroot word uses the source convention
`h α t = n α 1⁻¹ * n α t`.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem SourceChevalleyRelations.toIsChevalleySystem
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (h : SourceChevalleyRelations D C P e base) :
    IsChevalleySystem D C P e base := by
  let hr := h.reflection_relations.some
  exact ⟨
    (fun α => h.parametrizes_root_subgroups α),
    (fun α t => h.normalizer_word α t),
    (fun α t => h.coroot_word α t),
    (fun α t u => h.root_addition α t u),
    (fun α β hab => h.commutator_formula α β hab),
    (fun α β t u => h.coroots_commute α β t u),
    (fun α t u => h.coroot_multiplication α t u),
    (by simpa [sourceFundamentalCorootWord] using h.coroot_expansion),
    (by simpa [sourceFundamentalCorootWord] using h.universal_coroot_independence),
    (by simpa [sourceFundamentalCorootWord] using h.adjoint_coroot_relations),
    (by simpa [sourceFundamentalCorootWord] using h.general_coroot_relations),
    (fun α β t u => h.torus_conjugates_root_elements α β t u),
    ⟨hr.sign, hr.sign_is_unit_sign, hr.conjugates_root_elements,
      hr.conjugates_coroots, hr.conjugates_normalizer_words⟩,
    h.normalizer_square⟩

end Theory.AlgebraicGroup
