module

public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.Envelope
public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.AbsolutelyIrreducible

/-!
# Geometric predicates for maximal irreducible subgroups of PSU₄(3)

All actions below are actions of the full SU preimage on the defining space.
An imprimitivity system is an internal direct sum of nonzero subspaces permuted
by that action. Absolute irreducibility uses scalar extension to an algebraic
closure, as in the representation API; it is not inferred from irreducibility.

These definitions separate the geometric cases in the proper-section obligation
of Aschbacher–Smith, Theorem 0.1.2(4), condition K, printed pp.4 and 482 of
`refs/quasithin.pdf`. The matrix conventions are those of GLS3, §2.7.
-/

public noncomputable section
namespace CFSG.Quasithin.MainConverse.UnitaryFourIrreducible

open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

/-- The defining representation of the full scalar preimage. -/
@[expose] def liftedRepresentation (U : Subgroup (Carrier 4)) :
    Representation FiniteField.Nine (fullPreimage U) (Fin 4 → FiniteField.Nine) :=
  (Representation.generalLinearNatural 4).comp
    ((form 4).specialSubgroup.subtype.comp (fullPreimage U).subtype)

theorem liftedRepresentation_apply (U : Subgroup (Carrier 4))
    (g : fullPreimage U) (v : Fin 4 → FiniteField.Nine) :
    liftedRepresentation U g v = g.val.val.val.mulVec v := rfl

theorem liftedRepresentation_injective (U : Subgroup (Carrier 4)) :
    Function.Injective (liftedRepresentation U) :=
  (Representation.generalLinearNatural_injective 4).comp
    (Subtype.val_injective.comp Subtype.val_injective)

/-- The source invariant-subspace test is exactly irreducibility of the lift. -/
theorem liftedRepresentation_isIrreducible (U : Subgroup (Carrier 4))
    (hred : ¬ IsReducible U) : Representation.IsIrreducible (liftedRepresentation U) := by
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · exact ⟨⟨⊥, ⊤, fun h => bot_ne_top
      (congrArg Subrepresentation.toSubmodule h)⟩⟩
  · intro W
    by_cases hW0 : W.toSubmodule = ⊥
    · exact Or.inl (Subrepresentation.toSubmodule_injective hW0)
    by_cases hW1 : W.toSubmodule = ⊤
    · exact Or.inr (Subrepresentation.toSubmodule_injective hW1)
    exfalso
    apply hred
    refine ⟨W.toSubmodule, hW0, hW1, ?_⟩
    intro g hg v hv
    exact W.apply_mem_toSubmodule ⟨g, hg⟩ hv

/-- A nontrivial direct-sum decomposition permuted by the lifted group.
No nondegeneracy or orthogonality of its summands is assumed. -/
@[expose] def IsImprimitive (U : Subgroup (Carrier 4)) : Prop :=
  ∃ (r : ℕ) (W : Fin r → Submodule FiniteField.Nine (Fin 4 → FiniteField.Nine)),
    1 < r ∧ (∀ i, W i ≠ ⊥) ∧ iSupIndep W ∧ (⨆ i, W i) = ⊤ ∧
      ∀ g : fullPreimage U, ∃ σ : Equiv.Perm (Fin r),
        ∀ i, (W i).map (liftedRepresentation U g) = W (σ i)

/-- The action permutes the lines of an actual basis over F₉. -/
@[expose] def IsMonomial (U : Subgroup (Carrier 4)) : Prop :=
  ∃ b : Module.Basis (Fin 4) FiniteField.Nine (Fin 4 → FiniteField.Nine),
    ∀ g : fullPreimage U, ∃ σ : Equiv.Perm (Fin 4),
      ∀ i, ∃ a : FiniteField.Nine, a ≠ 0 ∧
        liftedRepresentation U g (b i) = a • b (σ i)

end CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
