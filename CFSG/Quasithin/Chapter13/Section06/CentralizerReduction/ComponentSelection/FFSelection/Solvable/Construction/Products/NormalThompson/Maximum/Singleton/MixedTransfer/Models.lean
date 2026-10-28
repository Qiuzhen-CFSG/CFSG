module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.Images
public import Theory.Representation.SL2NaturalOffenders.NoStrong
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd
public import Theory.Representation.BinaryOffender.Replacement

/-!
# Complementary native actions without strong offenders

The natural SL₂ and S₅ actions have no strong offenders. The exceptional
four-dimensional clause includes the source ratio one, which gives the same
conclusion by quadratic replacement. All transports use the actor equivalence
and linear intertwiner in the native clause. Thus only the single and doubled
natural SL₃ actions remain outside the sharp global-maximum reduction.

The parent MixedTransfer module applies this exhaustive reduction to the
original star action and selects actual sharp global maxima. Maximum transfer
to the selected full preimage is still required.

Source: Aschbacher–Smith B.3.2, B.4.2(1), B.4.8(3), B.5.6(3), and 13.6.13,
printed pp.83–86, 91, 105 and 929.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.SourceInduction CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.Models
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) D V)

omit [Finite D] [Module.Finite (ZMod 2) V] in
private theorem not_strong_of_actionEquiv
    {B W : Type*} [Group B] [Finite B] [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] {σ : Representation (ZMod 2) B W}
    (e : ActionEquiv ρ σ) (hσ : ¬ IsStrongFFModule σ) : ¬ IsStrongFFModule ρ := by
  rintro ⟨A, hA⟩
  refine hσ ⟨A.map e.groupEquiv.toMonoidHom,
    (IsOffender.map_equivariant ρ σ e.groupEquiv.toMonoidHom e.groupEquiv.injective
      e.linearEquiv e.intertwines ⟨hA.1, hA.2.le⟩).1, ?_⟩
  rw [← fixedCodim_map_equivariant ρ σ e.groupEquiv.toMonoidHom
    e.linearEquiv e.intertwines A, rank_map_injective _ e.groupEquiv.injective]
  exact hA.2

omit [Finite D] [Module.Finite (ZMod 2) V] in
/-- The native natural SL₂ clause supplies the no-strong-offender hypothesis. -/
theorem linearTwo_not_strong (F : BinaryField) (h : IsLinearNatural ρ F 2) :
    ¬ IsStrongFFModule ρ := by
  exact not_strong_of_actionEquiv ρ h.some
    (Representation.SL2NaturalOffenders.NoStrong.natural_not_strong (F := F.Carrier))

omit [Finite D] [Module.Finite (ZMod 2) V] in
/-- The native five-point natural action has no strong offenders. -/
theorem symmetricFive_not_strong (h : IsSymmetricNatural ρ 5) :
    ¬ IsStrongFFModule ρ := by
  apply not_strong_of_actionEquiv ρ h.some
  rintro ⟨A, hA⟩
  exact CFSG.Quasithin.ChapterB.Offenders.Odd.not_isStrongOffender_natural
    (Or.inl rfl) A hA

/-- Keep the exceptional source ratio clause; it also excludes nonquadratic
strong offenders, by the proved replacement theorem. -/
theorem exceptional_not_strong (h : FourDimensionalSource ρ) :
    ¬ IsStrongFFModule ρ := by
  rw [isStrongFFModule_iff_quadraticRatio_lt_one, h.ratio]
  exact lt_irrefl _

/-- An actual native single or doubled natural SL₃ action on the specified
quotient summand. The field, moved-space identity and intertwiner are retained. -/
def LinearThreeFactor (A : Subgroup D) (U : Subrepresentation ρ) : Prop :=
  let σ := ((fixed ρ).quotientImage U).toRepresentation.comp A.subtype
  ∃ F : BinaryField, Odd F.degree ∧ U.toSubmodule = moved ρ A ∧
    (IsLinearNatural σ F 3 ∨ IsRepeatedLinearNatural σ F 3 2)

/-- The only native complementary clauses still needing analysis are the
single and doubled natural SL₃ actions. No group-family tag replaces the action. -/
theorem sourceFactor_nonstrong_or_linearThree
    (A : Subgroup D) (U : Subrepresentation ρ) (h : SourceFactorCase ρ A U) :
    let σ := ((fixed ρ).quotientImage U).toRepresentation.comp A.subtype
    (¬ IsStrongFFModule σ) ∨ LinearThreeFactor ρ A U := by
  intro σ
  cases h with
  | natural hm h =>
    cases h with
    | linearTwo F h => exact Or.inl (linearTwo_not_strong σ F h)
    | symmetricFive h => exact Or.inl (symmetricFive_not_strong σ h)
    | linearThree F ho h => exact Or.inr ⟨F, ho, hm, Or.inl h⟩
  | doubleNatural F ho hm h => exact Or.inr ⟨F, ho, hm, Or.inr h⟩
  | exceptional _ h => exact Or.inl (exceptional_not_strong σ h)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.Models

end
