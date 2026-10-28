module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionNumericalSize
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSelectionAssembly

/-!
# Cyclic-block assembly with the numerical extraspecial argument discharged

The numerical reduction in 12.2.23 now proves p=d=3 and |W|=64 from the
literal invariant odd analysis and its Frattini fixed-point hypothesis.
The prime-order consumer and cyclic-block consumer below apply that theorem
on the original groups. The latter also supplies the previously proved
core centralization and normality facts to the terminal argument.

Nonprime invariant selection and the final component-module contradiction
remain explicit source obligations owned by qt-d-12213-cyclic-block. These
conditional applications do not assert the unconditional source theorem.
Source: Aschbacher–Smith, 12.2.21–24, printed pp.802–804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}

/-- The numerical callback in 12.2.23 is discharged; only its terminal
extraspecial contradiction remains. -/
theorem prime_order_of_extraspecial_terminal
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    {p : ℕ} {H P U W : Subgroup G} {g v : G}
    (S : InvariantOddLocalAnalysis T L V d p H P U W g v) (hnone : NoEscape L V)
    (terminal : IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      p = 3 → d = 3 → Nat.card W = 64 → False) : Nat.card P = p := by
  apply prime_order_of_extraspecial_steps D A S hnone _ terminal
  intro he _ _ hf
  exact S.extraspecial_numerical_reduction D A hTV he hf

/-- The original cyclic-block consumer with only nonprime invariant selection
and the terminal component-module contradiction still outstanding. -/
theorem cyclicLocalAnalysis_of_nonprime_selection_and_terminal_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (selectionStep : ∀ p H P U g, CyclicConstructionSeed T L V d p H P U g →
      Nat.card P ≠ p → ∃ P' U' g' v, CyclicInvariantSelection T L V d p H P' U' g' v)
    (terminal : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v →
      IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      p = 3 → d = 3 → Nat.card W = 64 →
      W ≤ centralizer (H.pCoreIn 2 : Set G) →
      H ≤ normalizer (((frattini P).map P.subtype ⊔ W : Subgroup G) : Set G) →
      H ≤ normalizer ((H.pCoreIn 2 ⊓ centralizer
        (((frattini P).map P.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) →
      False) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U := by
  have hTV := ((structural G T L h).2.2 V D).1
  apply cyclicLocalAnalysis_of_nonprime_selection_and_extraspecial_steps
    h D structural A hnone hTI selectionStep
  · intro p H P U W g v S he _ _ hf
    exact S.extraspecial_numerical_reduction D A hTV he hf
  · intro p H P U W g v S he hc hx hf hp hd hW
    exact terminal p H P U W g v S he hc hx hf hp hd hW
      (S.extraspecial_binary_three_module_centralizes_core A he hc hf hp hW)
      (S.extraspecial_frattini_module_normal he)
      (S.extraspecial_binary_three_core_centralizer_normal A he hc hf hp hW)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
