module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Transport
public import Theory.Representation.BinaryOffender.SectionLinear

/-!+# The two remaining nonsplit proof branches

`OrdinarySecondFactor` records precisely the natural and doubled-natural
constructors of the supplied B.5.11 factor conclusion. The elementary case
split below retains the alternative full four-dimensional source record.
Neither definition asserts the missing cohomology comparison or splitting.

The authorized earlier B.4.8(4) input is stated separately, on a faithful
indecomposable action with a literal chief series. Exactly one section is
noncentral and has the actual natural SL₃(2) action; every other section is
central. Its conclusion is dimension three or four. This input does not
assert a splitting of the present representation. Deriving that splitting
remains the exceptional-branch obligation. The earlier theorem's source
owner is qt-b-04-natural-extensions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(4),
printed p.91, and the nonsplit B.5.6 endgame, printed p.110.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
open ComponentReduction
universe u v

/-- A chief series with exactly one noncentral factor, carrying a natural
three-dimensional action under an actual identification of the whole actor. -/
def UniqueNoncentralNaturalFactor {D : Type u} [Group D]
    {U : Type v} [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) D U) : Prop :=
  ∃ (n : ℕ) (c : ℕ → Subrepresentation σ) (i : ℕ),
    Monotone c ∧ c 0 = ⊥ ∧ c n = ⊤ ∧
    (∀ j < n, c j ⋖ c (j + 1)) ∧ i < n ∧
    IsLinearNatural (sectionRepresentation σ (c i) (c (i + 1))) BinaryField.two 3 ∧
    ∀ j < n, j ≠ i → ∀ g w, sectionRepresentation σ (c j) (c (j + 1)) g w = w

/-- Full B.4.8(4)'s dimension assertion. In particular no FF or generation
hypothesis is added, and no fixed-supplement assertion replaces its conclusion. -/
def EarlierB48Four : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (U : Type v) [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (σ : Representation (ZMod 2) D U),
    Function.Injective σ → IsIndecomposable σ →
    Nonempty (D ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    UniqueNoncentralNaturalFactor σ →
      Module.finrank (ZMod 2) U = 3 ∨ Module.finrank (ZMod 2) U = 4

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The actual action on the factor's image in its own fixed quotient. -/
noncomputable abbrev secondFactorAction (c : Conclusion ρ)
    (f : FactorModuleConclusion (secondAction c)) :=
  (((fixed (secondAction c)).quotientImage f.space).toRepresentation.comp
    (⊤ : Subgroup (second c)).subtype)

/-- The two ordinary B.5.11 factor constructors, before cohomological
restrictions are imposed. The moved equality is on V₂, not on V. -/
def OrdinarySecondFactor (c : Conclusion ρ)
    (f : FactorModuleConclusion (secondAction c)) : Prop :=
  f.space.toSubmodule = moved (secondAction c) ⊤ ∧
    (FactorNatural (secondFactorAction c f) ∨
      ∃ F : BinaryField, Odd F.degree ∧
        IsRepeatedLinearNatural (secondFactorAction c f) F 3 2)

/-- Exhaust the supplied factor conclusion without identifying either
branch with a proved nonsplit source theorem. -/
theorem factor_cases (c : Conclusion ρ) (f : FactorModuleConclusion (secondAction c)) :
    OrdinarySecondFactor c f ∨ Nonempty (FourDimensionalSource (secondFactorAction c f)) := by
  cases f.actionCase with
  | natural hm hn => exact Or.inl ⟨hm,Or.inl hn⟩
  | doubleNatural F ho hm hn => exact Or.inl ⟨hm,Or.inr ⟨F,ho,hn⟩⟩
  | exceptional _ q => exact Or.inr ⟨q⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
