module
public import CFSG.Quasithin.ChapterB.Section05.DualNumerical.SmallSupport
public import CFSG.Quasithin.ChapterB.Section05.DualNumerical.Hyperplane
public import CFSG.Quasithin.ChapterB.Section05.DualNumerical.OuterSixThree
public import CFSG.Quasithin.ChapterB.Section05.DualNumerical.ProductComplete
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.Quasisimple
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
/-!
# Assembling the source B.5.13 numerical alternatives

Strong induction on the finite nontrivial actor combines the five literal
adequate B.5 alternatives. The two-factor branch recurses only on a nontrivial
factor of strictly smaller order, retaining the original full module.
All model, extension, splitting and numerical branch inputs are proved.
The sole classifier premise is instantiated by the full known-simple source
classification in `DualNumerical.Complete`.

Source: Aschbacher--Smith B.5.13, printed pp.110--112.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceB513
open SourceInduction
universe u v

/-- The complete numerical induction over the actual adequate source classifier. -/
theorem quadraticRatio_le_two_of_adequateClassification
    {K : GroupClass.{u}} (hclass : AdequateClassificationInput.{u,v} K)
    {D : Type u} [Group D] [Finite D] [Nontrivial D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (h : FFHypothesis K ρ.dual) :
    quadraticRatio ρ ≤ 2 := by
  suffices hall : ∀ n : ℕ, ∀ (D : Type u) [Group D] [Finite D] [Nontrivial D],
      Nat.card D = n → ∀ (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
      [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V),
      FFHypothesis K ρ.dual → quadraticRatio ρ ≤ 2 by
    exact hall (Nat.card D) D rfl V ρ h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro D _ _ _ hcard V _ _ _ ρ h
    have hc := (hclass D (Module.Dual (ZMod 2) V) ρ.dual h).of_nontrivial ρ.dual
    rcases hc with ⟨hqs,c⟩ | ⟨c⟩ | ⟨c⟩ | ⟨c⟩ | ⟨c⟩
    · exact quadraticRatio_le_two_of_quasisimple_source ρ h hqs c
    · exact quadraticRatio_le_two_of_dual_symmetricThree ρ c
    · apply quadraticRatio_le_two_of_twoFactors_source_nontrivial ρ h c
      intro A _ hlt hh
      exact ih (Nat.card A) (hcard ▸ hlt) A rfl V (ρ.comp A.subtype) hh
    · exact quadraticRatio_le_two_of_outerSixThree_source ρ h c
    · exact quadraticRatio_le_two_of_hyperplane_source ρ h c

end CFSG.Quasithin.ChapterB.SourceB513
