module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceCompletion
public import BenderSuzuki.ZD.Recognition.NativeSource

/-!
# Aschbacher's Lemma 3.4

The full finite-group Theorem ZD discharges the last source input in the
completed fusion and induction proof. Every original closure condition and
all three conclusions remain unchanged, including strong embedding in the
actual normal closure and the dihedral/semidihedral exceptional alternative.

Source: Aschbacher, On finite groups of component type (1975), Lemma 3.4,
printed pp.94--96; GLS IV, Chapter 2, Theorem ZD.
-/

public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
universe u

/-- The exact universally quantified ZD source input is now proved. -/
theorem theoremZD : TheoremZD.{u} := BenderSuzuki.ZD.theorem_ZD

/-- Full Lemma 3.4 from its original hypotheses, with every earlier-source
input discharged. -/
theorem lemma_3_4_source
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (A₁ A₂ : Subgroup G) (h : Hypotheses S A₁ A₂) :
    Conclusion A₁ A₂ :=
  lemma_3_4 theoremZD S A₁ A₂ h

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
