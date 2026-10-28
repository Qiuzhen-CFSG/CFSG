module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Contracts
public import CFSG.Quasithin.Chapter3.Defs
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Remaining original local inputs to 12.4.1

The geometric and weak-closure implications are proved in the companion
modules. Their original application needs an escaping H-star subgroup and
the parameter bound on the literal V_H = ⟨Ω₁(Z(T))ᴴ⟩. These propositions
specify those producer obligations without assuming a conjugator, parity,
weak-closure containment or a commutator plane.

The first obligation also retains s(G,V)>1, so no unproved multiple-local
standing assumption is silently added to the public 12.4.1 contract. The
second applies to any original H-star member and is independent of its
selection. Its source is 12.3.2 followed by E.4.1 and the A₅ calculation.
Source: Aschbacher–Smith, 12.3.2 and 12.4.1, printed pp.807,812.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02 SmallFusion ChapterE
universe u
variable {G : Type u} [Group G]

/-- The actual Omega-center seed, not the fixed subgroup C_V(L). -/
abbrev sylowCenterSeed (T : Sylow 2 G) : Subgroup G :=
  omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype)

/-- The original module V_H, generated in G by the H-conjugates of Z. -/
def localModule (T : Sylow 2 G) (H : Subgroup G) : Subgroup G :=
  conjugateSpanBy (sylowCenterSeed T) H

/-- Relative normality of the actual local span. -/
theorem localModule_normalized (T : Sylow 2 G) (H : Subgroup G) :
    H ≤ normalizer (localModule T H : Set G) :=
  le_normalizer_conjugateSpanBy _ _

/-- The precise local consequences used by the weak-closure argument.
The parameter is for the faithful image of H acting on the whole V_H. -/
structure LocalParameterData (T : Sylow 2 G) (H : Subgroup G) : Prop where
  elementary : IsElementaryAbelian 2 (localModule T H)
  centralizer_le_core : H ⊓ centralizer (localModule T H : Set G) ≤ H.pCoreIn 2
  parameter : letI := elementary
    moduleA ((automizerRepresentation (localModule T H)).comp
      (inducedAutomizer (localModule T H) H).subtype) ≤ 1

/-- Selection of the original escaping local subgroup. The permitted
earlier 12.2 implications are supplied by the eventual producer theorem. -/
def LocalSelectionSource : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    centralizer (sylowCenterSeed T : Set X) ≤ normalizer (L : Set X) →
    letI := D.elementary
    1 < globalS V →
      ∃ H : Subgroup X, H ∈ Chapter3.HStar (T : Subgroup X) (normalizer (L : Set X))

/-- The 12.3.2/E.4.1 application on each actual local module.
No bound on the full ambient automizer of V_H is requested. -/
def LocalParameterSource : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → ChosenModule T L V →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    centralizer (sylowCenterSeed T : Set X) ≤ normalizer (L : Set X) →
    ∀ H : Subgroup X, H ∈ Chapter3.HStar (T : Subgroup X) (normalizer (L : Set X)) →
      LocalParameterData T H

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
