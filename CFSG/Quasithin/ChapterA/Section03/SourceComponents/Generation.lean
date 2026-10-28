module

public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation.Core
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# A.3.9(1): generation of the solvable residual

The original ambient C-components are normal in the perfect residual by the
proved orbit bound. Their simple solvable-radical quotients are SQTK by the
genuine semisimple-section assertion of Theorem A. Solvability of the actual
outer groups supplies component supplements to the action kernels. Successive
factor adjustment and the own-kernel contradiction make the common kernel
solvable, so the C-component layer is the entire residual.

Only universal Theorem A and the explicit outer-solvability/even-order theorem
for nonabelian simple SQTK groups remain as earlier-source inputs. The known
simple class here is the full carrier catalogue. No ordinary-cover classification,
generation assertion or solvability of an action kernel is assumed.

Source: Aschbacher--Smith, Proposition A.3.9(1), printed p.46,
combined manuscript of 1 March 2004.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source generation assertion, at the full known-simple K-group boundary. -/
theorem generation
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hSimple : ∀ (S : Type u) [Group S] [Finite S],
      IsSimpleGroup S → ¬ IsMulCommutative S → IsSQTK KnownSimple.IsKnownSimple S →
        Group.IsSolvable (MulAut.Outer S) ∧ Even (Nat.card S))
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥) :
    cComponentLayer G = solvableResidual G :=
  GenerationCore.generation hA hSimple hG hO

end CFSG.Quasithin.ChapterA.Section03.SourceComponents
