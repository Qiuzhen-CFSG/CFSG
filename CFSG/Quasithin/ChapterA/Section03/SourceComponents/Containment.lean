module

public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Containment.Core

/-!
# The unique-containment assertion of A.3.12

Generation puts the local C-component B in the ambient C-component layer.
Exact intersections with the full ambient Sylow generate its Sylow intersection.
If no component contains B, A.3.3(7), applied in the original group B sup T,
puts every factor commutator in that group's solvable radical. The actual
Sylow image in B/Rad(B) would then be central, contrary to its even order
and nonabelian simplicity. Distinct containing components commute, so
perfectness of B proves uniqueness.

The universal earlier Theorem A and simple SQTK outer/parity inputs remain
explicit. This proves the first assertion of A.3.12 independently of its
22 proper-embedding cases. The full Sylow hypothesis is essential.

Source: Aschbacher--Smith, Proposition A.3.12, printed pp.47--48,
combined manuscript of 1 March 2004.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every local C-component for the original ambient Sylow lies in a unique ambient C-component. -/
theorem containment
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hSimple : ∀ (S : Type u) [Group S] [Finite S],
      IsSimpleGroup S → ¬ IsMulCommutative S → IsSQTK KnownSimple.IsKnownSimple S →
        Group.IsSolvable (MulAut.Outer S) ∧ Even (Nat.card S))
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents T) :
    ∃! L : Subgroup G, L.IsCComponent ∧ B ≤ L :=
  ContainmentCore.containment hA hSimple hG hO T B hB

end CFSG.Quasithin.ChapterA.Section03.SourceComponents
