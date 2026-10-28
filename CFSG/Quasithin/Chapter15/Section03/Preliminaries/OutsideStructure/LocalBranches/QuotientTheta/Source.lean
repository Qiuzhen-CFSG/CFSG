module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Statements
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.Geometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.SourceData

/-!
# The earlier three-group alternatives used in 15.3.11

These inputs retain all clauses of 15.3.7, including the cyclicity assertions
in its extraspecial branch. The two-core quotient, central inverse image,
prime-to-three residual and natural action image are literal constructions.
The source owner of 15.3.7 must supply this disjunction; it contains no
conclusion about the chosen subgroup Y₊ or the outside intersection M∩I.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7, printed p.1122, used in 15.3.11(5)–(6), pp.1123–1124.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta
open FusionCore.CosetSetup.ExtraspecialLocal
variable {G : Type*} [Group G]

/-- The full alternatives of 15.3.7 as earlier mathematical inputs. -/
def EarlierThreeAlternatives (d : CharacteristicTwo.LocalData G) : Prop :=
  OrdinaryCase d.M d.Y d.V ∨
    (ExtraspecialCase d.M d.Y d.V ∧
      IsCyclic (d.action.image ((d.M ⊓ d.Mc).pCoreIn 2)) ∧
      ∀ P : Sylow 3 ↥(d.M ⊓ d.Mc), IsCyclic P)

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta
end
