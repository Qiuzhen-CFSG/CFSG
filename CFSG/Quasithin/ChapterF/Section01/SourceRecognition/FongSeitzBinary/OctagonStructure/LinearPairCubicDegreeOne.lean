module

public import Theory.GroupTheory.TwoCubicSubgroupsCardinality
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicTerminalInput

/-!
# The degree-one counting leaf for the octagon terminal argument

This is the exact finite-group calculation used in the `a = 1` paragraph of
Fong--Seitz I (6G), printed p.50.  The two order-three factors and their
placement in the actual Cartan are kept as hypotheses: the checked terminal
input constructs only the cubic actor and the perpendicular product, and does
not yet construct these two independent factors.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure

variable {X : Type*} [Group X] [Finite X]

/-- Source-facing degree-one contradiction once the two marked cubic factors
have been constructed inside the actual Cartan. -/
theorem degree_one_cartan_contradiction
    (H A B : Subgroup X)
    (hAH : A ≤ H) (hBH : B ≤ H)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hdisj : Disjoint A B)
    (hcomm : A ≤ centralizer (B : Set X))
    (hH : Nat.card H = 3) :
    False := by
  exact Theory.GroupTheory.not_card_three_of_disjoint_commuting_cubic
    H A B hAH hBH hA hB hdisj hcomm hH

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure

