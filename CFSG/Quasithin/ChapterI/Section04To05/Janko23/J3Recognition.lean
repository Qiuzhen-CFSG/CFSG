module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.LocalStructure
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.ModelRelations
public import Theory.SpecificGroups.Janko3.Model.Order

/-!
# Presentation comparison for the J₃ recognition argument

Aschbacher–Smith, *The Classification of Quasithin Groups*, I.4.7(2),
printed p. 418, requires an actual equivalence from a group of type J₃ to
the concrete J₃ model. This module proves the final comparison step for
the ATLAS standard-generator presentation: two generated quotients whose
orders reach the presentation's upper bound are isomorphic. The concrete
quotient and its order are proved, rather than supplied as assumptions.

The remaining inputs are explicit: finiteness and an order upper bound for
the abstract presentation, and a generating pair and order lower bound
for the source group. The centralizer-index variant uses the already proved
order 1920 of the source involution centralizer. These conditional results
do not assert I.4.7(2); its local-to-presentation argument remains necessary.

Source routes: Janko, *Some new simple groups of finite order, I* (1968),
and Higman–McKay, *On Janko's simple group of order 50,232,960* (1969).
The precise eight relators used here are those of ATLAS `J3G1-P1`, as
documented in `Theory.SpecificGroups.Janko3.RecognitionPresentation.Basic`.
-/

namespace CFSG.Quasithin.Janko23.J3Recognition

open Sporadic.Janko3.RecognitionPresentation

variable {G : Type*} [Group G]

/-- The finite presentation's upper bound makes its concrete evaluation faithful. -/
public theorem model_evaluation_bijective [Finite Presentation]
    (hbound : Nat.card Presentation ≤ 50232960) :
    Function.Bijective (evaluation model_satisfies) := by
  apply evaluation_bijective_of_card_le model_satisfies Sporadic.Janko3.generators_closure
  rwa [Sporadic.Janko3.model_card]

/-- Compare a generated quotient with the actual ATLAS permutation model.
The source structure and presentation enumeration must supply the three premises. -/
public theorem recognition_of_generators [Finite Presentation]
    (hgen : HasGenerators G) (hcard : 50232960 ≤ Nat.card G)
    (hbound : Nat.card Presentation ≤ 50232960) :
    Nonempty (G ≃* Sporadic.Janko3.Model) := by
  obtain ⟨a, b, hab, hrel⟩ := hgen
  exact ⟨equivOfCardBounds hrel model_satisfies hab Sporadic.Janko3.generators_closure
    (hbound.trans hcard) (by rwa [Sporadic.Janko3.model_card])⟩

/-- In the source local setup, the required order lower bound follows from
an involution-centralizer index of at least 26163. -/
public theorem recognition_of_generators_of_centralizer_index [Finite G]
    [Finite Presentation] {z : G} (hlocal : HTypeAt z)
    (hgen : HasGenerators G) (hindex : 26163 ≤ (involutionCentralizer z).index)
    (hbound : Nat.card Presentation ≤ 50232960) :
    Nonempty (G ≃* Sporadic.Janko3.Model) := by
  apply recognition_of_generators hgen ?_ hbound
  calc
    50232960 = 26163 * 1920 := by decide
    _ ≤ (involutionCentralizer z).index * Nat.card (involutionCentralizer z) := by
      rw [hlocal.centralizer_card]
      exact Nat.mul_le_mul_right 1920 hindex
    _ = Nat.card G := (involutionCentralizer z).index_mul_card

end CFSG.Quasithin.Janko23.J3Recognition
