module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models.Exclusion
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Sections

/-!
# The G.6.4 contradiction on a surviving exceptional chief section

The existing chief-section representation supplies every genuine G.6.4
hypothesis. The literal exceptional component image excludes every resulting
model, including the odd-by-SL₂ branch. This finishes the model-comparison
part of the last paragraph of 11.5.8.

Constructing the section and its moved seed remains with
qt-d-1222-amalgam-chief-section. The relative-component and surviving-case
premises are supplied by qt-d-1222-natural-relative-components and
qt-d-1222-shadow-component-triangle; the parent
qt-d-1222-natural-closure-amalgam discharges OddPair existence in the final
K=L₁ argument. The theorem below is explicitly conditional and is not an
unconditional statement of 11.5.8.
Source: Aschbacher--Smith, 11.5.8, printed p.784, and G.6.4, pp.345--346.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D) (g : G)

/-- The actual G.6.4 consumer, conditional only on the outstanding surviving
chief section and its moved seed. The earlier relative-component and surviving
case statements retain their original source producers. -/
theorem false_of_surviving_chief_section [IsElementaryAbelian 2 (localClosure E)]
    (h : LocalInputs E) (hab : IsMulCommutative E.W)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞))
    (hp : E.point ≠ ⊥) (p : OddPair E g)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hcase : Source.ClassicalRefinementCase L E.L₁ E.K 1 E.input.field.degree)
    (A B : Subrepresentation (action E g)) (hAB : A ⋖ B)
    (hF : ¬ markedFitting E g ≤ (sectionRepresentation (action E g) A B).ker)
    (v : V) (hv : seed E g p v ∉ (sectionRepresentation (action E g) A B).ker) : False := by
  have hc := chief_classification E g h hab hs hp p A B hAB v hv
  exact chief_model_exclusion E g h hK hlt hcase A B hAB hF _ hc

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models
