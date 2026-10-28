module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.GraphSymplectic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# The graph inner centralizer on the published U₅(4) marking

Apply the actual fixed-group equivalence and order calculation to the
extension stored in the original full-normalizer marking. The graph element
and the inner base map belong to this same carrier. The conclusion identifies
only the inner intersection of its centralizer. Selecting the graph element
from S<T and proving ambient Sylow placement remain the F.4.37--38 obligations.

Source: Aschbacher--Smith F.4.37(1) and the order comparison before F.4.38,
printed pp.293--294 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive.GraphFixed
variable {G : Type*} [Group G] {L K S : Subgroup G} {U : Model 4}

/-- Exact inner fixed group and its two-part on the same marked extension.
The displayed graph-element equation is retained as a local input. -/
theorem UnitaryFiveNormalizerMarking.graph_inner_centralizer
    (r : UnitaryFiveNormalizerMarking L K S U) (f : r.extension.carrier)
    (hf : f.val=projectiveAut U.form U.matrix) :
    let C := r.extension.baseHom.range ⊓ centralizer ({f} : Set r.extension.carrier)
    Nonempty (C ≃* Matrix.PSp4Three.Sp 2 (FixedBy.subfield U.F U.form.conj)) ∧
      Nat.card C=979200 ∧ ∀ P : Sylow 2 C, Nat.card P=256 := by
  exact ⟨⟨graphInnerCentralizerEquiv U r.extension f hf⟩,
    graph_inner_centralizer_card U r.extension f hf,
    graph_inner_centralizer_sylow_card U r.extension f hf⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
