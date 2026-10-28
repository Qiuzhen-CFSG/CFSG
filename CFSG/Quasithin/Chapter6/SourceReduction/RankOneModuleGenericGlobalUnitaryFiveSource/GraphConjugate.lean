module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.GraphConjugate
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Conjugated graph centralizers on the published U₅(4) marking

Use the same stored extension and literal base map for a conjugated graph
actor. The conjugating automorphism need not belong to the extension.
The original native subgroups are pulled back explicitly, so the endpoint
and flag fixed subgroups are retained rather than silently replaced.

Source: F.4.29(2) and F.4.37, printed pp.289,293 of refs/quasithin.pdf.
The conjugated-graph equation remains an input; its construction from the
selected outer involution is still required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive.GraphFixed
variable {G : Type*} [Group G] {L K S : Subgroup G} {U : Model 4}

/-- Graph type, when witnessed by an actual conjugating automorphism, gives
the fixed-group order and all marked subgroup intersections on the same E. -/
theorem UnitaryFiveNormalizerMarking.conjugate_graph_inner_centralizer
    (r : UnitaryFiveNormalizerMarking L K S U) (f : r.extension.carrier)
    (b : MulAut U.Carrier) (hf : f.val=b*projectiveAut U.form U.matrix*b⁻¹) :
    let C := r.extension.baseHom.range ⊓ centralizer ({f} : Set r.extension.carrier)
    Nonempty (C ≃* Matrix.PSp4Three.Sp 2 (FixedBy.subfield U.F U.form.conj)) ∧
      Nat.card C=979200 ∧ (∀ P : Sylow 2 C, Nat.card P=256) ∧
      ∀ P : Subgroup U.Carrier,
        ∃ e : (P.comap b.toMonoidHom ⊓ (projectiveAut U.form U.matrix).fixedSubgroup : Subgroup U.Carrier) ≃*
            (P.map r.extension.baseHom ⊓ centralizer ({f} : Set r.extension.carrier) : Subgroup r.extension.carrier),
          ∀ x, (e x).val=r.extension.baseHom (b x.val) := by
  exact ⟨⟨conjugateGraphInnerCentralizerEquiv U r.extension f b hf⟩,
    conjugate_graph_inner_centralizer_card U r.extension f b hf,
    conjugate_graph_inner_centralizer_sylow_card U r.extension f b hf,
    fun P => ⟨conjugateGraphFixedSubgroupEquiv U r.extension f b hf P,
      conjugateGraphFixedSubgroupEquiv_apply U r.extension f b hf P⟩⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
