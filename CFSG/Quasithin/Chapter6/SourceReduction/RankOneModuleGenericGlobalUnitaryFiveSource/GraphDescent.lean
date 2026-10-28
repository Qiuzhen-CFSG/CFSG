module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.GraphDescent
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.GraphConjugate

/-!
# Unitary graph-twist descent on the original full-normalizer marking

An involution with an actual unitary graph-twist formula has a constructed
graph conjugator. Applying graph transport on the same stored extension
identifies its inner centralizer with Sp₄(4), and carries every native
subgroup through the literal base map. The pulled-back subgroups explicitly
retain the parabolic flag rather than identifying it with a standard flag.

Source: F.4.29(2) and F.4.37, printed pp.289,293 of refs/quasithin.pdf.
The representation formula for the selected abstract actor remains unproved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive.Descent Theory.SpecificGroups.UnitaryFive.GraphFixed
variable {G : Type*} [Group G] {L K S : Subgroup G} {U : Model 4}

/-- Descent supplies the conjugator and the fixed-group transport together,
on the same marking and base map, from a concrete unitary-twist formula. -/
theorem UnitaryFiveNormalizerMarking.unitary_twist_inner_centralizer
    (r : UnitaryFiveNormalizerMarking L K S U) (f : r.extension.carrier)
    (hf2 : f^2=1) (u : U.form.unitarySubgroup)
    (hf : f.val=unitaryConj U.form u*projectiveAut U.form U.matrix) :
    ∃ v : U.form.unitarySubgroup,
      let b := unitaryConj U.form v
      f.val=b*projectiveAut U.form U.matrix*b⁻¹ ∧
      let C := r.extension.baseHom.range ⊓ centralizer ({f} : Set r.extension.carrier)
      Nonempty (C ≃* Matrix.PSp4Three.Sp 2 (FixedBy.subfield U.F U.form.conj)) ∧
        Nat.card C=979200 ∧ (∀ P : Sylow 2 C, Nat.card P=256) ∧
        ∀ P : Subgroup U.Carrier,
          ∃ e : (P.comap b.toMonoidHom ⊓ (projectiveAut U.form U.matrix).fixedSubgroup : Subgroup U.Carrier) ≃*
              (P.map r.extension.baseHom ⊓ centralizer ({f} : Set r.extension.carrier) : Subgroup r.extension.carrier),
            ∀ x, (e x).val=r.extension.baseHom (b x.val) := by
  obtain ⟨v,hv⟩ := exists_graph_conjugator_of_unitary_twist U r.extension f hf2 u hf
  exact ⟨v,hv,r.conjugate_graph_inner_centralizer f (unitaryConj U.form v) hv⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
