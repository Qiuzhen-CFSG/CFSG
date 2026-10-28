module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.Inner
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FourRecognition

/-!
# Recognition of the original nonbinary unitary-four normalizer pair

The literal compatible DGS extension and the ambient order bound yield a
faithful completion in G with whole overlap. The established comparison
supplies m > 1 and n = 2*m. Full-extension completion recognition gives a
faithful normal PSU₄(2^m) subgroup; original ambient simplicity makes it G.
This retains both orientations and ordinary/degree-two local comparisons.

The only extra source inputs are the genuine compatible extension and
ambient bound, retained with the generic-global producer. Source:
Aschbacher–Smith 5.2.6–7,5.3.1–4 and F.4.24, pp.650–651,658–659,287.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion

theorem Preparation.unitary_extension_recognition
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (E : FourExtension m hm) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    1 < m ∧ n = 2*m ∧ Nat.card G=Nat.card E.carrier ∧ ClassicalGroup.IsPSU G 4 (2^m) := by
  obtain ⟨hmgt,hn,c,ho,_hN,_⟩ := d.unitary_native_ambient_completion h hH hp m hm hc E he horder
  let : IsSimpleGroup G := h.qtke.simple
  obtain ⟨e⟩ := FourWeyl.nonempty_mulEquiv_native_of_simple m hm hmgt E c ho horder
  refine ⟨hmgt,hn,four_completion_card_eq m hm hmgt E c ho horder,?_⟩
  exact ⟨ChapterF.GreenBook.LieModels.UnitaryFour.MatrixField m,inferInstance,inferInstance,
    ChapterF.GreenBook.LieModels.UnitaryFour.standardForm m hm,
    ChapterF.GreenBook.LieModels.UnitaryFour.matrixField_card m hm,
    ChapterF.GreenBook.LieModels.UnitaryFour.fieldConj_apply m,⟨e⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
