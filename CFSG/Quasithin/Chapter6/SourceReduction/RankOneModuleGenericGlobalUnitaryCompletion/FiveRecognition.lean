module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.FiveGeometry
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveRecognition

/-!
# Recognition of the original PSU₅(4) normalizer pair

The compatible full DGS extension and ambient order bound yield the literal
original normalizer completion in G, with its whole overlap and both local
orientations. Full-extension recognition and original ambient simplicity
identify G with the parameter-four projective unitary-five carrier. The
field has order sixteen; its order-five scalar kernel is retained.

The generic-global producer retains the compatible extension, order bound,
and exhaustive model selection. Source: Aschbacher–Smith 5.2.6–7,5.3.1–4
and F.4.24, pp.650–651,658–659,287.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion

theorem Preparation.unitaryFive_extension_recognition
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : FiveLocalComparison L (residual H) (sourceS L H) U)
    (E : FiveExtension U) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    n = 4 ∧ Nat.card G=Nat.card E.carrier ∧ ClassicalGroup.IsPSU G 5 4 := by
  obtain ⟨hn,c,ho,_hN,_⟩ := d.unitaryFive_native_ambient_completion h hH hp U hc E he horder
  let : IsSimpleGroup G := h.qtke.simple
  obtain ⟨e⟩ := FiveWeyl.nonempty_mulEquiv_native_of_simple U E c ho horder
  refine ⟨hn,five_completion_card_eq U E c ho horder,?_⟩
  exact ⟨U.F,inferInstance,inferInstance,U.form,U.card,U.conjugation,⟨e⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
