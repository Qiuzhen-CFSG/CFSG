module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Recognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Recognition.Quotient
public import Theory.Representation.SL2SylowFixedRecognition

/-!
# Natural quotient coordinates on the original source action

The general G.1.6 theorem now discharges recognition. In the degree-n
application, the original hypotheses give generation and uniformity, and the
two compatible matrix identifications return the exact source marking. The
same theorem applies at degree 2n before parameter equality is established.
That branch's source generation and uniformity are supplied by
`qt-d-1222-shadow-doubled-exclusion`; no degree-n marking is used there.
The preceding-source conclusions and selected Sylow placement in the degree-n
application are discharged by `qt-d-1222-shadow-common-action`.

Source: Aschbacher--Smith, G.1.6--7 and 11.3.6--7, pp.329--330, 772--773.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Representation.SL2SylowFixedRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
namespace NaturalRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- G.1.6 on the literal source action at any degree. The explicit generation
and uniformity inputs belong to the source branch, not to recognition. -/
theorem source_coordinates_at_degree
    (s : Hypothesis1131At D S U₁ H) (B : BinaryField) (hB : 2 ≤ B.degree)
    (e : residualStar T H ≃* SL(2,B.Carrier)) (R : Sylow 2 (residualStar T H))
    (h : let _ := source_omegaClosure_elementary s
      FixedSpaceHypotheses (binaryAction T H e)
        (R.mapSurjective (f := e.toMonoidHom) e.surjective)) :
    let _ := source_omegaClosure_elementary s
    ∃ c : QuotientCoordinates (binaryAction T H e), 0 < c.multiplicity := by
  let := source_omegaClosure_elementary s
  obtain ⟨c⟩ := quotientCoordinates_of_fixedSpaceHypotheses (binaryAction T H e) _ h
    B.degree hB B.card_eq
  exact ⟨c,c.positive_of_movement
    (binaryAction_moves e s.outside.1.1.2 s.moves_omega_center)⟩

/-- The early 11.3.6 application uses degree 2n, with no assumption k=n.
Its inputs are produced by the doubled-exclusion owner on this same action. -/
theorem source_doubled_coordinates
    (s : Hypothesis1131At D S U₁ H) (B : BinaryField)
    (hB : B.degree = 2 * S.field.degree)
    (e : residualStar T H ≃* SL(2,B.Carrier)) (R : Sylow 2 (residualStar T H))
    (h : let _ := source_omegaClosure_elementary s
      FixedSpaceHypotheses (binaryAction T H e)
        (R.mapSurjective (f := e.toMonoidHom) e.surjective)) :
    let _ := source_omegaClosure_elementary s
    ∃ c : QuotientCoordinates (binaryAction T H e), 0 < c.multiplicity := by
  apply source_coordinates_at_degree s B _ e R h
  have := S.nonbinary
  omega

/-- The concrete 11.3.7 marking from the original source and selected conjugate.
Generation, uniformity, general recognition, and positivity are all discharged. -/
theorem source_naturalQuotientMarking
    (s : Hypothesis1131At D S U₁ H)
    (R : Sylow 2 (residualStar T H)) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H)) :
    Nonempty (NaturalQuotientMarking T H S.field) := by
  let := source_omegaClosure_elementary s
  obtain ⟨e,eStar,he⟩ := source_compatible_matrix_equivs s hmodel
  have hf := source_fixedSpaceHypotheses s eStar R g hg hs hmodel hR
  obtain ⟨c⟩ := quotientCoordinates_of_fixedSpaceHypotheses (binaryAction T H eStar) _ hf
    S.field.degree S.nonbinary S.field.card_eq
  exact marking_of_coordinates s e eStar he c

end NaturalRecognition
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
