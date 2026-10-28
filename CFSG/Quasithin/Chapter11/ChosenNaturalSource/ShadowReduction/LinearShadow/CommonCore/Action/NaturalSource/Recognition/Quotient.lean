module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Recognition.Inputs
public import Theory.Representation.SL2SylowFixedRecognition.Reduction

/-!
# Complementary fixed spaces for the source central quotient

G.1.6's reduction applies to the actual action on V_H/C_{V_H}(K).
The elementary structure, generation and uniformity come from 11.3.1 and
the earlier source lemmas. The Sylow witness is still the original subgroup
of K-star, with its literal image equality. The final 11.3.7 assembly is owned
by `qt-d-1222-shadow-common-action`; it supplies that Sylow witness.

Source: Aschbacher--Smith, G.1.6 and 11.3.7, printed pp.329 and 773.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
namespace NaturalRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The source action has complementary Sylow fixed spaces after taking its
literal global-fixed quotient, using any compatible matrix identification. -/
theorem source_centralQuotient_exists_complement
    (s : Hypothesis1131At D S U₁ H)
    (e : residualStar T H ≃* SL(2,S.field.Carrier))
    (R : Sylow 2 (residualStar T H)) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H)) :
    let _ := source_omegaClosure_elementary s
    ∃ Q : Sylow 2 SL(2,S.field.Carrier),
      IsCompl
        (fixedSpace (SL2SylowFixedRecognition.centralQuotient (binaryAction T H e))
          (R.mapSurjective (f := e.toMonoidHom) e.surjective))
        (fixedSpace (SL2SylowFixedRecognition.centralQuotient (binaryAction T H e)) Q) := by
  let := source_omegaClosure_elementary s
  exact SL2SylowFixedRecognition.centralQuotient_exists_complement
    (binaryAction T H e) _ (source_fixedSpaceHypotheses s e R g hg hs hmodel hR)
    S.field.degree S.nonbinary S.field.card_eq

end NaturalRecognition
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
