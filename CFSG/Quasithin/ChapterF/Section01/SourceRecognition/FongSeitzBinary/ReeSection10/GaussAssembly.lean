module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.GaussEquations

/-!
# Source Gauss fields after the coordinate identifications

The literal matrix transports already prove both Gauss identities.  This
small assembly module packages them into the exact `Global.SourceGauss`
field, retaining the chart, reflection, and torus identifications as explicit
premises of the consumer.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open RootPresentationRecognition

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
  (d : SourcePositive.Charts Q split m)
  (T : SourceBorel.TorusData Q split d)
  (W : SourceNormalizer.WeylData Q split d T)

theorem synchronizedSourceSigned
    (hd : ∀ i a, (d.chart i a : X ⧸ Q.D) =
      synchronizedPositivePoint Q split c i a)
    (hW : ∀ s, W.n s = sourceSimpleReflection Q split c s) :
    SourceSigned.Equations Q split d T W :=
  synchronizedSourceSigned_equations Q split c d T W hd hW

theorem synchronizedSourceGauss
    (hd : ∀ i a, (d.chart i a : X ⧸ Q.D) =
      synchronizedPositivePoint Q split c i a)
    (hW : ∀ s, W.n s = sourceSimpleReflection Q split c s)
    (hTl : ∀ a : (CoefficientField m)ˣ,
      T.h (linearTau a) = synchronizedLinearTorus Q split c a)
    (hTs : ∀ a : (CoefficientField m)ˣ,
      T.h (suzukiTau a) = synchronizedSuzukiTorus Q split c
        (synchronizedSuzukiGaussParameter a)) :
    Global.SourceGauss Q split d T W where
  linear := synchronizedSourceLinear_gauss Q split c d T W hd hW hTl
  suzuki := synchronizedSourceSuzuki_gauss Q split c d T W hd hW hTs

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
