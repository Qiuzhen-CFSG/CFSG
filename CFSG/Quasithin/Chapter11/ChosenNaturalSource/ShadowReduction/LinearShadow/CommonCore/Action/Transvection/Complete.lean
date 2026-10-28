module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.AxisCases.Sp4
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.AxisCases.SL3
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.SL3Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Sp4Source

/-!
# The original equality and Sylow conclusion of 11.3.7(4)

In each surviving natural model, the genuine Hall action identifies the
original marked line in compatible V_H coordinates. Its individual commutator
realization and the reciprocal displacement orbit construct the literal x*g
transporter. The source line-normalizer theorem identifies A with V, and the
original A-star Sylow image is thereby the V-star image.

The inputs here are the preceding source conclusions from natural local
geometry, parameter/component recognition, and the natural/Cartan action
branches. The final owner qt-d-1222-shadow-common-action discharges those
inputs. All local scalar-span, Hall-spectrum, original-line and reciprocal-orbit
premises are discharged here; no transvection-recognition callback is assumed.
The common-axis and multiplicity theorems are re-exported alongside this
endpoint. The doubled R₂ comparison is also re-exported: its sole action input is
the preceding original flag-radical shear image, discharged by the same
final owner.
Source: Aschbacher--Smith 11.3.7(4), printed p.773 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The equality and actual starred Sylow conclusion in both surviving models,
with the actual normalizer transporter retained. -/
theorem source_seed_star_sylow_transvections
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hline : U₁ = c.binarySubspace (f.space 0))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hcounter : ¬ Proposition1132At D S U₁ H)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hparameters : (S.field.degree : ℕ∞) < CFSG.Quasithin.ChapterE.globalR V ∨
      (Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
        CFSG.Quasithin.ChapterE.globalR V = S.field.degree ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)))
    (g : G) (cK : NaturalQuotientMarking T H S.field)
    (hfixedL : V ⊓ centralizer (L : Set G) = ⊥)
    (hfixedK : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    [IsSimpleGroup (outsideResidual H ⧸ pCore 2 (outsideResidual H))]
    (hAH : V.map (MulAut.conj g).toMonoidHom ≤ H)
    (P : Sylow 2 (residualStar T H))
    (hP : (P : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H))
    (D_H : Subgroup G)
    (hDH : D_H ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (D_H.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hcontain : D.centralQuotientPreimage U₁ ≤
      omegaClosure T H ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hcomm : D.centralQuotientPreimage U₁ = ⁅D.centralQuotientPreimage U₁,oddCartanPart D_H⁆) :
    (∃ x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G),
      (D.centralQuotientPreimage U₁).map (MulAut.conj (x * g)).toMonoidHom =
        D.centralQuotientPreimage U₁) ∧
      V.map (MulAut.conj g).toMonoidHom = V ∧
      (P : Subgroup (residualStar T H)).map (residualStar T H).subtype =
        (V.subgroupOf H).map (starProjection T H) := by
  cases c with
  | sl3 a =>
    exact source_seed_star_sylow_sl3 a f hline s p hcounter halt hparameters g cK
      hfixedL hfixedK hAH P hP D_H hDH hHall hcontain hcomm
  | sp4 a =>
    exact source_seed_star_sylow_sp4 a f hline s p hcounter halt hparameters g cK
      hfixedL hfixedK hAH P hP D_H hDH hHall hcontain hcomm
  | g2 a => exact (hG2 ⟨a⟩).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
