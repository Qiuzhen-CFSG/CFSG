module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio.Comparisons

/-!
# Exhausting Table B.4.5 under the quadratic bound

All fourteen rows are retained in the input. The strict quadratic bounds
exclude seven rows; actual model comparisons exclude A₇, G₂(2)′, M₂₂,
its triple cover, and the special unitary row. The orthogonal row is
excluded only after recovering its defining field. The Suzuki row retains
the given action equivalence and the source defining-field cardinality.

Source: Aschbacher--Smith, Table B.4.5, printed p.87, and p.1152.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups ENNReal
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
open FFExclusions.ModelRigidity

universe u v
variable {D : Type u} [Group D] [Finite D] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {L : Subgroup D} {f : ℕ}

/-- Every table row is inspected. In the orthogonal row the actual PSL₂
isomorphism recovers the field before the even-exponent contradiction. -/
theorem natural_of_table_B45 (hs : SourceModel (L ⧸ center L) f)
    (hf : 1 < f) (ho : Odd f) (hz : center L = ⊥)
    (hq : quadraticRatio ρ ≤ 2) (h : TableB45 ρ L) : NaturalConstituent ρ L f := by
  have hsL := hs.transport (centerQuotientEquiv hz).symm
  cases h with
  | alternatingSeven action _ _ _ =>
    have hc := hs.componentModel hf ho (.alternatingSeven
      ((centerQuotientEquiv hz).trans action.groupEquiv))
    rcases hc.1 with he | he | he <;> cases he
  | orthogonal K F degree actor _ _ _ _ =>
    have hc := hs.componentModel hf ho (.linearTwo F.Carrier F.degree_pos F.card_eq
      ((centerQuotientEquiv hz).trans actor))
    exact (field_card_ne_even_exponent (F.card_eq.trans hc.2) ho K.degree
      (by rw [F.card_eq, degree])).elim
  | unitary F n large degree J conjugation action _ _ _ =>
    have hF : Nat.card F.Carrier = (2 ^ n) ^ 2 := by
      rw [F.card_eq, degree, Nat.mul_comm 2 n, pow_mul]
    exact (hsL.not_specialUnitary hf ho hz J (by omega) hF conjugation action.groupEquiv).elim
  | suzuki k positive action _ _ _ =>
    have he := hsL.suzuki_degree hf positive action.groupEquiv
    exact .suzuki k positive he (by rw [he]; exact GaloisField.card 2 _ (by omega)) action
  | linearThree _ _ _ _ _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | g2Derived action _ _ _ =>
    have hc := hs.componentModel hf ho (.gTwoTwoDerived
      ((centerQuotientEquiv hz).trans action.groupEquiv))
    rcases hc.1 with he | he | he <;> cases he
  | mathieuTwelve _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | tripleMathieuTwentyTwo _ quotientEquiv _ _ _ =>
    exact (hs.not_mathieuTwentyTwo hf quotientEquiv).elim
  | mathieuTwentyTwoCocode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | mathieuTwentyTwoCode action _ _ _ =>
    exact (hsL.not_mathieuTwentyTwo hf action.groupEquiv).elim
  | mathieuTwentyThreeCocode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | mathieuTwentyThreeCode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | mathieuTwentyFourCocode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | mathieuTwentyFourCode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
