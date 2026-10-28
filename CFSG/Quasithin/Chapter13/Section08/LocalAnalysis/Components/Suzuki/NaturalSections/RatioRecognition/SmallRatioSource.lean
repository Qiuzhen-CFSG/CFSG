module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.Modules
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.FFExclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.SourceB42
public import Theory.SpecificGroups.ThreeDivisibility.Classical
public import Theory.Mathieu.M22.Properties.Order

/-!+# The full B.4.5 alternatives and their quadratic-bound consequence

`FullB45` retains all fourteen rows of Table B.4.5 and both cases of (iii),
on the original finite faithful binary action with its actual quasisimple
generalized Fitting subgroup. Together with the full universal B.4.2
implication, this gives the proved reduction: q ≤ 2 forces either an actual
natural Suzuki action or order divisible by three. The universal
classification implications are explicit inputs, not asserted theorems.

The proof discards every q > 2 row numerically. In case (i), attainment
and offender replacement produce the best offender needed by B.4.2.
For the other surviving rows we use actual matrix or permutation models;
in particular three-divisibility passes from PSU to SU and from M₂₂ to
its genuine triple cover through quotient cardinality.

Source conventions: Remark B.4.4 identifies A₅, A₆, A₈ and the small
odd-characteristic coincidences with their characteristic-two models.
The complete B.4.2 action list retains those endpoints. For the unitary
row K.3.3 explicitly gives SU₃, including its center. For the L₃ row we
retain both SL₃ and PSL₃ as in K.3.2 (p.454), rather than reading the
abbreviated table label as an instruction to discard central covers.
The Suzuki intertwiner is justified by the natural-module assertion
immediately before K.3.5 and in K.3.6, not by dimension alone.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2,
Remark B.4.4 and B.4.5, printed pp.86–87 (PDF pp.97–98); K.3,
pp.453–457, and H.13.1, p.395.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open BenderSuzuki.MatrixGroups Sporadic.Mathieu
open scoped ENNReal

namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- Every row of Table B.4.5, retaining its actor, dimension, module
distinctions, and both numerical columns. The common 1 < q-hat ≤ 2
is recorded by the enclosing `B45Conclusion.table` constructor. -/
inductive TableB45 (L : Subgroup D) : Prop
  | alternatingSeven
      (action : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 7))
      (dimension : Module.finrank (ZMod 2) V = 6)
      (quadratic : quadraticRatio ρ = 3 / 2) (cubic : cubicRatio ρ = 3 / 2)
  | orthogonal (K F : BinaryField) (degree : F.degree = 2 * K.degree)
      (actor : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F.Carrier)
      (action : ActionEquiv (ρ.comp L.subtype) (orthogonalFour K))
      (dimension : Module.finrank (ZMod 2) V = 4 * K.degree)
      (quadratic : quadraticRatio ρ ≤ 2) (cubic : cubicRatio ρ ≤ 3 / 2)
  | unitary (F : BinaryField) (n : ℕ) (large : 2 ≤ n)
      (degree : F.degree = 2 * n) (J : HermitianForm 3 F.Carrier)
      (conjugation : ∀ x, J.conj x = x ^ (2 ^ n))
      (action : ActionEquiv (ρ.comp L.subtype) (unitaryThree F J))
      (dimension : Module.finrank (ZMod 2) V = 6 * n)
      (quadratic : quadraticRatio ρ = 2) (cubic : cubicRatio ρ = 2)
  | suzuki (k : ℕ) (positive : 0 < k)
      (action : ActionEquiv (ρ.comp L.subtype) (Suzuki.natural k))
      (dimension : Module.finrank (ZMod 2) V = 4 * (2 * k + 1))
      (quadratic : quadraticRatio ρ = 2) (cubic : cubicRatio ρ = 2)
  | linearThree (F : BinaryField) (n : ℕ) (positive : 0 < n)
      (degree : F.degree = 2 * n)
      (actor : Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) ∨
        Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F.Carrier))
      (dimension : Module.finrank (ZMod 2) V = 9 * n)
      (quadratic : 2 < quadraticRatio ρ) (cubic : cubicRatio ρ = 5 / 4)
  | g2Derived
      (action : ActionEquiv (ρ.comp L.subtype) (g2DerivedNatural (ZMod 2)))
      (dimension : Module.finrank (ZMod 2) V = 6)
      (quadratic : quadraticRatio ρ = 3 / 2) (cubic : cubicRatio ρ = 3 / 2)
  | mathieuTwelve (actor : L ≃* M12)
      (dimension : Module.finrank (ZMod 2) V = 10)
      (quadratic : 2 < quadraticRatio ρ) (cubic : 1 < cubicRatio ρ)
  | tripleMathieuTwentyTwo
      (centerEquiv : center L ≃* Multiplicative (ZMod 3))
      (quotientEquiv : (L ⧸ center L) ≃* M22)
      (dimension : Module.finrank (ZMod 2) V = 12)
      (quadratic : 1 < quadraticRatio ρ) (cubic : 1 < cubicRatio ρ)
  | mathieuTwentyTwoCocode
      (action : ActionEquiv (ρ.comp L.subtype) m22Cocode)
      (dimension : Module.finrank (ZMod 2) V = 10)
      (quadratic : 2 < quadraticRatio ρ) (cubic : 1 < cubicRatio ρ)
  | mathieuTwentyTwoCode
      (action : ActionEquiv (ρ.comp L.subtype) MathieuCode.m22CodeRepresentation)
      (dimension : Module.finrank (ZMod 2) V = 10)
      (quadratic : 2 ≤ quadraticRatio ρ) (cubic : 1 < cubicRatio ρ)
  | mathieuTwentyThreeCocode
      (action : ActionEquiv (ρ.comp L.subtype) MathieuCode.m23CocodeRepresentation)
      (dimension : Module.finrank (ZMod 2) V = 11)
      (quadratic : 2 < quadraticRatio ρ) (cubic : 1 < cubicRatio ρ)
  | mathieuTwentyThreeCode
      (action : ActionEquiv (ρ.comp L.subtype) MathieuCode.m23CodeRepresentation)
      (dimension : Module.finrank (ZMod 2) V = 11)
      (quadratic : 2 < quadraticRatio ρ) (cubic : 1 < cubicRatio ρ)
  | mathieuTwentyFourCocode
      (action : ActionEquiv (ρ.comp L.subtype) MathieuCode.cocodeRepresentation)
      (dimension : Module.finrank (ZMod 2) V = 11)
      (quadratic : 2 < quadraticRatio ρ) (cubic : 1 < cubicRatio ρ)
  | mathieuTwentyFourCode
      (action : ActionEquiv (ρ.comp L.subtype) MathieuCode.codeRepresentation)
      (dimension : Module.finrank (ZMod 2) V = 11)
      (quadratic : 2 < quadraticRatio ρ) (cubic : 1 < cubicRatio ρ)

/-- Both cases in B.4.5(iii), before imposing the distinct numerical bounds. -/
inductive BoundaryB45 (L : Subgroup D) : Prop
  | symplectic (descent : SymplecticTensorDescent (ρ.comp L.subtype))
  | jankoTwo (actor : L ≃* Sporadic.LeechRelated.J2.Carrier)
      (dimension : Module.finrank (ZMod 2) V = 12)

/-- The complete B.4.5 conclusion. Case (i) invokes B.4.2 via the actual
best offender, as proved below; it is not replaced by a restricted model list. -/
inductive B45Conclusion : Prop
  | ff (cubic : cubicRatio ρ ≤ 1)
  | table (lower : 1 < cubicRatio ρ) (upper : cubicRatio ρ ≤ 2)
      (row : TableB45 ρ (generalizedFitting D))
  | boundary (cubic : cubicRatio ρ = 2) (quadratic : 2 < quadraticRatio ρ)
      (alternative : BoundaryB45 ρ (generalizedFitting D))

/-- The unfiltered universal source implication. Its proof remains with
the owner of B.4; no Suzuki identification is part of its input. -/
def FullB45 (𝒦 : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (V : Type v)
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V), B45Hypotheses 𝒦 ρ → B45Conclusion ρ

/-- The actual module identification, allowing the parameter to be discovered. -/
def HasNaturalSuzukiRestriction : Prop :=
  ∃ k, 0 < k ∧ Nonempty
    (ActionEquiv (ρ.comp (generalizedFitting D).subtype) (Suzuki.natural k))

/-- Three-divisibility lifts from the projective unitary group to SU. -/
theorem three_dvd_card_specialUnitary (F : BinaryField) (n : ℕ) (hn : 0 < n)
    (degree : F.degree = 2 * n) (J : HermitianForm 3 F.Carrier)
    (conjugation : ∀ x, J.conj x = x ^ (2 ^ n)) :
    3 ∣ Nat.card J.specialSubgroup := by
  have hcard : Nat.card F.Carrier = (2 ^ n) ^ 2 := by
    rw [F.card_eq, degree, Nat.mul_comm 2 n, pow_mul]
  exact (Theory.SpecificGroups.ThreeDivisibility.unitary_three_dvd J n hn
    hcard conjugation).trans (J.specialSubgroup.card_map_dvd Matrix.ProjGenLinGroup.mk)

/-- Numerical elimination of all q > 2 rows leaves only genuine Suzuki
modules and models with three dividing their order. -/
theorem TableB45.natural_or_three [Finite D]
    (h : TableB45 ρ (generalizedFitting D)) (hq : quadraticRatio ρ ≤ 2) :
    HasNaturalSuzukiRestriction ρ ∨ 3 ∣ Nat.card (generalizedFitting D) := by
  cases h with
  | alternatingSeven action _ _ _ =>
    right
    rw [Nat.card_congr action.groupEquiv.toEquiv]
    exact three_dvd_card_alternating 7 (by decide)
  | orthogonal K F _ actor _ _ _ _ =>
    right
    rw [Nat.card_congr actor.toEquiv]
    exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F.Carrier 2 (by decide)
  | unitary F n large degree J conjugation action _ _ _ =>
    right
    rw [Nat.card_congr action.groupEquiv.toEquiv]
    exact three_dvd_card_specialUnitary F n (by omega) degree J conjugation
  | suzuki k positive action _ _ _ => exact Or.inl ⟨k, positive, ⟨action⟩⟩
  | linearThree _ _ _ _ _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | g2Derived action _ _ _ =>
    right
    rw [Nat.card_congr action.groupEquiv.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_g2_derived_two
  | mathieuTwelve _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | tripleMathieuTwentyTwo _ quotientEquiv _ _ _ =>
    right
    have hm : 3 ∣ Nat.card (generalizedFitting D ⧸ center (generalizedFitting D)) := by
      rw [Nat.card_congr quotientEquiv.toEquiv, m22_order]
      norm_num
    exact hm.trans (center (generalizedFitting D)).card_quotient_dvd_card
  | mathieuTwentyTwoCocode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | mathieuTwentyTwoCode action _ _ _ =>
    right
    rw [Nat.card_congr action.groupEquiv.toEquiv, m22_order]
    norm_num
  | mathieuTwentyThreeCocode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | mathieuTwentyThreeCode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | mathieuTwentyFourCocode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim
  | mathieuTwentyFourCode _ _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim

/-- Reduction of a supplied complete B.4.5 conclusion. In case (i),
produce an actual best offender and apply the full B.4.2 implication. -/
theorem B45Conclusion.natural_or_three [Finite D] [Finite V]
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    (hyp : B4Hypotheses 𝒦 ρ) (h : B45Conclusion ρ)
    (hq : quadraticRatio ρ ≤ 2) :
    HasNaturalSuzukiRestriction ρ ∨ 3 ∣ Nat.card (generalizedFitting D) := by
  cases h with
  | ff cubic =>
    obtain ⟨A, hA⟩ := hyp.exists_B42_of_cubic_le_one cubic
    let := hyp.quasisimple
    exact Or.inr (three_dvd_card_quasisimpleModel ((hB42 D V ρ A hA).model ρ))
  | table _ _ row => exact row.natural_or_three ρ hq
  | boundary _ quadratic _ => exact (not_lt_of_ge hq quadratic).elim

/-- The generic small-quadratic-ratio consequence of the full earlier
classifications. No identification of F*(D) is assumed. -/
theorem natural_or_three_of_full_classification [Finite D] [Finite V]
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hyp : B4Hypotheses 𝒦 ρ) (hq : quadraticRatio ρ ≤ 2) :
    HasNaturalSuzukiRestriction ρ ∨ 3 ∣ Nat.card (generalizedFitting D) :=
  (hB45 D V ρ (hyp.with_quadratic_bound hq)).natural_or_three ρ hB42 hyp hq

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
