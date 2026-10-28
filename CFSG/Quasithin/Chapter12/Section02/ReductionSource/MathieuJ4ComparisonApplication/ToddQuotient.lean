module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCharacteristic

/-!
# Actual Todd quotient correction in the original Mathieu branch

Retain the original marked M24 hypotheses, its same IsTypeJ4 witness,
and the unchanged earlier LocalData. Tetrad parity now identifies the
literal I/(Q A) with its affine natural group. The actual cubic-fixing
Todd correction is outer there, and every automorphism of the original
I preserves both Q and Q A and has the stated quotient factorization.
All quotient maps and the scalar cubic use the original data.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
The full overlap lift and edge-reversal recognition remain unasserted.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour SourceComparison SourceRecognition
open LocalGeometry.LocalSubgroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The constructed affine quotient and the actual Todd outer class in the
same original overlap, including the cubic scalar in its denominator. -/
theorem sourceOrbit_m24_todd_quotient_class
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    (overlapAffineProjection data).ker =
      (twoThreeCore (Recognition.JankoFour.centralizer (z : G))).subgroupOf (PlaneOverlap data) ∧
    (∀ x : PlaneOverlap data, cubicAffineEquiv data (QuotientGroup.mk' _ x) =
      overlapAffineProjection data x) ∧
    (¬ ∃ x : OverlapCohomology.Original data.P, cubicToddQuotientTwist data = MulAut.conj x) ∧
    (∃ x : OverlapCohomology.Original data.P, cubicToddQuotientTwist data =
      MulAut.conj x * OverlapCohomology.originalQuadraticTwist
        (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data.P) := by
  exact ⟨overlapAffineProjection_ker data,cubicAffineEquiv_mk data,
    cubicToddQuotientTwist_not_inner data,cubicToddQuotientTwist_outer_class data⟩

/-- The original automorphism can be arbitrary: preservation of Q and Q A
is a conclusion, and its quotient correction comes from the actual M. -/
theorem sourceOrbit_m24_overlap_automorphism_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    (f : MulAut (PlaneOverlap data)) :
    ((core (z : G)).subgroupOf (PlaneOverlap data)).map f.toMonoidHom =
      (core (z : G)).subgroupOf (PlaneOverlap data) ∧
    ((twoThreeCore (Recognition.JankoFour.centralizer (z : G))).subgroupOf (PlaneOverlap data)).map
        f.toMonoidHom =
      (twoThreeCore (Recognition.JankoFour.centralizer (z : G))).subgroupOf (PlaneOverlap data) ∧
    (∃ x : PlaneOverlap data,
      (∀ y : PlaneOverlap data, QuotientGroup.mk'
        ((twoThreeCore (Recognition.JankoFour.centralizer (z : G))).subgroupOf (PlaneOverlap data))
        (f y) = QuotientGroup.mk' _ (x*y*x⁻¹)) ∨
      (∀ y : PlaneOverlap data, QuotientGroup.mk'
        ((twoThreeCore (Recognition.JankoFour.centralizer (z : G))).subgroupOf (PlaneOverlap data))
        (f y) = QuotientGroup.mk' _
          (x * planeOverlapToddTwist data (cubicFixedWord data) y * x⁻¹))) := by
  exact ⟨overlap_automorphism_preserves_core data f,
    overlap_automorphism_preserves_cubicLift data f,overlap_automorphism_quotient_factorization data f⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
