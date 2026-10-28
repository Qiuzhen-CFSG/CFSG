module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology.Original

/-!
# Original Mathieu application of the overlap quotient calculation

The unchanged Chapter 12 marked-M24 hypotheses give the same IsTypeJ4
witness. With its earlier Section 4 LocalData, the literal point-plane
quotient I/(Q A) has the natural Sp4(2) cohomology and the complete
inner-times-quadratic-twist automorphism description. The source cubic
scalar remains in the denominator and all conjugation coordinates use
the same original quotient map. Neither simplicity of the native J4
model nor a compatible local comparison is assumed.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
This supplies the quotient automorphism step for the original Mathieu
branch. The full overlap lift, local-map agreement and edge equation
remain with Section 8 assembly.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour SourceComparison SourceRecognition
open LocalGeometry.LocalSubgroups
open SourceComparison.OverlapCohomology
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The genuine original overlap quotient, with its retained scalar and
constructed automorphism correction, for the marked Mathieu branch. -/
theorem sourceOrbit_m24_overlap_quotient_automorphisms
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
    let hj := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    (twoThreeCore (Recognition.JankoFour.centralizer (z : G))).subgroupOf
        (data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G))) =
      (core (z : G) ⊔ cubicSylowImage data.e data.X).subgroupOf
        (data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G))) ∧
    Module.finrank (ZMod 2) (OneCohomology.H1 (originalRepresentation hj data.P)) = 1 ∧
    (originalActor hj data.P).ker = pCore 2 (Original data.P) ∧
    (∀ g : Original data.P, ∀ n : pCore 2 (Original data.P),
      (originalCoordinates hj data.P (MulAut.conjNormal g n)).toAdd =
        natural (originalActor hj data.P g) (originalCoordinates hj data.P n).toAdd) ∧
    originalQuadraticTwist hj data.P ^ 2 = 1 ∧
    (¬ ∃ x : Original data.P, originalQuadraticTwist hj data.P = MulAut.conj x) ∧
    (∀ n : pCore 2 (Original data.P), originalQuadraticTwist hj data.P n.val = n.val) ∧
    (∀ α : MulAut (Original data.P), ∃ x : Original data.P,
      α = MulAut.conj x ∨ α = MulAut.conj x * originalQuadraticTwist hj data.P) := by
  let hj := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  exact ⟨original_denominator hj data,original_comparison hj data.P⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
