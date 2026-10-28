module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FullCubicInvolutions

/-!
# Original Mathieu involution lifts in the cubic centralizer

The marked source hypotheses give IsTypeJ4 on the same central involution.
For every original cubic quotient and its Sylow three-subgroup, the literal
projection C_H(X) → C_H(X)/⟨z⟩ lifts all involutions to involutions. Every
lift of a square-one element has square one, and elementary subgroups have
elementary full inverse images. No splitting hypothesis is added.

This discharges the centralizer involution-lifting step in AS91 (4.8),
printed p.599, for the original Aschbacher--Smith 8.2.12--14 Mathieu data.
The involution outside C_H(X), Todd splitting, LocalData construction and
unconditional ambient recognition remain separate obligations.
Source: Aschbacher--Segev, Invent. Math. 105 (1991), (4.8)--(4.9),
DOI 10.1007/BF01232280.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
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

include D h hmany hV hq hnon a E hE z hz hne hquot

/-- Every square-one element of the original triple quotient has only
square-one lifts through the original marker line. -/
theorem sourceOrbit_m24_full_cubic_square_one :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (x : fullCubicCentralizer cubic X),
      fullCubicProjection ht cubic X x ^ 2 = 1 → x ^ 2 = 1 := by
  intro ht cubic X x hx
  exact fullCubic_square_eq_one ht cubic X x hx

/-- The actual original centralizer projection lifts every quotient involution. -/
theorem sourceOrbit_m24_full_cubic_involution_lift :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (u : cubicCentralizer cubic X), orderOf u = 2 →
      ∃ x : fullCubicCentralizer cubic X,
        fullCubicProjection ht cubic X x = u ∧ orderOf x = 2 := by
  intro ht cubic X u hu
  exact fullCubic_involution_lift ht cubic X u hu

/-- The full inverse image, with the original marker retained, is elementary. -/
theorem sourceOrbit_m24_full_cubic_elementary_preimage :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (A : Subgroup (cubicCentralizer cubic X)), IsElementaryAbelian 2 A →
      IsElementaryAbelian 2 (A.comap (fullCubicProjection ht cubic X)) := by
  intro ht cubic X A hA
  let := hA
  exact fullCubic_elementary_preimage ht cubic X A

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
