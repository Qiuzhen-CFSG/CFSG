module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FullCubicCentralizer

/-!
# The original Mathieu application of the full cubic central extensions

For every original cubic quotient and its Sylow subgroup, the marked Mathieu
inputs construct the double extension C_H(X)→3.M22 with kernel the original
involution line, its center X⟨z⟩ of order six, its simple M22 quotient, and
its quasisimple derived subgroup. The same inputs give N_H(X)/⟨z⟩≃H/Q and
the exact centralizer index two in N_H(X), retaining all quotient maps.

The source (4.9) perfectness and splitting remain to be proved upstairs:
the new exports isolate membership of the original z in the derived subgroup
and the required involution in the other normalizer coset. Neither condition
is assumed here or replaced by its quotient analogue. Todd splitting,
LocalData construction and final recognition remain with this family.

Source: Aschbacher--Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (4.8)--(4.9), p.599, DOI 10.1007/BF01232280;
original Aschbacher--Smith 8.2.12--14 marked Mathieu application.
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

include D h hmany hV hq hnon a E hE

include z hz hne hquot

/-- Original Mathieu inputs give the full centralizer and normalizer extensions
for every original cubic quotient and cubic Sylow, without a splitting premise. -/
theorem sourceOrbit_m24_full_cubic_extensions :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot;
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)),
      Function.Surjective (fullCubicProjection ht cubic X) ∧
      (fullCubicProjection ht cubic X).ker = zpowers (fullCubicMarker cubic X) ∧
      Nat.card (fullCubicProjection ht cubic X).ker = 2 ∧
      Nonempty ((fullCubicCentralizer cubic X ⧸ (fullCubicProjection ht cubic X).ker) ≃*
        M22TripleCover) ∧
      (center (fullCubicCentralizer cubic X)).map (fullCubicCentralizer cubic X).subtype =
        cubicSylowImage cubic X ⊔ center (centralizer ({(z : G)} : Set G)) ∧
      Nat.card (center (fullCubicCentralizer cubic X)) = 6 ∧
      Nonempty ((fullCubicCentralizer cubic X ⧸ center (fullCubicCentralizer cubic X)) ≃* M22) ∧
      (∀ c : fullCubicCentralizer cubic X,
        MulAut.conj (fullCubicSimpleProjection ht cubic X c) =
          cubic.projection (QuotientGroup.mk' (Recognition.JankoFour.core (z : G)) c.val)) ∧
      IsQuasisimple (commutator (fullCubicCentralizer cubic X)) ∧
      componentLayer (fullCubicCentralizer cubic X) = commutator (fullCubicCentralizer cubic X) ∧
      (commutator (fullCubicCentralizer cubic X)).index ∣ 2 ∧
      (componentLayer (fullCubicCentralizer cubic X) = ⊤ ↔
        fullCubicMarker cubic X ∈ commutator (fullCubicCentralizer cubic X)) ∧
      Recognition.JankoFour.core (z : G) ⊓ fullCubicNormalizer cubic X =
        center (centralizer ({(z : G)} : Set G)) ∧
      Function.Surjective (fullCubicNormalizerProjection cubic X) ∧
      (fullCubicNormalizerProjection cubic X).ker =
        (center (centralizer ({(z : G)} : Set G))).subgroupOf (fullCubicNormalizer cubic X) ∧
      Nonempty ((fullCubicNormalizer cubic X ⧸
        (center (centralizer ({(z : G)} : Set G))).subgroupOf (fullCubicNormalizer cubic X)) ≃*
          (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G))) ∧
      (fullCubicCentralizer cubic X).relIndex (fullCubicNormalizer cubic X) = 2 := by
  intro ht cubic X
  exact ⟨fullCubicProjection_surjective ht cubic X,fullCubicProjection_ker_zpowers ht cubic X,
    fullCubicProjection_kernel_card ht cubic X,⟨fullCubicTripleQuotientEquiv ht cubic X⟩,
    fullCubicCentralizer_center_image ht cubic X,fullCubicCentralizer_center_card ht cubic X,
    ⟨fullCubicCentralQuotientEquiv ht cubic X⟩,fullCubicSimpleProjection_conj ht cubic X,
    fullCubicDerived_quasisimple ht cubic X,fullCubicCentralizer_layer ht cubic X,
    fullCubicDerived_index_dvd_two ht cubic X,fullCubicCentralizer_layer_eq_top_iff ht cubic X,
    fullCubicNormalizer_core_intersection ht cubic X,fullCubicNormalizerProjection_surjective ht cubic X,
    fullCubicNormalizerProjection_ker ht cubic X,⟨fullCubicNormalizerQuotientEquiv ht cubic X⟩,
    fullCubicCentralizer_normalizer_index ht cubic X⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
