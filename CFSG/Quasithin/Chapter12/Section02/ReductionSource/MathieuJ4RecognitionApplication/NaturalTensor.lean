module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.NaturalTensor

/-!
# The original Mathieu application of the natural tensor module

The marked M24 inputs and full cubic quotient construct the same three-space
and pair section. The original marked alternating-five action on that section
is the natural SL2(4) action. Applying these same coordinates to the existing
tensor equivalence retains the full normalizer action and the original
Aut(Z) times S5 marking; its A5 factor is now explicitly natural.

This discharges the remaining module clause of Aschbacher--Segev (4.4),
printed pp.597--598, DOI 10.1007/BF01232280, for the original
Aschbacher--Smith 8.2.12--14 application. Subsequent local geometry and ambient
J4 recognition remain separate conclusions, not premises of these results.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative TensorProduct
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

local instance threeSpaceElementary {z : G}
    {e : Recognition.JankoFour.CubicAutomorphismQuotient
      (Recognition.JankoFour.centralizer z ⧸ Recognition.JankoFour.core z)}
    {X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup e)}
    (d : ThreeSpaceData z e X) : IsElementaryAbelian 2 d.space := d.elementary

/-- The SAME original four-space is natural for its marked alternating-five action. -/
theorem sourceOrbit_m24_three_space_natural
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
        pCore 2 (centralizer ({(z : G)} : Set G))))) :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∃ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (d : ThreeSpaceData (z : G) cubic X),
      letI := d.multiplicitySpace_elementary ht
      ∃ (A : alternatingGroup (Fin 5) ≃* SL2FourNatural.SL)
        (F : Additive d.multiplicitySpace ≃ₗ[ZMod 2] SL2FourNatural.V),
        ∀ (b : alternatingGroup (Fin 5)) (w : Additive d.multiplicitySpace),
          F (Additive.ofMul (d.markedMultiplicityAction ht b.val w.toMul)) =
            SL2FourNatural.action (A b) (F w) := by
  let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,⟨d⟩⟩ := source_three_space_data_exists ht
  exact ⟨cubic,X,d,d.exists_multiplicity_natural_equiv ht⟩

/-- The literal full normalizer action is dual-natural tensor natural, with its S5 marking retained. -/
theorem sourceOrbit_m24_three_space_natural_tensor
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
        pCore 2 (centralizer ({(z : G)} : Set G))))) :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∃ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (d : ThreeSpaceData (z : G) cubic X),
      letI := d.R_normal_in_normalizer
      letI := d.R_center_quotient_elementary ht
      ∃ F : Additive (d.R ⧸ center d.R) ≃ₗ[ZMod 2]
          Module.Dual (ZMod 2) (Additive d.space) ⊗[ZMod 2] SL2FourNatural.V,
        (∀ n : normalizer (d.space : Set G) ⧸ d.R.subgroupOf (normalizer (d.space : Set G)),
          ∀ v : Additive (d.R ⧸ center d.R),
          F (Additive.ofMul (d.radicalQuotientAction ht n v.toMul)) =
            TensorProduct.congr
              (binaryLinearAut (d.markedNormalizerQuotientEquiv ht n).1).symm.dualMap
              (d.naturalMarkedAction ht (d.markedNormalizerQuotientEquiv ht n).2) (F v)) ∧
        ∀ b : alternatingGroup (Fin 5),
          d.naturalMarkedAction ht b.val = SL2FourNatural.action (d.markedNaturalActorEquiv ht b) := by
  let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,⟨d⟩⟩ := source_three_space_data_exists ht
  let := d.R_normal_in_normalizer
  let := d.R_center_quotient_elementary ht
  obtain ⟨F,hF⟩ := d.exists_radical_natural_tensor_equiv ht
  exact ⟨cubic,X,d,F,hF,d.naturalMarkedAction_alternating ht⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
end
