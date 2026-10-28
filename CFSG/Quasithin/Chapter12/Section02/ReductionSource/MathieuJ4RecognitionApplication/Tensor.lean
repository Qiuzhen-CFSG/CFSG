module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.Tensor

/-!
# The original Mathieu application of the marked tensor action

The original marked M₂₄ data and full cubic quotient construct the same
three-space Z and rank-four pair section W. Their actual radical quotient
is linearly equivalent to Z* tensor W, equivariantly for the full normalizer
quotient and its original Aut(Z) × S₅ marking. No additional action, geometry,
or representation input is assumed.

This completes the dual-natural tensor factor. Identifying the same W as
the natural L₂(4) module and proving ambient J₄ recognition remain open.

Source: Aschbacher–Smith 8.2.12–14, printed pp.722–723;
Aschbacher–Segev (1991), (4.4), pp.597–598, DOI 10.1007/BF01232280.
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

/-- The literal normalizer action is the marked dual-natural tensor action, from the original Mathieu inputs. -/
theorem sourceOrbit_m24_three_space_tensor
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
      letI := d.R_normal_in_S_intrinsic
      letI := d.R_center_quotient_elementary ht
      letI := d.multiplicitySpace_elementary ht
      ∃ F : Additive (d.R ⧸ center d.R) ≃ₗ[ZMod 2]
          Module.Dual (ZMod 2) (Additive d.space) ⊗[ZMod 2] Additive d.multiplicitySpace,
        ∀ n : normalizer (d.space : Set G) ⧸ d.R.subgroupOf (normalizer (d.space : Set G)),
          ∀ v : Additive (d.R ⧸ center d.R),
        F (Additive.ofMul (d.radicalQuotientAction ht n v.toMul)) =
          TensorProduct.congr
            (binaryLinearAut (d.markedNormalizerQuotientEquiv ht n).1).symm.dualMap
            (binaryLinearAut (d.markedMultiplicityAction ht (d.markedNormalizerQuotientEquiv ht n).2))
            (F v) := by
  let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,⟨d⟩⟩ := source_three_space_data_exists ht
  exact ⟨cubic,X,d,d.exists_radical_normalizer_tensor_equiv ht⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
end
