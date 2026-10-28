module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.HexadFixedSpace
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadFixedStructure

/-!
# The constructed elementary subgroup at the original Mathieu overlap

The standard native fixed-space premises are now discharged. At the same
original point-plane overlap, the literal E₁ is elementary of order 128;
its product with O₂(G₁,₃) intersect C_H(X) is elementary of order 2048,
normalized by the whole overlap, and meets Q exactly in E₁. The original
Mathieu data, cubic quotient and Sylow subgroup are retained throughout.

Source: Aschbacher–Segev (4.6), Invent. Math. 105 (1991), p.598,
DOI 10.1007/BF01232280; Aschbacher–Smith 8.2.12–14. Thompson equality,
full normalizer/module marking and ambient recognition remain later duties.
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

/-- The actual source E construction, with no remaining fixed-space inputs. -/
theorem sourceOrbit_m24_hexad_elementary :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)),
      ∃ B ∈ m22Blocks,
        let I := (normalizer (D.sourceOrbit : Set G)).subgroupOf
          (centralizer ({(z : G)} : Set G))
        let E1 := originalHexadFixedCore ht cubic X B
        let F := originalHexadElementary ht cubic X B
        I = originalPlaneHexad cubic B ∧
        IsElementaryAbelian 2 E1 ∧ Nat.card E1=128 ∧
        IsElementaryAbelian 2 F ∧ Nat.card F=2048 ∧
        I ≤ normalizer (F : Set (centralizer ({(z : G)} : Set G))) ∧
        F ⊓ Recognition.JankoFour.core (z : G) = E1 :=
  D.sourceOrbit_m24_hexad_elementary_of_standard h hmany hV hq hnon a E hE z hz hne hquot
    NativeHexadRealization.standard_card NativeHexadRealization.standard_singular

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
