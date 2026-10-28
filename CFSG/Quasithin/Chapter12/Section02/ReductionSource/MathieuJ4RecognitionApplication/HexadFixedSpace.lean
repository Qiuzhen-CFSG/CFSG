module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.HexadCore
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadFixedTransport

/-!
# The original Mathieu product from the standard native hexad calculation

Apply the fixed-space transport at the literal original point-plane overlap,
retaining the same cubic quotient, Sylow subgroup and hexad. The two finite
native statements at the standard hexad give the actual elementary E₁ of
order 128, hence elementary E of order 2048 and its full overlap normalization.
These native premises remain explicit until their independent calculation is
integrated. This does not assert E = J(T) or ambient J4 recognition.

Source: Aschbacher–Segev (4.6), Invent. Math. 105 (1991), p.598,
DOI 10.1007/BF01232280; the original Aschbacher–Smith 8.2.12–14 consumer.
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

/-- Use only the standard native fixed-space facts to construct E₁ and E
at the original marked Mathieu overlap. -/
theorem sourceOrbit_m24_hexad_elementary_of_standard
    (hc : Nat.card (nativeHexadFixedSpace m22Hexad123)=64)
    (hs : ∀ v ∈ nativeHexadFixedSpace m22Hexad123,
      M22TripleCover.Unitary.quadraticForm v=0) :
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
        F ⊓ Recognition.JankoFour.core (z : G) = E1 := by
  intro ht cubic X
  obtain ⟨B,hB,hdata⟩ := D.sourceOrbit_m24_hexad_construction h hmany hV hq hnon
    a E hE z hz hne hquot cubic X
  have hI := hdata.1
  obtain ⟨hE1,hc1,hF,hcF,hn,hint⟩ :=
    originalHexadElementary_data_of_standard ht cubic X hc hs hB
  exact ⟨B,hB,hI,hE1,hc1,hF,hcF,hI.symm ▸ hn,hint⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
