module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.HexadElementary
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadCentralizers

/-!
# Fixed-space bounds at the original Mathieu hexad overlap

Apply the general type-J4 bounds to the original full hexad preimage,
retaining its cubic quotient, Sylow and embedded E₁ and E. The literal
quotient image of A ≤ Q has order |E₁:C_E₁(A)|. For |A|>512 the
centralizer in E lies in E₁, giving |E:C_E(A)|=16|A*|. The original
fixed preimage has order at most 512 for every noncore two-core actor;
more than two quotient actors cut out exactly E₁.

Source: Aschbacher–Segev (4.6), Invent. Math. 105 (1991), p.598,
DOI 10.1007/BF01232280; Aschbacher–Smith 8.2.12–14. These are
centralizer bounds for the general Thompson argument, including its rank-two
Q-image boundary. Actors outside Q and full normalizer recognition remain separate steps.
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

/-- The source centralizer bounds, with the same original overlap and full quotient maps. -/
theorem sourceOrbit_m24_hexad_centralizer_bounds :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)),
      ∃ B, ∃ hB : B ∈ m22Blocks,
        let I := (normalizer (D.sourceOrbit : Set G)).subgroupOf
          (centralizer ({(z : G)} : Set G))
        let U := originalHexadFixedCore ht cubic X B
        let F := originalHexadElementary ht cubic X B
        let Q := Recognition.JankoFour.core (z : G)
        letI := originalHexadElementary_normal ht cubic X hB
        let q := QuotientGroup.mk' (F.subgroupOf (originalPlaneHexad cubic B))
        I = originalPlaneHexad cubic B ∧
        (∀ A : Subgroup (centralizer ({(z : G)} : Set G)), A ≤ Q →
          Nat.card ((A.subgroupOf (originalPlaneHexad cubic B)).map q) *
            Nat.card (U ⊓ centralizer (A : Set (centralizer ({(z : G)} : Set G))) :
              Subgroup (centralizer ({(z : G)} : Set G))) = 128) ∧
        (∀ A : Subgroup (centralizer ({(z : G)} : Set G)), A ≤ Q → 512 < Nat.card A →
          ((F ⊓ centralizer (A : Set (centralizer ({(z : G)} : Set G)))).subgroupOf F).index =
            16 * Nat.card ((A.subgroupOf (originalPlaneHexad cubic B)).map q)) ∧
        (∀ P : Subgroup (centralizer ({(z : G)} : Set G)), P ≤ I.pCoreIn 2 → ¬ P ≤ Q →
          Nat.card (commutatorPreimage Q P (center (centralizer ({(z : G)} : Set G)))) ≤ 512) ∧
        (∀ P : Subgroup (centralizer ({(z : G)} : Set G)), P ≤ I.pCoreIn 2 →
          2 < Nat.card (P.map (QuotientGroup.mk' Q)) →
            commutatorPreimage Q P (center (centralizer ({(z : G)} : Set G))) = U) ∧
        (∀ A : Subgroup (centralizer ({(z : G)} : Set G)), A ≤ Q → Nat.card A = 512 →
          (((F ⊓ centralizer (A : Set (centralizer ({(z : G)} : Set G)))) ⊔ U).subgroupOf F).index ≥ 8) := by
  intro ht cubic X
  obtain ⟨B,hB,hpre,_⟩ := D.sourceOrbit_m24_hexad_elementary
    h hmany hV hq hnon a E hE z hz hne hquot cubic X
  refine ⟨B,hB,hpre,?_,?_,?_,?_,?_⟩
  · exact fun A hA => originalHexadQuotient_core_centralizer_card ht cubic X hB A hA
  · exact fun A hA hc => originalHexad_large_core_index ht cubic X hB A hA hc
  · intro P hP hn
    rw [hpre] at hP
    exact originalHexad_noncore_fixed_card_le ht cubic X hB P hP hn
  · intro P hP hc
    rw [hpre] at hP
    exact originalHexad_large_actor_fixed_eq ht cubic X hB P hP hc
  · exact fun A hA hc => originalHexad_core_boundary_index ht cubic X hB A hA hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
