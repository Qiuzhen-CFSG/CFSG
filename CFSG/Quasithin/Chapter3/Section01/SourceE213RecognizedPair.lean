module
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalSymplecticExceptions
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.MiddleRecognition
/-!
# The original qrc action from a recognized E.2.7 pair

The source qrc geometry supplies the actual Sylow, maximal two-core,
outside-core, and characteristic-two inputs for the E.2.13 action estimate.
Thus a literal recognized pair for the intrinsic H-module gives the cubic
bound on the original M₀ image action. This isolates exactly the remaining
symplectic recognition producer; no action or normalization premise remains.

Source: Aschbacher--Smith E.2.7--13, printed pp.219--225, in the original
outside-core application of 3.1.6, printed pp.573--574.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- A recognized pair on the literal intrinsic module discharges the original
qrc action bound. The remaining hypothesis is geometric recognition only. -/
theorem QrcHypotheses.cubicRatio_le_two_of_recognized_pair
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hout : ¬ V ≤ H.pCoreIn 2)
    (hp : ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (hr : ChapterE.Witnesses.SymplecticFour.HasRecognizedPair
        (T.subtype h.right_mem.1.1.2)
        (ChapterB.minimalParabolicMax (T.subtype h.right_mem.1.1.2) hp)
        (V.subgroupOf H)) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 := by
  let := h.module_elementary
  let S := T.subtype h.right_mem.1.1.2
  let W := V.subgroupOf H
  have hVH : V ≤ H := h.module_le_sylow.trans h.right_mem.1.1.2
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  have hWS : W ≤ (S : Subgroup H) := fun _ hx => h.module_le_sylow hx
  have hTV : (S : Subgroup H) ≤ normalizer (W : Set H) := h.intrinsic_module_normalized
  have hvn : (W.subgroupOf (S : Subgroup H)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWS).mpr hTV
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hp).pCoreIn 2 :=
    h.intrinsic_module_le_maximal_core hG hM hp
  have hWout : ¬ W ≤ ChapterB.minimalParabolicCore S hp := by
    intro he
    have hc : W ≤ pCore 2 H := by
      rw [←ChapterB.minimalParabolic_sylow_inf_core S hp]
      exact le_inf hWS he
    apply hout
    have hmap := map_mono (f := H.subtype) hc
    change (V.subgroupOf H).map H.subtype ≤ H.pCoreIn 2 at hmap
    simpa only [map_subgroupOf_eq_of_le hVH] using hmap
  have hfit : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp
        (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) h.right_mem.1.1))
  exact h.cubicRatio_le_nat_of_intrinsic_action 2
    (ChapterE.Witnesses.SymplecticFour.source_cubicRatio_le_two_of_recognized_pair
      S hp W S hWS hvn hWcore hWout hfit le_rfl hTV hr)

/-- Recognition through the full original maximal core discharges the same
qrc action bound, preserving the literal quotient map and module image. -/
theorem QrcHypotheses.cubicRatio_le_two_of_recognized_star
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hout : ¬ V ≤ H.pCoreIn 2)
    (hp : ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (hr : let S := T.subtype h.right_mem.1.1.2
      let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp)
      ChapterE.Witnesses.SymplecticFour.HasRecognizedPair
        (S.mapSurjective (QuotientGroup.mk'_surjective _))
        ((ChapterB.minimalParabolicMax S hp).map q) ((V.subgroupOf H).map q)) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 := by
  let := h.module_elementary
  let S := T.subtype h.right_mem.1.1.2
  let W := V.subgroupOf H
  have hVH : V ≤ H := h.module_le_sylow.trans h.right_mem.1.1.2
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  have hWS : W ≤ (S : Subgroup H) := fun _ hx => h.module_le_sylow hx
  have hTV : (S : Subgroup H) ≤ normalizer (W : Set H) := h.intrinsic_module_normalized
  have hvn : (W.subgroupOf (S : Subgroup H)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWS).mpr hTV
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hp).pCoreIn 2 :=
    h.intrinsic_module_le_maximal_core hG hM hp
  have hWout : ¬ W ≤ ChapterB.minimalParabolicCore S hp := by
    intro he
    have hc : W ≤ pCore 2 H := by
      rw [←ChapterB.minimalParabolic_sylow_inf_core S hp]
      exact le_inf hWS he
    apply hout
    have hmap := map_mono (f := H.subtype) hc
    change (V.subgroupOf H).map H.subtype ≤ H.pCoreIn 2 at hmap
    simpa only [map_subgroupOf_eq_of_le hVH] using hmap
  have hfit : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp
        (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) h.right_mem.1.1))
  exact h.cubicRatio_le_nat_of_intrinsic_action 2
    (ChapterE.Witnesses.SymplecticFour.source_cubicRatio_le_two_of_recognized_star
      S hp W S hWS hvn hWcore hWout hfit le_rfl hTV hr)

/-- The complete outside-core action assembly from the remaining E.2.7
producer. Its premise asks for the literal recognized pair, not a bound. -/
theorem QrcHypotheses.outsideCore_cubicRatio_le_two_of_symplectic_recognition
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hout : ¬ V ≤ H.pCoreIn 2)
    (hrec : h.HasSymplecticMiddleOutsideCoreModel →
      ∃ hp : ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤,
        let S := T.subtype h.right_mem.1.1.2
        let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp)
        ChapterE.Witnesses.SymplecticFour.HasRecognizedPair
          (S.mapSurjective (QuotientGroup.mk'_surjective _))
          ((ChapterB.minimalParabolicMax S hp).map q) ((V.subgroupOf H).map q)) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 := by
  rcases h.outsideCore_cubicRatio_le_two_or_symplectic_middle_model hG hM hu hout with hb | hs
  · exact hb
  · obtain ⟨hp,hr⟩ := hrec hs
    exact h.cubicRatio_le_two_of_recognized_star hG hM hout hp hr

end CFSG.Quasithin.Chapter3
