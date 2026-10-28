module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaNumericalInput
public import CFSG.Quasithin.Chapter3.Section01.SourceDualNumerical
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalSymplecticExceptions
public import CFSG.Quasithin.Chapter3.Section01.SourceE213RecognizedPair

/-!
# The numerical source alternatives on the original central Omega module

The canonical action on Ω₁Z(O₂(L₀T)) satisfies the actual QRC hypotheses.
The complete dual-FF and odd-linear estimates give its cubic ratio bound
unless the marked nonbinary symplectic middle case remains. Recognition
on the literal H/core quotient discharges that case through E.2.13.

Source: Aschbacher--Smith 3.1.8(1), E.2.7--13, and 9.2.2(1).
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

theorem omegaCenter_core_ne_bot : omegaCenterIn ((localJoin T L).pCoreIn 2) ≠ ⊥ := by
  intro he
  apply D.module_ne_bot
  exact bot_unique ((m.module_eq.le.trans m.fullModule_le_omegaCenter_core).trans_eq he)

theorem omegaCenter_core_cubicRatio_le_two_or_symplectic {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    cubicRatio (ChapterD.UniqueFactor.imageRepresentation (localJoin T L)
      (omegaCenterIn ((localJoin T L).pCoreIn 2)) join_normalizes_omegaCenter_core) ≤ 2 ∨
    (m.omegaCenter_core_qrcHypotheses hH).HasSymplecticMiddleOutsideCoreModel := by
  let h := m.omegaCenter_core_qrcHypotheses hH
  have hu := D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)
  rcases h.cubicRatio_le_two_or_source_branch D.simpleQTKE hu.1 hu.2.2
    m.omegaCenter_core_ne_bot with hb | ho | hd
  · exact Or.inl hb
  · exact h.outsideCore_cubicRatio_le_two_or_symplectic_middle_model
      D.simpleQTKE hu.1 hu.2.2 ho
  · exact Or.inl (h.cubicRatio_le_two_of_literal_dualFF D.simpleQTKE hu.1 hu.2.2 hd)

theorem omegaCenter_core_cubicRatio_le_two_of_recognized_star {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hout : ¬ omegaCenterIn ((localJoin T L).pCoreIn 2) ≤ H.pCoreIn 2)
    (hp : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    (hr : let S := T.subtype hH.1.1.2
      let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp)
      ChapterE.Witnesses.SymplecticFour.HasRecognizedPair
        (S.mapSurjective (QuotientGroup.mk'_surjective _))
        ((ChapterB.minimalParabolicMax S hp).map q)
        (((omegaCenterIn ((localJoin T L).pCoreIn 2)).subgroupOf H).map q)) :
    cubicRatio (ChapterD.UniqueFactor.imageRepresentation (localJoin T L)
      (omegaCenterIn ((localJoin T L).pCoreIn 2)) join_normalizes_omegaCenter_core) ≤ 2 :=
  (m.omegaCenter_core_qrcHypotheses hH).cubicRatio_le_two_of_recognized_star
    D.simpleQTKE (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1
    hout hp hr

/-- All numerical cases are discharged once the remaining marked E.2.7 pair
is recognized on the original H/core quotient. -/
theorem omegaCenter_core_cubicRatio_le_two_of_symplectic_recognition {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hrec : (m.omegaCenter_core_qrcHypotheses hH).HasSymplecticMiddleOutsideCoreModel →
      ∃ hp : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤,
        let S := T.subtype hH.1.1.2
        let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp)
        ChapterE.Witnesses.SymplecticFour.HasRecognizedPair
          (S.mapSurjective (QuotientGroup.mk'_surjective _))
          ((ChapterB.minimalParabolicMax S hp).map q)
          (((omegaCenterIn ((localJoin T L).pCoreIn 2)).subgroupOf H).map q)) :
    cubicRatio (ChapterD.UniqueFactor.imageRepresentation (localJoin T L)
      (omegaCenterIn ((localJoin T L).pCoreIn 2)) join_normalizes_omegaCenter_core) ≤ 2 := by
  let h := m.omegaCenter_core_qrcHypotheses hH
  have hu := D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)
  rcases h.cubicRatio_le_two_or_source_branch D.simpleQTKE hu.1 hu.2.2
    m.omegaCenter_core_ne_bot with hb | ho | hd
  · exact hb
  · exact h.outsideCore_cubicRatio_le_two_of_symplectic_recognition
      D.simpleQTKE hu.1 hu.2.2 ho hrec
  · exact h.cubicRatio_le_two_of_literal_dualFF D.simpleQTKE hu.1 hu.2.2 hd

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
