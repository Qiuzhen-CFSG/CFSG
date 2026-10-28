module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48Ordinary
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.BinaryUnitaryExclusion

/-!
# The strong-quasithin ordinary sieve for the original binary doubled orbit

The full center of the ordinary component is its two-core. Thus its central
quotient is strongly quasithin and satisfies the sharper Theorem C catalogue.
The actual six-space and residual section exclude every odd, alternating,
binary-linear-two, Suzuki, small sporadic and binary-linear-four row. The
genuine C.2.8 perfect-core argument also excludes the unitary Bender row.
Only the Theorem C rank-two families, SL₅(2), and four named sporadic models
remain. The original component, full center, residual and orbit are unchanged.

Source: Aschbacher--Smith C.3.5 and C.4.8, printed pp.150--154,
in the original Chapter 12 non-FF doubled application.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterA.Section02
open ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The source ordinary quotient has only these three classes of models.
In particular, no Bender, Sp₆(2), PSU₄ or PSU₅ alternative is introduced. -/
theorem sourceOrbit_binary_witness_ordinary_three_cases
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    (∃ f : ℕ, IsTheoremCRankTwoModel (K ⧸ center K) f) ∨
      ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
      ∃ name : SporadicName, (name = .m24 ∨ name = .j4 ∨ name = .he ∨ name = .ru) ∧
        Nonempty ((K ⧸ center K) ≃* name.Carrier) := by
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  obtain ⟨hr,j,_,f,hf⟩ :=
    D.sourceOrbit_binary_witness_ordinary_quotient h hd F hF hmodel hw hWJ hJC K hK
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center K))
      (QuotientGroup.mk'_surjective _)
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)
  have hsq : IsStronglyQuasithin (K ⧸ center K) := by
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ (hz.symm ▸ pCore_isPGroup)).trans
      ((hc.sqtk.subgroup K).stronglyQuasithin p hp ho)
  have hm := theoremC_knownSimple inferInstance (Group.IsPerfect.not_isMulCommutative _)
    hsq ((hc.sqtk.isKGroup.subgroup K).quotient _)
  cases hm with
  | alternating n hn he =>
      obtain ⟨e⟩ := he
      rw [primeRank_equiv 2 e] at hr
      have hb := DoubledBinaryPlacedModels.alternating_twoRank_le_four (by omega : n ≤ 9)
      omega
  | odd hm =>
      exact (DoubledBinaryOddRanks.no_odd_model_of_rank_six hr hm.toTheoremBOddModel).elim
  | bender hm =>
      obtain ⟨n,hn,he⟩ := DoubledBinaryPlacedModels.bender_unitary_of_section hm j.range f hf
      exact (hc.no_ordinary_component_binary_unitary_three K hK hn he).elim
  | rank_two f hm => exact Or.inl ⟨f,hm⟩
  | linear_binary n hn hm =>
      rcases hn with rfl | rfl
      · have hb := DoubledBinaryPlacedModels.binary_linear_four_twoRank_le_four hm
        omega
      · exact Or.inr (Or.inl hm)
  | sporadic hm =>
      exact Or.inr (Or.inr
        (DoubledBinaryPlacedModels.sporadic_remaining_of_rank_six hr hm.toTheoremBSporadicModel))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
