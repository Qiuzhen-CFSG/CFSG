module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSixOrdinarySource
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpOrdinary
-- The ordinary Theorem-C quotient calculation is internal to this source family.
import all CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpOrdinary

/-!
# The actual ordinary component in the doubled A6 reciprocal source

The full original orbit has rank eight and has no fixed points for the
intersection residual. It therefore embeds in the containing ordinary
component modulo its center. The actual Theorem C quotient catalogue then
leaves the rank-two characteristic-two rows and J4; the Bender rows are
excluded using the original nontrivial commutator module in the full two-core.
No equality of the original seed and the full orbit is imposed.
Source: Aschbacher--Smith C.3.2--5, 4.4.6 and 7.5.5,
printed pp.149--150,620,701, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter4 Chapter4.Section04
open Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape ChapterA.Section02 ClassificationModels

private theorem rank_eight_C_models {Q : Type*} [Group Q] [Finite Q]
    (hm : IsTheoremCModel Q) (hr : 8 ≤ primeRank 2 Q) :
    IsBenderModel Q ∨ (∃ n : ℕ, IsTheoremCRankTwoModel Q n) ∨
      Nonempty (Q ≃* Janko4.Model) := by
  cases hm with
  | alternating n hn he =>
    exact (no_small_alternating_of_twoRank_ge_eight hr (by omega) he).elim
  | odd ho => exact (no_theoremB_odd_model_of_twoRank_ge_eight hr ho.toTheoremBOddModel).elim
  | bender hb => exact Or.inl hb
  | rank_two n hn => exact Or.inr (Or.inl ⟨n,hn⟩)
  | linear_binary n hn he => exact (no_binary_linear_of_twoRank_ge_eight hr hn he).elim
  | sporadic hs => exact Or.inr (Or.inr
      (theoremBSporadic_j4_of_twoRank_ge_eight hr hs.toTheoremBSporadicModel))

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The whole doubled A6 orbit has elementary two-rank eight. -/
theorem sourceOrbit_six_primeRank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) :
    primeRank 2 D.sourceOrbit = 8 := by
  have hc : Nat.card D.sourceOrbit = 2 ^ 8 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,D.sourceOrbit_six_dimension h hd hmodel] at hh
    exact hh
  have he := IsElementaryAbelian.log_card_eq_primeRank (p := 2) D.sourceOrbit
  rw [hc,Nat.log_pow (by decide : 1 < (2 : ℕ))] at he
  exact he.symm

/-- The literal whole-orbit C.2.8 gives a perfect intersection residual,
its moved two-core subgroup, and trivial fixed subgroup without a new guard. -/
theorem sourceOrbit_six_witness_residual_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) :
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    Group.IsPerfect F ∧ D.sourceOrbit ≤ F.pCoreIn 2 ∧
      D.sourceOrbit = ⁅D.sourceOrbit,F⁆ ∧
      D.sourceOrbit ⊓ centralizer (F : Set G) = ⊥ := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_six_witness_hypothesisC28 h hd hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hs : conjugateSpanBy F (H ⊓ normalizer (L : Set G)) = F := hc.normalized_span_eq hn
  have hUF : D.sourceOrbit ≤ F := hs ▸ hc.module_le
  have hFN : F ≤ normalizer (D.sourceOrbit : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans D.sourceOrbit_component_normalizes
  have hperfect : Group.IsPerfect F := hs ▸ hc.span_perfect
  have hm : D.sourceOrbit = ⁅D.sourceOrbit,F⁆ := hs ▸ hc.module_commutator
  exact ⟨hperfect,
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.sourceOrbit) hUF hFN,
    hm,D.sourceOrbit_six_witness_fixed_eq_bot h hd hmodel hw⟩

/-- The literal ordinary reciprocal component has a rank-two or J4 central
quotient. The full source orbit, residual kernel and original witness are
retained; no odd-normalizer uniqueness is assumed. -/
theorem sourceOrbit_six_ordinary_component_catalogue
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    8 ≤ primeRank 2 (K ⧸ center K) ∧
      ((∃ n : ℕ, IsTheoremCRankTwoModel (K ⧸ center K) n) ∨
        Nonempty ((K ⧸ center K) ≃* Janko4.Model)) := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let K₀ := K.map H.subtype
  have hc := D.sourceOrbit_six_witness_hypothesisC28 h hd hmodel hw hWJ hJC
  obtain ⟨hperfect,hUF,hcomm,hfix⟩ :=
    D.sourceOrbit_six_witness_residual_data h hd hmodel hw hWJ hJC
  let : Group.IsPerfect F := hperfect
  have hFK : F ≤ K₀ := by
    intro f hf
    exact ⟨⟨f,hc.component_le.trans hc.local_le hf⟩,
      hc.ordinary_component_contains_original K hK hf,rfl⟩
  let e := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let z := QuotientGroup.congr (center K₀) (center K) e
    (Theory.GroupTheory.FixedElementary.map_center e)
  have hr : 8 ≤ primeRank 2 (K₀ ⧸ center K₀) := by
    rw [←D.sourceOrbit_six_primeRank h hd hmodel]
    exact rank_le_central_quotient_of_fixed_eq_bot hFK
      (hUF.trans (pCoreIn_le 2 F)) hfix
  have hrK : 8 ≤ primeRank 2 (K ⧸ center K) := by
    simpa only [primeRank_equiv 2 z] using hr
  refine ⟨hrK,?_⟩
  rcases rank_eight_C_models (ordinary_theoremC_model hc K hK) hrK with hb | hrank
  · exact (no_bender_of_residual_module K₀ F D.sourceOrbit hFK hUF
      D.sourceOrbit_weakClosure_setup.nontrivial hcomm (hb.of_mulEquiv z)).elim
  · exact hrank

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
