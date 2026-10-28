module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.AlternatingLinearFive
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSevenCoordinates
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpOrdinary
-- The ordinary Theorem-C quotient calculation is internal to this source family.
import all CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpOrdinary

/-!
# The actual ordinary component in the doubled A7 reciprocal source

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
open ChapterB.QuasisimpleSource Chapter4.Section04.NormalizedRankOneOddControl
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

/-- The whole doubled A7 orbit has elementary two-rank eight. -/
theorem sourceOrbit_seven_primeRank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ)) :
    primeRank 2 D.sourceOrbit = 8 := by
  have hc : Nat.card D.sourceOrbit = 2 ^ 8 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,D.sourceOrbit_seven_dimension h hd σ hmodel] at hh
    exact hh
  have he := IsElementaryAbelian.log_card_eq_primeRank (p := 2) D.sourceOrbit
  rw [hc,Nat.log_pow (by decide : 1 < (2 : ℕ))] at he
  exact he.symm

/-- The literal ordinary reciprocal component has a rank-two or J4 central
quotient. The full source orbit, residual kernel and original witness are
retained; no odd-normalizer uniqueness is assumed. -/
theorem sourceOrbit_seven_ordinary_component_catalogue
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (hUF : D.sourceOrbit ≤
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).pCoreIn 2)
    (hcomm : D.sourceOrbit = ⁅D.sourceOrbit,
      (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype⁆)
    (hfix : D.sourceOrbit ⊓ centralizer
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype : Set G) = ⊥)
    (K : Subgroup H) (hK : IsComponent H K) :
    8 ≤ primeRank 2 (K ⧸ center K) ∧
      ((∃ n : ℕ, IsTheoremCRankTwoModel (K ⧸ center K) n) ∨
        Nonempty ((K ⧸ center K) ≃* Janko4.Model)) := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let K₀ := K.map H.subtype
  have hc := hw.2.2.2.2.2.2.1
  have hFK : F ≤ K₀ := by
    intro f hf
    exact ⟨⟨f,hc.component_le.trans hc.local_le hf⟩,
      hc.ordinary_component_contains_original K hK hf,rfl⟩
  let e := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let z := QuotientGroup.congr (center K₀) (center K) e
    (Theory.GroupTheory.FixedElementary.map_center e)
  have hr : 8 ≤ primeRank 2 (K₀ ⧸ center K₀) := by
    rw [←D.sourceOrbit_seven_primeRank h hd σ hmodel]
    exact rank_le_central_quotient_of_fixed_eq_bot hFK
      (hUF.trans (pCoreIn_le 2 F)) hfix
  have hrK : 8 ≤ primeRank 2 (K ⧸ center K) := by
    simpa only [primeRank_equiv 2 z] using hr
  refine ⟨hrK,?_⟩
  rcases rank_eight_C_models (ordinary_theoremC_model hc K hK) hrK with hb | hrank
  · have hn : (H ⊓ normalizer (L : Set G)) ≤ normalizer (F : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hw.2.2.2.2.2.2.2.2.1
    let : Group.IsPerfect F := by
      change Group.IsPerfect ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      exact (hc.normalized_span_eq hn) ▸ hc.span_perfect
    exact (no_bender_of_residual_module K₀ F D.sourceOrbit hFK hUF
      D.sourceOrbit_weakClosure_setup.nontrivial hcomm (hb.of_mulEquiv z)).elim
  · exact hrank

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
