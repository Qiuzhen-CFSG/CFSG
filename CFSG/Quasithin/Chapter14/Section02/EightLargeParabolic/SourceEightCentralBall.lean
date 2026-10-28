module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceComplementCenter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SixPathCentralSource

/-!
# The original central involution fixes the eight-endpoint three-ball

The reduced middle center is nontrivial and lies in the center of the full
original extraspecial core. That center has order two, so the two subgroups
are equal through the literal reduced-completion inclusion. The actual
critical pair then makes every lift fixing the marked endpoint fix its whole
radius-three ball. This supplies the central correction used for the chosen
reflection on the same universal tree.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree
open Subgroup.CosetGeometry
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightCentralBall
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal source covering carries original full-core center elements
fixing the eight base into its radius-three pointwise fixer. -/
@[expose] def HasEightCentralBall (h : HypothesisF11 L S) (P : Subgroup G) : Prop :=
  ∀ z : (reducedAmalgam L S).Universal,
    z • base (Universal.cosetFamily (reducedAmalgam L S)) true =
      base (Universal.cosetFamily (reducedAmalgam L S)) true →
    ((G₀ L S).subtype.comp (bOne_tree_map h)) z ∈ centerIn (P.pCoreIn 2) →
    z ∈ graphBallFixer (sourceGraph (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) true) 3

private theorem central_ball_of_middle (h : HypothesisF11 L S) (P : Subgroup G)
    (hcenter : (Z (reducedFamily L S) (RankTwo.base (reducedFamily L S) true)).map
      (G₀ L S).subtype = centerIn (P.pCoreIn 2))
    {u : RankTwo.Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) (RankTwo.base (reducedFamily L S) false) u)
    (hne : ⁅Z (reducedFamily L S) (RankTwo.base (reducedFamily L S) false),
      Z (reducedFamily L S) u⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 2)
    (hu : (RankTwo.graph (reducedFamily L S)).Adj (RankTwo.base (reducedFamily L S) true) u) :
    HasEightCentralBall h P := by
  intro z hzfix hz
  have hz' : bOne_tree_map h z ∈ Z (reducedFamily L S) (RankTwo.base (reducedFamily L S) true) := by
    rw [←hcenter] at hz
    obtain ⟨y,hy,he⟩ := hz
    exact ((G₀ L S).subtype_injective he) ▸ hy
  exact source_bTwo_middle_radius_three h true hc hne hb
    ⟨by change false ≠ true; decide,incident_base _ _ _⟩ hu z hzfix hz'
private theorem eight_pair_central_ball {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (P : Subgroup G)
    (hcenter : (Z (reducedFamily ![U,K] S)
      (RankTwo.base (reducedFamily ![U,K] S) true)).map (G₀ ![U,K] S).subtype =
        centerIn (P.pCoreIn 2)) : HasEightCentralBall h.swap P := by
  obtain ⟨u,hc,hne,hu⟩ := SourceCriticalGeometry.reversed_base_critical h eK eU
  have hb : b (reducedFamily ![U,K] S) = 2 := (pair_b_swap K U S).trans
    (SourceCriticalGeometry.critical_distance_two h eK eU)
  exact central_ball_of_middle h.swap P hcenter hc hne hb hu

end Geometry

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR
local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "Sₛ" => (T : Subgroup G)
local notation "Fₛ" => reducedFamily Lₛ Sₛ

/-- The actual reduced middle center maps onto the original full-core center. -/
theorem source_eight_middle_center :
    (Z Fₛ (RankTwo.base Fₛ true)).map (G₀ Lₛ Sₛ).subtype =
      centerIn (H.pCoreIn 2) := by
  let h : HypothesisF11 Lₛ Sₛ :=
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  let ι := (G₀ Lₛ Sₛ).subtype
  let β := RankTwo.base Fₛ true
  have hQ : (Q Fₛ β).map ι = H.pCoreIn 2 := by
    have he := reduced_base_Q_map h true
    change (Q Fₛ β).map ι = (parabolic (locals T M Mc H) Sₛ 0).pCoreIn 2 at he
    rwa [(source_parabolics hG T hempty hM hu hmany hcard e H hH eR).1] at he
  have hle : (Z Fₛ β).map ι ≤ centerIn (H.pCoreIn 2) := by
    rintro x ⟨z,hz,rfl⟩
    have hz' := (mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U (reduced_triple h) β).1 hz)
    refine ⟨hQ ▸ mem_map_of_mem ι hz'.1,?_⟩
    intro q hq
    obtain ⟨r,hr,rfl⟩ := hQ.symm ▸ hq
    exact congrArg ι (hz'.2.1 r hr)
  let _ := (source_core_structure hG T hempty hM hu hmany hcard e H hH eR).1
  have hc : Nat.card (centerIn (H.pCoreIn 2)) = 2 := by
    rw [centerIn_eq_map_center,card_map_of_injective (H.pCoreIn 2).subtype_injective]
    exact IsExtraspecial.center_order_p 2 _
  have hn : (Z Fₛ β).map ι ≠ ⊥ := by
    intro he
    exact base_Z_ne_bot (reduced_triple h) true
      ((map_eq_bot_iff_of_injective _ (G₀ Lₛ Sₛ).subtype_injective).mp he)
  apply eq_of_le_of_card_ge hle
  have hp := ((Z Fₛ β).map ι).one_lt_card_iff_ne_bot.mpr hn
  omega

set_option maxHeartbeats 800000 in
/-- The original core center supplies the whole radius-three fixation for
any lift fixing the marked eight endpoint. -/
theorem source_eight_core_center_radius_three :
    HasEightCentralBall
      (show HypothesisF11 Lₛ Sₛ from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) H := by
  obtain ⟨hF,hS,_,_,_⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  have hq : IsRankOneModel (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
    .linear 3 (by decide) ⟨GaloisField 2 3,inferInstance,inferInstance,
      GaloisField.card 2 3 (by decide),⟨eR⟩⟩
  have hnot := source_normal_amalgam_not_normalizes hG T hempty hM hu hmany hcard e H hH
    (pResidual 2 H) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2)) rfl hq
  obtain ⟨eU⟩ := (source_residual_actor_movement hG T hempty hM hu hmany hcard e
    (secondSylow T M Mc H) hS le_sup_left hnot).2
  exact eight_pair_central_ball hF (residualQuotientEquiv H eR) eU H
    (source_eight_middle_center hG T hempty hM hu hmany hcard e H hH eR)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightCentralBall
