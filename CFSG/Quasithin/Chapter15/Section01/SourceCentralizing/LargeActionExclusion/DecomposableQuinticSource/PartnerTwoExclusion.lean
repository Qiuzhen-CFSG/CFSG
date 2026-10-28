module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.PartnerTwoPointOrdinaryModels
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinary

/-!
# Exclusion of the original order-two quintic partner

The actual support point supplies an ordinary outside component. Its Sylow
has a genuine permuting quintic actor, and the original moving support acts
faithfully with order sixteen. The generic ordinary catalogue gives the
contradiction at this literal point, retaining the original denominator.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The literal order-two partner branch of the original quintic source is impossible. -/
theorem PreparedChosenModule.decomposable_five_partner_two_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      (let Z := thompsonPlane T V (c.ambientFactor d s.first).space
       let C := M ⊓ centralizer (Z : Set G)
       letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
       Nat.card (pResidual 2 (C ⧸
         (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5) →
      False := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hratio hfive hcU hcard
  obtain ⟨a,ha,b,hb,hane,hbne,hU,hE,L,hZ,hZcard,hc,hMZ,ho,hSylG,hSn,hI,hseed,hQne,hcontrol,hn,
      hTn,hTQ,hresN,hYseed,h115,hLc,hout,hquasi,hloc,hSyl,houtM,hnL,hmove,hord⟩ :=
    h.decomposable_five_partner_two_point_ordinary
      hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hratio hfive hcU hcard
  let Z1 := zpowers a
  let Z₀ := thompsonPlane T V (c.ambientFactor d s.first).space
  let G1 := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ G1
  let C := M ⊓ G1
  let R := (pResidual 2 C).map C.subtype
  let W := ⁅V,R⁆
  let Rorig := (pResidual 2 (M ⊓ centralizer (Z₀ : Set G) : Subgroup G)).map
    (M ⊓ centralizer (Z₀ : Set G)).subtype
  have hReq : R = Rorig := by
    have hC : C = M ⊓ centralizer ({a} : Set G) := by
      simp only [C, G1, Z1, zpowers_eq_closure, centralizer_closure]
    exact (congrArg (fun K : Subgroup G => (pResidual 2 K).map K.subtype) hC).trans
      (s.quintic_point_residual_eq_marked h.normalized c d π hp hs hfive a ha hane)
  have hnOrig : Rorig ⊔ ⁅V,Rorig⁆ ≤ normalizer (L : Set G) := by
    rw [← hReq]
    exact hnL
  have hmOrig : ⁅L,⁅V,Rorig⁆⁆ ≠ ⊥ := by
    rw [← hReq]
    exact hmove
  have hrank : primeRank 2 (internalActionImage M V h.normalized) ≤ 2 := by
    subst V
    exact source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
      (Or.inr (Or.inr (Or.inl hdec)))
  have hactors := (h.thompson_actors T hM.1.2 hratio
    (fun A hA => hA.rank_le_of_primeRank_le hrank)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm hactors c d π hp hdec).1
  have hW : W = plane V (c.ambientFactor d s.second).space := by
    change ⁅V,R⁆ = _
    rw [hReq]
    exact (s.full_residual_geometry hM.1.2 h.normalized c d π hp hs hJi).2.1
  have hfaith16 : ∃ hWN : W ≤ normalizer (L : Set G),
      Nat.card (internalActionImage W L hWN) = 16 := by
    rw [hW]
    obtain ⟨hBL,_,hcardB⟩ := h.decomposable_five_raw_moving_support_action
      hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hratio hfive hnOrig hmOrig
    exact ⟨hBL,hcardB⟩
  have hSylC : Chapter1.IsSylowIn 2 S C := hSylG.restrict
    (le_inf (inf_le_left.trans hM.1.2) inf_le_right) inf_le_right
  obtain ⟨Y,hY,hperfect,hYR,hperm,_,hWY⟩ :=
    caseI_exists_permuting_quintic_actor h.normalized h.le_selected
      (hZ.trans inf_le_left) hSylC hc
  obtain ⟨hcenter,_⟩ := raw_ordinary_center hLc.1 hord ho
  obtain ⟨hnZ,hfaith,hmodels⟩ := raw_ordinary_marked_actions hG T hLc.1 hout
    (Classical.choose h115) (Classical.choose_spec h115).2 hord
  have hZne : Z1 ≠ ⊥ := (one_lt_card_iff_ne_bot Z1).mp (by
    change Nat.card Z1 = 2 at hZcard
    rw [hZcard]
    decide)
  apply h.quintic_ordinary_component_false hG T hempty hM hJ hu hZ hZne
    hLc.1 hord hcenter hquasi hSyl hnL hmove hnZ hfaith hSylG h115 hout houtM
    hcontrol hresN hn hI hfaith16 ⟨Y,hY,hperfect,hYR,hperm,hWY⟩
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨α,_,hα⟩ := (hmodels z hz hzne).2
  exact ⟨α,hα⟩

end CFSG.Quasithin.Chapter15.Section01
