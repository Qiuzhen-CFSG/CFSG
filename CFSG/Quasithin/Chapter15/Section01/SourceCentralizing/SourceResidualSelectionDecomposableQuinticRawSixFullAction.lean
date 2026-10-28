module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCubicPlacement

/-! The full original V acts on the same six-letter core quotient with
image of order at most four. Its kernel contains the actual moving support
of order sixteen and the disjoint marked plane of order four. Both subgroups
are literal original subgroups; the cubic core center is retained. -/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem core_action_small
    {V A B Z L : Subgroup G} [IsElementaryAbelian 2 V]
    (hAV : A ≤ V) (hBV : B ≤ V) (hZA : Z ≤ A)
    (hAB : A ⊔ B = V) (hdis : A ⊓ B = ⊥)
    (hA : Nat.card A = 16) (hB : Nat.card B = 16) (hZ : Nat.card Z = 4)
    (hnV : V ≤ normalizer (L : Set G))
    (hZL : Z ≤ centralizer (L : Set G)) (hBL : ⁅B,L⁆ ≤ L.pCoreIn 2) :
    Nat.card ((pCoreNormalizerAction 2 L).comp (inclusion hnV)).range ≤ 4 := by
  let f := (pCoreNormalizerAction 2 L).comp (inclusion hnV)
  have hZV : Z ≤ V := hZA.trans hAV
  have hZK : Z.subgroupOf V ≤ f.ker := by
    intro z hz
    apply (pCoreNormalizerAction_eq_one_iff 2 L (inclusion hnV z)).mpr
    intro l
    have hc := hZL hz l l.property
    change (l : G) * (z : G) = (z : G) * (l : G) at hc
    have he : L.normalizerMonoidHom (inclusion hnV z) l = l := by
      apply Subtype.ext
      change (z : G) * (l : G) * (z : G)⁻¹ = (l : G)
      rw [←hc,mul_inv_cancel_right]
    rw [he]
    simpa only [div_eq_mul_inv,mul_inv_cancel] using (one_mem (pCore 2 L))
  have hBK : B.subgroupOf V ≤ f.ker := by
    intro b hb
    apply (pCoreNormalizerAction_eq_one_iff 2 L (inclusion hnV b)).mpr
    intro l
    obtain ⟨u,hu,he⟩ := hBL (commutator_mem_commutator hb l.property)
    have he' : u = L.normalizerMonoidHom (inclusion hnV b) l / l := by
      apply Subtype.ext
      simpa [div_eq_mul_inv,Subgroup.coe_mul,Subgroup.coe_inv,
        normalizerMonoidHom_apply_apply_coe,coe_inclusion,commutatorElement_def] using he
    exact he' ▸ hu
  have hK : (Z ⊔ B).subgroupOf V ≤ f.ker := by
    rw [subgroupOf_sup hZV hBV]
    exact sup_le hZK hBK
  have hcv : Nat.card V = 256 := by
    rw [←hAB,card_sup_eq_mul_of_normalizes_of_disjoint A B
      ((hBV.trans (V.le_centralizer.trans (centralizer_le hAV))).trans
        (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr hdis),hA,hB]
  have hcz : Nat.card (Z ⊔ B : Subgroup G) = 64 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint Z B
      ((hBV.trans (V.le_centralizer.trans (centralizer_le hZV))).trans
        (Subgroup.centralizer_le_normalizer _))
      (disjoint_iff.mpr (bot_unique ((inf_le_inf_right B hZA).trans_eq hdis))),hZ,hB]
  have hlarge : 64 ≤ Nat.card f.ker := by
    have hh := card_le_of_le hK
    rw [Nat.card_congr (subgroupOfEquivOfLe (sup_le hZV hBV)).toEquiv,hcz] at hh
    exact hh
  have hcount := f.ker.card_mul_index
  rw [index_ker,hcv] at hcount
  change Nat.card f.range ≤ 4
  nlinarith

/-- The full original module has core action of order at most four in either central A6 row. -/
theorem PreparedChosenModule.decomposable_five_raw_six_full_core_action_small
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
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
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z1 : Set G)
      let R := (pResidual 2 C).map C.subtype
      ∀ {L : Subgroup G}, R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) →
        L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
          ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) →
        IsQuasisimple (L ⧸ pCore 2 L) →
        ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 6) →
        ∃ hnV : V ≤ normalizer (L : Set G),
          Nat.card ((pCoreNormalizerAction 2 L).comp (inclusion hnV)).range ≤ 4 := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 C R L hnL hlocal hLq e
  have hZ : Z1 ≤ thompsonFixed T (localModule T M) := inf_le_right
  have hZne : Z1 ≠ ⊥ := by
    intro hz
    have hc := s.thompson_card s.first
    change Nat.card Z1 = 4 at hc
    rw [hz,Nat.card_unique] at hc
    omega
  have hnV := (h.raw_six_central_sylow_module_normalizes hG T hM.1.2 hZ hZne hlocal hLq e).2
  have hmoving := h.decomposable_five_raw_six_moving_support_core hG T hempty hM hmany hJ
    rfl c d hd s π hp hs hdec hq hfive hnL hLq e
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  have hWB := (s.full_residual_geometry hM.1.2 h.normalized c d π hp hs hJi).2.1
  rw [hWB] at hmoving
  exact ⟨hnV,core_action_small (plane_le _) (plane_le _)
    (show Z1 ≤ plane (localModule T M) (c.ambientFactor d s.first).space from inf_le_left)
    s.complement s.disjoint (s.support_card s.first) (s.support_card s.second)
    (s.thompson_card s.first) hnV (le_centralizer_iff.mp hlocal.1) hmoving⟩

end CFSG.Quasithin.Chapter15.Section01
