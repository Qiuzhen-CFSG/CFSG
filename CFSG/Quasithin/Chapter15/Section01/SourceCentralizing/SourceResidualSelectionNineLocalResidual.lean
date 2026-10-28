module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineMarkedControl
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNinePartner
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.SmallExceptions

/-!
# Nine component exclusions using the actual marked residual

The residual of M_Z lies in the original marked centralizer G1 without
any global fixed-subgroup conclusion. Its two-perfect action normalizes
the selected component. When the partner centralizes the original central
seed and the full normalizer of this residual lies in the partner, a
two-group marked automorphism centralizer contradicts component escape.

The full Nine row supplies both partner and normalizer bounds. Applied
to the actual PSL3(2) model, this proves its exclusion without the global
15.1.14 residual premise. No component model classification is asserted.

Source: Aschbacher--Smith 15.1.18--20, printed pp.1092--1097.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The actual marked residual normalizes the selected component by its
two-perfect action on the component orbit. -/
theorem markedResidual_normalizes_component
    (d : CaseIComponentData T M Mc V) (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) :
    (pResidual 2 d.MZ).map d.MZ.subtype ≤ normalizer (d.L : Set G) := by
  let Y := (pResidual 2 d.MZ).map d.MZ.subtype
  have hYG : Y ≤ d.G1 := (map_subtype_le _).trans inf_le_left
  let := h.elementary
  have hQ : IsSQTK KnownSimple.IsKnownSimple d.G1 := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    (IsElementaryAbelian.isPGroup 2 V |>.to_le (d.Z1_le_fixed.trans inf_le_left))
  have hquot : IsSQTK KnownSimple.IsKnownSimple (d.G1 ⧸ pCore 2 d.G1) := by
    refine ⟨?_,hQ.isKGroup.quotient (pCore 2 d.G1)⟩
    intro q hq ho
    let : Fact q.Prime := ⟨hq⟩
    exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 d.G1) pCore_isPGroup).trans
      (hQ.stronglyQuasithin q hq ho)
  let e := (subgroupOfEquivOfLe hYG).symm
  have hp : IsPPerfect 2 (Y.subgroupOf d.G1) :=
    (isPPerfect_embedded_pResidual 2 _).of_surjective e.toMonoidHom e.surjective
  have hn := Chapter1.Section02.twoPerfect_normalizes_cComponent_source hquot d.L_component.2 hp
  have hh := (map_mono (f := d.G1.subtype) hn).trans
    ((d.L.subgroupOf d.G1).le_normalizer_map d.G1.subtype)
  rwa [map_subgroupOf_eq_of_le hYG,map_subgroupOf_eq_of_le (show d.L ≤ d.G1 from d.L_component.1)] at hh

/-- A two-group marked automorphism centralizer is incompatible with the
local residual's normalizer bound and the actual component escape. -/
theorem false_of_twoGroup_marked_centralizer_local
    (d : CaseIComponentData T M Mc V) (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hMcC : Mc ≤ centralizer (centralInvolutions T : Set G))
    (hNY : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    {z : G} (hz : z ∈ centralInvolutions T)
    (α : MulAut d.L) (ha : ∀ x : d.L, (α x : G) = z*x*z⁻¹)
    (hp : IsPGroup 2 (centralizer ({α} : Set (MulAut d.L)))) : False := by
  let Y := (pResidual 2 d.MZ).map d.MZ.subtype
  let N := normalizer (d.L : Set G)
  let f := d.L.normalizerMonoidHom
  have hYN : Y ≤ N := d.markedResidual_normalizes_component h hG
  let a : Y →* MulAut d.L := f.comp (inclusion hYN)
  have hac : ∀ y : Y, a y ∈ centralizer ({α} : Set (MulAut d.L)) := by
    intro y
    apply mem_centralizer_singleton_iff.mpr
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    change (y : G)*(α l : G)*(y : G)⁻¹ = (α (f (inclusion hYN y) l) : G)
    rw [ha,ha]
    change (y : G)*(z*(l : G)*z⁻¹)*(y : G)⁻¹ = z*((y : G)*(l : G)*(y : G)⁻¹)*z⁻¹
    have hyMZ : (y : G) ∈ d.MZ := map_subtype_le _ y.property
    have hyz : z*(y : G) = (y : G)*z := hMcC hyMZ.2 z hz
    calc
      (y : G)*(z*(l : G)*z⁻¹)*(y : G)⁻¹ =
          ((y : G)*z)*(l : G)*((y : G)*z)⁻¹ := by group
      _ = (z*(y : G))*(l : G)*(z*(y : G))⁻¹ := by rw [hyz]
      _ = _ := by group
  let b := a.codRestrict (centralizer ({α} : Set (MulAut d.L))) hac
  have hb := (isPPerfect_embedded_pResidual 2 d.MZ).hom_eq_one_of_isPGroup hp b
  have hc : Y ≤ centralizer (d.L : Set G) := by
    intro y hy l hl
    have hy1 : a ⟨y,hy⟩ = 1 := congrArg (fun c : Y →* centralizer ({α} : Set (MulAut d.L)) =>
      (c ⟨y,hy⟩ : MulAut d.L)) hb
    have he := congrArg Subtype.val (DFunLike.congr_fun hy1 (⟨l,hl⟩ : d.L))
    change y*l*y⁻¹=l at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  apply d.L_not_le_MZ
  exact le_inf d.L_component.1 (((le_centralizer_iff.mp hc).trans
    (Subgroup.centralizer_le_normalizer _)).trans hNY)

private theorem pslThreeTwo_inner
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Matrix.PSL3Two.PSL)
    {α : MulAut d.L} (hm : ModelAction115 d.L α) :
    α ∈ (MulAut.conj (G := d.L)).range := by
  have hcard : Nat.card d.L = 168 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hnot (n : ℕ) (hn : n = 6 ∨ n = 7) (σ : Equiv.Perm (Fin n)) :
      ¬ AlternatingAction α n σ := by
    rintro (⟨f,_⟩ | ⟨_,⟨f⟩,_⟩)
    · have hh := Nat.card_congr f.toEquiv
      rcases hn with rfl | rfl <;>
        rw [hcard,nat_card_alternatingGroup,Nat.card_fin] at hh <;> norm_num at hh
    · have hh : Nat.card (center d.L) = 3 := by simpa using Nat.card_congr f.toEquiv
      rcases (s.ordinary hL).center_two.card_eq_or_dvd with h1 | h2
      · omega
      · norm_num [hh] at h2
  cases hm with
  | lie _ _ hi => exact hi
  | two_cover _ _ _ hi => exact hi
  | six σ _ ha => exact (hnot 6 (Or.inl rfl) σ ha).elim
  | seven σ _ ha => exact (hnot 7 (Or.inr rfl) σ ha).elim
  | odd _ hi => exact hi
  | sporadic _ _ _ ha => exact ha.1

/-- The actual PSL₃(2) model is impossible before exchanged selection. -/
theorem PreExclusionSource.nine_false_of_pslThreeTwo_equiv
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hne : M ≠ Mc) (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (ChapterD.UniqueFactor.imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map
          (ChapterD.UniqueFactor.actionHom M V h.normalized).rangeRestrict))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Matrix.PSL3Two.PSL) : False := by
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨α,ha,hm⟩ := s.ordinary_marked_model (h := h) hL hz hzne
  have hi := pslThreeTwo_inner (h := h) s hL e hm
  have hzL : center d.L = ⊥ := by
    apply (center d.L).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr (e.trans Matrix.PSL3Two.equiv.symm)).toEquiv,
      Matrix.PSL3Two.center_eq_bot,card_bot]
  obtain ⟨t,ht⟩ := hi
  have hα2 : α ^ 2 = 1 := by
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    change (α (α l) : G) = (l : G)
    rw [ha,ha]
    have hz2 := (mem_omegaOneCenterAmbient_iff _ _).mp hz |>.2.1
    have hzz : z*z=1 := by simpa only [pow_two] using hz2
    calc
      z*(z*(l : G)*z⁻¹)*z⁻¹ = (z*z)*(l : G)*(z*z)⁻¹ := by group
      _ = _ := by rw [hzz]; simp
  have hαne : α ≠ 1 := by
    intro he
    apply hzne
    apply mem_bot.mp
    rw [←(s.ordinary hL).central_faithful]
    refine ⟨hz,?_⟩
    intro l hl
    have hh := ha ⟨l,hl⟩
    rw [he] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have ht2 : orderOf t = 2 := by
    rw [←orderOf_injective _ (MulAut.conj_injective_of_center_eq_bot hzL) t,ht]
    exact orderOf_eq_prime hα2 hαne
  have hpair := h.nine_maximal_overgroups hG T hempty hM hJ hu h9
  have hNY := h.marked_residual_normalizer_control_of_pair hG T hempty hM hmany hJ hu
    hpair d.Z1_le_fixed d.Z1_ne_bot s.sylow_normalizes_MZ s.centralizer_sylow
  have hMcC := (h.nine_partner_centralizer hG T hempty hM hJ hu hne hfull h9).1.le
  apply d.false_of_twoGroup_marked_centralizer_local h hG hMcC hNY hz α ha
  rw [←ht]
  apply MulAut.isPGroup_centralizer_conj_of_outer hzL
    (Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv
      (MulAut.outerCongr (e.trans Matrix.PSL3Two.equiv.symm)).symm)
  let f : centralizer ({t} : Set d.L) →* centralizer ({e t} : Set Matrix.PSL3Two.PSL) :=
    (e.toMonoidHom.comp (centralizer ({t} : Set d.L)).subtype).codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      exact (map_mul e _ _).symm.trans
        ((congrArg e (mem_centralizer_singleton_iff.mp x.property)).trans (map_mul e _ _)))
  exact (Matrix.PSL3Two.InvolutionResidual.centralizer_two (e t)
    ((e.orderOf_eq t).trans ht2)).of_injective f
      (fun a b hh => Subtype.ext (e.injective (congrArg Subtype.val hh)))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
