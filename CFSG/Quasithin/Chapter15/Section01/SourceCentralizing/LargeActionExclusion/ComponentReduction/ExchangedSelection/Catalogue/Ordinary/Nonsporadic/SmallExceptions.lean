module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary
public import Theory.SpecificGroups.PSL3Two.InvolutionResidual
public import Theory.GroupTheory.InnerAutomorphismCentralizerPGroup
public import Theory.GroupTheory.TwoLocalUniquenessControl.NormalSubgroups

/-!
# The small linear ordinary exception

The original residual Y = O²(C_G(Z)) normalizes the selected component:
15.1.14 places Y in G₁, and the two-element component orbit is fixed by
its two-perfect action. A two-group centralizer of the marked automorphism
therefore makes Y centralize L. The characteristic-two uniqueness subgroup
C_G(Z) controls N_G(Y), contradicting L outside M_Z.

For the actual PSL₃(2) carrier, every marked 1.1.5 action is inner.
Its involution centralizers and outer automorphism group are two-groups,
so the argument applies. The original component, central involution and
embedded residual are retained throughout. The earlier 15.1.14 premise
is discharged by qt-e-1514-global-thompson-residual and the final owner
qt-e-15122-pre-exclusion-catalogue.

Source: Aschbacher--Smith, 15.1.20(3), printed pp.1096--1097.
-/

public section
open Subgroup Theory.GroupTheory
open Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The literal O²(C_G(Z)) has its full ambient normalizer inside M_c. -/
theorem centralResidual_normalizer_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    normalizer ((pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype : Set G) ≤ Mc := by
  let C := centralizer (centralInvolutions T : Set G)
  let Y := (pResidual 2 C).map C.subtype
  have hMc : Mc ∈ maximalTwoLocalOvergroups C := hu ▸ Set.mem_singleton Mc
  have hTC : (T : Subgroup G) ≤ C := by
    intro t ht z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  let : IsElementaryAbelian 2 (centralInvolutions T) := omegaOneCenterAmbient_elementaryAbelian _
  have hCT : HasCharacteristicTwo C := by
    have hh := CaseIMarkedSubgroup.partner_centralizer_characteristic_two hG hu
      (IsElementaryAbelian.isPGroup 2 (centralInvolutions T))
      (fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
    rw [inf_eq_left.mpr hMc.2] at hh
    exact Chapter1.mem_He_iff.mp hh
  have hYne : Y ≠ ⊥ := by
    intro he
    have hr : pResidual 2 C = ⊥ :=
      ((pResidual 2 C).map_eq_bot_iff_of_injective C.subtype_injective).mp he
    have hCp : IsPGroup 2 C := (isPGroup_quotient_pResidual 2).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hr).trans QuotientGroup.quotientBot)
    have hCTeq : C = (T : Subgroup G) := T.is_maximal' hCp hTC
    change maximalTwoLocalOvergroups C = {Mc} at hu
    rw [hCTeq] at hu
    simp only [hu,Set.ncard_singleton,lt_self_iff_false] at hmany
  exact normalizer_le_of_characteristic_two_unique hCT
    (fun N hN hCN => Set.mem_singleton_iff.mp
      (hu ▸ (show N ∈ maximalTwoLocalOvergroups C from ⟨hN,hCN⟩)))
    (map_subtype_le _) hYne
    (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C)))

private theorem centralResidual_normalizes
    (_s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤ normalizer (d.L : Set G) := by
  let Y := (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
    (centralizer (centralInvolutions T : Set G)).subtype
  have hYG : Y ≤ d.G1 := hres.trans (centralizer_le d.Z1_le_fixed)
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

/-- A two-group automorphism centralizer kills the original centralizer residual,
contradicting its normalizer bound and the original component escape. -/
theorem PreExclusionSource.false_of_twoGroup_marked_centralizer
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {z : G} (hz : z ∈ centralInvolutions T)
    (α : MulAut d.L) (ha : ∀ x : d.L, (α x : G) = z*x*z⁻¹)
    (hp : IsPGroup 2 (centralizer ({α} : Set (MulAut d.L)))) : False := by
  let C := centralizer (centralInvolutions T : Set G)
  let Y := (pResidual 2 C).map C.subtype
  let N := normalizer (d.L : Set G)
  let f := d.L.normalizerMonoidHom
  have hYN : Y ≤ N := centralResidual_normalizes (h := h) s hG hres
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
    have hyz : z*(y : G) = (y : G)*z := (map_subtype_le _ y.property) z hz
    calc
      (y : G)*(z*(l : G)*z⁻¹)*(y : G)⁻¹ =
          ((y : G)*z)*(l : G)*((y : G)*z)⁻¹ := by group
      _ = (z*(y : G))*(l : G)*(z*(y : G))⁻¹ := by rw [hyz]
      _ = _ := by group
  let b := a.codRestrict (centralizer ({α} : Set (MulAut d.L))) hac
  have hb := (isPPerfect_embedded_pResidual 2 C).hom_eq_one_of_isPGroup hp b
  have hc : Y ≤ centralizer (d.L : Set G) := by
    intro y hy l hl
    have hy1 : a ⟨y,hy⟩ = 1 := congrArg (fun c : Y →* centralizer ({α} : Set (MulAut d.L)) =>
      (c ⟨y,hy⟩ : MulAut d.L)) hb
    have he := congrArg Subtype.val (DFunLike.congr_fun hy1 (⟨l,hl⟩ : d.L))
    change y*l*y⁻¹=l at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  apply d.L_not_le_MZ
  exact le_inf d.L_component.1 (((le_centralizer_iff.mp hc).trans
    (Subgroup.centralizer_le_normalizer _)).trans (centralResidual_normalizer_le hG hu hmany))

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
theorem PreExclusionSource.false_of_pslThreeTwo_equiv
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
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
  apply PreExclusionSource.false_of_twoGroup_marked_centralizer (h := h) s hG hu hmany hres hz α ha
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
