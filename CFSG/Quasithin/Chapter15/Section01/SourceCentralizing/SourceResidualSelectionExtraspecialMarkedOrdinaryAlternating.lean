module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialMarkedOrdinaryResidual
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineAlternating

/-!
# Alternating exclusions with seed control only on the marked residual

Retain the original selected component and its marked involution. The
ordinary A₆ argument needs seed centralization only by O²(M_Z), while the
A₇ and triple-cover arguments already require no such additional control.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem exists_inner_central_involution
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hn : d.S ≤ normalizer (d.L : Set G))
    (ho : IsMulCommutative (MulAut.Outer d.L))
    (hS : ¬IsMulCommutative d.S) :
    ∃ z ∈ centralInvolutions T, z ≠ 1 ∧
      ∃ α : MulAut d.L, (∀ x : d.L, (α x : G) = z*x*z⁻¹) ∧
        α ∈ (MulAut.conj (G := d.L)).range ∧ orderOf α = 2 := by
  let D := (commutator d.S).map d.S.subtype
  have hDT : D ≤ (T : Subgroup G) := (map_subtype_le _).trans d.S_le_T
  have hDn : (T : Subgroup G) ≤ normalizer (D : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer d.S_le_T).mp s.sylow_normal).trans
      (normalizer_le_normalizer_characteristic_image d.S (commutator d.S))
  let : (D.subgroupOf (T : Subgroup G)).Normal := normal_subgroupOf_of_le_normalizer hDn
  have hDne : D.subgroupOf (T : Subgroup G) ≠ ⊥ := by
    intro he
    have heD : D = ⊥ := by
      have hh := congrArg (map (T : Subgroup G).subtype) he
      rwa [map_subgroupOf_eq_of_le hDT,Subgroup.map_bot] at hh
    have hd : commutator d.S = ⊥ :=
      ((commutator d.S).map_eq_bot_iff_of_injective d.S.subtype_injective).mp heD
    exact hS ((_root_.commutator_eq_bot_iff d.S).mp hd)
  let : Fact (IsPGroup 2 (T : Subgroup G)) := ⟨T.isPGroup'⟩
  obtain ⟨Z,_,hZD,hZcard,hZcen⟩ := exists_central_subgroup_card_eq_prime_in_normal
    (p := 2) (D.subgroupOf (T : Subgroup G))
    ((nontrivial_iff_ne_bot _).mpr hDne)
  obtain ⟨x,hx2⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hZcard])
  let z : G := x.val.val
  have hz2 : orderOf z = 2 := by
    exact ((Subgroup.orderOf_coe (x : (T : Subgroup G))).trans
      (Subgroup.orderOf_coe x)).trans hx2
  have hz : z ∈ centralInvolutions T := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨x.val.property,?_,?_⟩
    · rw [←hz2]; exact pow_orderOf_eq_one z
    · intro t ht
      exact congrArg Subtype.val (mem_center_iff.mp (hZcen x.property) ⟨t,ht⟩)
  have hzD : z ∈ D := hZD x.property
  obtain ⟨y,hy,hye⟩ := hzD
  let a : d.S →* MulAut d.L := d.L.normalizerMonoidHom.comp (inclusion hn)
  let f : d.S →* MulAut.Outer d.L := (QuotientGroup.mk' (MulAut.innerSubgroup d.L)).comp a
  have hker : commutator d.S ≤ f.ker := by
    rw [commutator_eq_closure,closure_le]
    rintro _ ⟨u,v,rfl⟩
    change f ⁅u,v⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (ho.is_comm.comm _ _)
  have hi : a y ∈ MulAut.innerSubgroup d.L := (QuotientGroup.eq_one_iff _).mp (hker hy)
  have ha (l : d.L) : (a y l : G) = z*l*z⁻¹ := by
    change (y : G)*l*(y : G)⁻¹ = z*l*z⁻¹
    change (y : G) = z at hye
    rw [hye]
  have hzne : z ≠ 1 := by intro he; simp [he] at hz2
  have ha2 : a y ^ 2 = 1 := by
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    change (a y (a y l) : G) = l
    rw [ha,ha]
    have hzz : z*z=1 := by simpa only [pow_two,hz2] using pow_orderOf_eq_one z
    calc
      z*(z*(l : G)*z⁻¹)*z⁻¹ = (z*z)*(l : G)*(z*z)⁻¹ := by group
      _ = _ := by rw [hzz]; simp
  have hane : a y ≠ 1 := by
    intro he
    apply hzne
    apply mem_bot.mp
    rw [←(s.ordinary hL).central_faithful]
    refine ⟨hz,?_⟩
    intro l hl
    have hh := ha ⟨l,hl⟩
    rw [he] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  exact ⟨z,hz,hzne,a y,ha,hi,orderOf_eq_prime ha2 hane⟩

/-- The actual A₆ carrier cannot be the original ordinary component. -/
theorem PreExclusionSource.false_of_alternatingSix_equiv_of_residual_seed
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hYseed : (pResidual 2 d.MZ).map d.MZ.subtype ≤
      centralizer (centralInvolutions T : Set G))
    (hNY : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* alternatingGroup (Fin 6)) : False := by
  let eK := (subgroupOfEquivOfLe (show d.L ≤ d.G1 from d.L_component.1)).trans e
  have hzK : center (d.L.subgroupOf d.G1) = ⊥ := by
    apply (center (d.L.subgroupOf d.G1)).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr eK).toEquiv,
      alternatingGroup.center_eq_bot (by simp),card_bot]
  let := h.elementary
  have hQ : IsSQTK KnownSimple.IsKnownSimple d.G1 := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    (IsElementaryAbelian.isPGroup 2 V |>.to_le (d.Z1_le_fixed.trans inf_le_left))
  have hr : 2 ≤ primeRank 3 (d.L.subgroupOf d.G1) := by
    rw [primeRank_congr 3 eK]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  let : (d.L.subgroupOf d.G1).Normal := hL.normal_of_centerless_primeRank hzK hr
    (hQ.stronglyQuasithin 3 (by decide) (by decide))
  have hSN : d.S ≤ normalizer (d.L : Set G) := by
    have hh : d.G1 ≤ normalizer ((d.L.subgroupOf d.G1).map d.G1.subtype : Set G) :=
      (by
        have hh := (d.L.subgroupOf d.G1).le_normalizer_map d.G1.subtype
        rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
        exact hh)
    rw [map_subgroupOf_eq_of_le (show d.L ≤ d.G1 from d.L_component.1)] at hh
    exact d.S_le_G1.trans hh
  have ho : IsMulCommutative (MulAut.Outer d.L) := by
    let q := MulAut.outerCongr e
    exact ⟨⟨fun x y => q.injective (by
      simpa only [map_mul] using AlternatingSix.ShadowLocal.outer_isMulCommutative.is_comm.comm
        (q x) (q y))⟩⟩
  have hSn : ¬IsMulCommutative d.S := by
    intro hs
    obtain ⟨P,hP⟩ := s.component_sylow
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    obtain ⟨f⟩ := AlternatingSix.ShadowLocal.alternatingSylow_dihedral Q
    let q : P ≃* DihedralGroup 4 := (e.subgroupMap (P : Subgroup d.L)).trans f
    have hpS (x : P) : ((x : d.L) : G) ∈ d.S :=
      (hP ▸ mem_map_of_mem d.L.subtype x.property).1
    apply DihedralGroup.not_commutative (by decide : 4 ≠ 1) (by decide : 4 ≠ 2)
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨a,rfl⟩ := q.surjective x
    obtain ⟨b,rfl⟩ := q.surjective y
    rw [←map_mul,←map_mul]
    apply congrArg q
    apply Subtype.ext
    apply Subtype.ext
    change ((a : d.L) : G) * ((b : d.L) : G) = ((b : d.L) : G) * ((a : d.L) : G)
    exact congrArg (fun x : d.S => (x : G)) (hs.is_comm.comm
      (⟨a,hpS a⟩ : d.S) (⟨b,hpS b⟩ : d.S))
  obtain ⟨z,hz,_,α,ha,⟨t,ht⟩,hα⟩ := exists_inner_central_involution (h := h) s hL hSN ho hSn
  apply d.false_of_twoGroup_marked_centralizer_of_residual_seed h hG hYseed hNY hz α ha
  let q := MulAut.congr e
  have hconj : q α = MulAut.conj (e t) := by rw [←ht]; ext x; simp [q]
  have ht2 : orderOf (e t) = 2 := by
    have hzL : center d.L = ⊥ := by
      apply (center d.L).eq_bot_iff_card.mpr
      rw [Nat.card_congr (centerCongr e).toEquiv,
        alternatingGroup.center_eq_bot (by simp),card_bot]
    rw [e.orderOf_eq,←orderOf_injective _ (MulAut.conj_injective_of_center_eq_bot hzL) t,ht]
    exact hα
  let f : centralizer ({α} : Set (MulAut d.L)) →*
      centralizer ({MulAut.conj (e t)} : Set (MulAut (alternatingGroup (Fin 6)))) :=
    (q.toMonoidHom.comp (centralizer ({α} : Set (MulAut d.L))).subtype).codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      rw [←hconj]
      exact (map_mul q _ _).symm.trans
        ((congrArg q (mem_centralizer_singleton_iff.mp x.property)).trans (map_mul q _ _)))
  exact (IsPGroup.of_card (p := 2) (n := 5)
    (AlternatingSix.ShadowLocal.inner_involution_centralizer_card (e t) ht2)).of_injective f
    (fun a b hh => Subtype.ext (q.injective (congrArg Subtype.val hh)))

/-- The actual alternating markings, including their possible triple covers,
are impossible at the original fixed component. -/
theorem PreExclusionSource.false_of_alternating_action_of_residual_seed
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hYseed : (pResidual 2 d.MZ).map d.MZ.subtype ≤
      centralizer (centralInvolutions T : Set G))
    (hNY : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {α : MulAut d.L} {n : ℕ} (hn : n = 6 ∨ n = 7) {σ : Equiv.Perm (Fin n)}
    (hm : Chapter15.Section03.Candidates.ComponentStructure.AlternatingAction α n σ) : False := by
  rcases hm with ⟨e,_⟩ | ⟨_,⟨e⟩,_⟩
  · rcases hn with rfl | rfl
    · exact s.false_of_alternatingSix_equiv_of_residual_seed (h := h) hG hYseed hNY hL e
    · exact s.false_of_alternatingSeven_equiv (h := h) hG hu hL e
  · have hc : Nat.card (center d.L) = 3 := by simpa using Nat.card_congr e.toEquiv
    rcases (s.ordinary hL).center_two.card_eq_or_dvd with h1 | h2
    · omega
    · norm_num [hc] at h2

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
