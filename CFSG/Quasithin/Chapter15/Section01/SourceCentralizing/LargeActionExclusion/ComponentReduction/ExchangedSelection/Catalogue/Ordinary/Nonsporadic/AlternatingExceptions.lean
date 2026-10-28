module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.SmallExceptions
public import Theory.GroupTheory.GeneralizedFitting.ComponentRankNormality
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.AlternatingSeven.DihedralLocals.Model
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Alternating.Seven

/-!
# The alternating ordinary exceptions

The three-rank of A₆ and A₇ makes the original component normal in G₁.
Its dihedral Sylow subgroup makes S nonabelian. Since S is normal in T,
its nontrivial derived subgroup meets Ω₁(Z(T)); the abelian outer group
makes this central involution act internally on L.

For A₆ the full centralizer of this inner involution in Aut(L) is a
two-group, so the literal O²(C_G(Z)) argument applies. For A₇ the earlier
1.1.5 marked fixed-group calculation forces three transpositions, an
outer automorphism, contradicting the constructed inner action. Triple
covers in the original markings are excluded by the proved two-group
center. No exchanged-plane noncentrality or later selection is used.

The earlier 15.1.14 residual premise in the A₆ argument remains with
qt-e-1514-global-thompson-residual and the final assembly owner
qt-e-15122-pre-exclusion-catalogue.
Source: Aschbacher--Smith 15.1.20(3), printed pp.1096--1097.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped commutatorElement
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
theorem PreExclusionSource.false_of_alternatingSix_equiv
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
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
  apply s.false_of_twoGroup_marked_centralizer (h := h) hG hu hmany hres hz α ha
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

private theorem seven_outer_commutative :
    IsMulCommutative (MulAut.Outer (alternatingGroup (Fin 7))) := by
  let A := alternatingGroup (Fin 7)
  let e : Equiv.Perm (Fin 7) ≃* MulAut A := MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  have hc : Nat.card (MulAut.innerSubgroup A) = 2520 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective
      (MulAut.conj_injective_of_center_eq_bot
        (alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 7))))).toEquiv]
    rw [nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  have ha : Nat.card (MulAut A) = 5040 := by
    rw [←Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hi := (MulAut.innerSubgroup A).index_mul_card
  rw [hc,ha] at hi
  have hcard : Nat.card (MulAut.Outer A) = 2 := by
    change (MulAut.innerSubgroup A).index = 2
    omega
  let := isCyclic_of_prime_card hcard
  infer_instance

private theorem marked_fixed_characteristic
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {z : G} (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (α : MulAut d.L) (ha : ∀ x : d.L, (α x : G) = z*x*z⁻¹) :
    HasCharacteristicTwo α.fixedSubgroup := by
  obtain ⟨P,_,h115⟩ := d.ordinary_involution_inputs hG hu h s.centralizer_sylow
  obtain ⟨_,β,Q,hβ,hm,_⟩ := (h115 z hz hzne).component_inputs
    (d.L.subgroupOf d.G1) hL
  let e := subgroupOfEquivOfLe (show d.L ≤ d.G1 from d.L_component.1)
  have he : MulAut.congr e β = α := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change ((β (e.symm x) : d.G1) : G) = (α x : G)
    rw [hβ,ha]
    rfl
  rw [←he]
  exact hm.characteristic_two.of_equiv (MulAut.fixedSubgroupCongr e β)

/-- The actual A₇ carrier contradicts the original marked involution action. -/
theorem PreExclusionSource.false_of_alternatingSeven_equiv
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* alternatingGroup (Fin 7)) : False := by
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
    have hh := (d.L.subgroupOf d.G1).le_normalizer_map d.G1.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le (show d.L ≤ d.G1 from d.L_component.1)] at hh
    exact d.S_le_G1.trans hh
  have ho : IsMulCommutative (MulAut.Outer d.L) := by
    let q := MulAut.outerCongr e
    exact ⟨⟨fun x y => q.injective (by
      simpa only [map_mul] using seven_outer_commutative.is_comm.comm (q x) (q y))⟩⟩
  have hSn : ¬IsMulCommutative d.S := by
    intro hs
    obtain ⟨P,hP⟩ := s.component_sylow
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    let q := (e.subgroupMap (P : Subgroup d.L)).trans
      (Q.equiv AlternatingSeven.DihedralLocals.fixedSylow)
    have hpS (x : P) : ((x : d.L) : G) ∈ d.S :=
      (hP ▸ mem_map_of_mem d.L.subtype x.property).1
    have hcomm : IsMulCommutative AlternatingSeven.DihedralLocals.fixedSylow := by
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
    let r : AlternatingSeven.DihedralLocals.fixedSylow :=
      ⟨⟨_,AlternatingSeven.DihedralLocals.twoGroup_le_alternating
        AlternatingSeven.DihedralLocals.r_mem_twoGroup⟩,
          AlternatingSeven.DihedralLocals.r_mem_twoGroup⟩
    let t : AlternatingSeven.DihedralLocals.fixedSylow :=
      ⟨⟨_,AlternatingSeven.DihedralLocals.twoGroup_le_alternating
        AlternatingSeven.DihedralLocals.s_mem_twoGroup⟩,
          AlternatingSeven.DihedralLocals.s_mem_twoGroup⟩
    have hh := congrArg (fun x : AlternatingSeven.DihedralLocals.fixedSylow =>
      ((x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) (hcomm.is_comm.comm r t)
    exact (by decide : AlternatingSeven.DihedralLocals.r * AlternatingSeven.DihedralLocals.s ≠
      AlternatingSeven.DihedralLocals.s * AlternatingSeven.DihedralLocals.r) hh
  obtain ⟨z,hz,hzne,α,ha,⟨t,ht⟩,hα⟩ := exists_inner_central_involution (h := h) s hL hSN ho hSn
  have hc := (Theory.Quasithin.centralizer_pCore_le_iff 2
    (MulAut.fixedSubgroupCongr e α)).mp
      (marked_fixed_characteristic (h := h) s hG hu hL hz hzne α ha)
  obtain ⟨σ,hσ,he⟩ := Chapter1.QuasisimpleInvolutions.Alternating.seven_fixed_action
    (MulAut.congr e α) (((MulAut.congr e).orderOf_eq α).trans hα) hc
  have hconj : MulAut.congr e α = MulAut.conjNormal (e t : Equiv.Perm (Fin 7)) := by
    rw [←ht]
    ext x
    simp
  have heq : (e t : Equiv.Perm (Fin 7)) = σ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide)
      (by decide)).injective (hconj.symm.trans he)
  have hev : Equiv.Perm.sign σ = 1 := heq ▸ (Equiv.Perm.mem_alternatingGroup.mp (e t).property)
  rw [Equiv.Perm.sign_of_cycleType,hσ] at hev
  norm_num at hev

/-- The actual alternating markings, including their possible triple covers,
are impossible at the original fixed component. -/
theorem PreExclusionSource.false_of_alternating_action
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {α : MulAut d.L} {n : ℕ} (hn : n = 6 ∨ n = 7) {σ : Equiv.Perm (Fin n)}
    (hm : Chapter15.Section03.Candidates.ComponentStructure.AlternatingAction α n σ) : False := by
  rcases hm with ⟨e,_⟩ | ⟨_,⟨e⟩,_⟩
  · rcases hn with rfl | rfl
    · exact s.false_of_alternatingSix_equiv (h := h) hG hu hmany hres hL e
    · exact s.false_of_alternatingSeven_equiv (h := h) hG hu hL e
  · have hc : Nat.card (center d.L) = 3 := by simpa using Nat.card_congr e.toEquiv
    rcases (s.ordinary hL).center_two.card_eq_or_dvd with h1 | h2
    · omega
    · norm_num [hc] at h2

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
