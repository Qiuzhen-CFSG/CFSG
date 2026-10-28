module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.NaturalKernel
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# The index of the component in the plane centralizer

The natural Sylow image and the outer cubic force the actual outer index
to be twelve, and also give full marked projective action. On the central
four-group, two-perfectness and the Sylow fixed line force image order six.
The index tower therefore supplies the literal index-two premise of
the field-centralizer contradiction.
Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel
variable {G : Type*} [Group G] [Finite G]

/-- The actual marked outer action has order twelve. -/
theorem LocalResult.component_relIndex {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) : L.relIndex I = 12 := by
  let : Group.IsPerfect L := h.perfect
  have hSI : d.S ≤ I := le_sup_right.trans h.outside.1.2
  have hIL := h.normalizes_component s.earlier
  let K := L.subgroupOf I
  let : K.Normal := normal_subgroupOf_of_le_normalizer hIL
  let f : I →* MulAut.Outer PSL(3,r.marking.F) :=
    (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,r.marking.F))).comp
      ((markedAction r.marking).comp (inclusion hIL))
  have hk : f.ker = K := by
    ext x
    exact (QuotientGroup.eq_one_iff _).trans
      (markedAction_inner_iff_mem r.marking r.cover.center_core.ge h.component_le hIL
        (r.cover.overgroup_centralizer ▸ r.cover.center_plane ▸ centerImage_le L)
        x.property)
  have hd : K.index ∣ 12 := by
    rw [← hk, index_ker]
    exact f.range.card_subgroup_dvd_card.trans
      (Matrix.PSL3Four.OuterThreeStructure.outer_card_dvd_twelve_of_card_four r.marking.card)
  have hs : L.relIndex d.S = 4 := by
    let g := d.action.actor.comp (inclusion
      (show d.S ≤ d.M from inf_le_left.trans d.sylow_le))
    have hg : g.ker = L.subgroupOf d.S := by
      have he := (natural_kernel_T s h r).trans r.cover.residual_core
      ext x
      change d.action.actor _ = 1 ↔ (x : G) ∈ L
      change _ ∈ d.action.actor.ker ↔ _
      rw [d.action.ker_actor]
      exact ⟨fun hx => (he.le ⟨x.property.1, hx⟩).2,
        fun hx => (he.ge ⟨x.property, hx⟩).2⟩
    change (L.subgroupOf d.S).index = 4
    rw [← hg, index_ker, RankTwo.natural_restricted_actor_range]
    exact d.action.card_image_planeStabilizer d.T d.sylow_le 1
  have hfour : 4 ∣ K.index := by
    rw [← hs, ← relIndex_subgroupOf hSI]
    exact K.relIndex_dvd_index_of_normal (d.S.subgroupOf I)
  let z : I := ⟨r.actor, (show d.Yplus ≤ I from le_sup_left.trans h.outside.1.2) r.actor.property⟩
  have hz3 : z ^ 3 = 1 := Subtype.ext (orderOf_eq_prime_iff.mp r.diagonal.1).1
  have hzout : f z ≠ 1 := by
    intro he
    obtain ⟨_, a, ha, hr⟩ := r.diagonal
    apply ha
    rw [← markedAction_eq_of_realizes r.marking ⟨z, hIL z.property⟩ hr]
    exact (QuotientGroup.eq_one_iff _).mp he
  have hz : orderOf (f.rangeRestrict z) = 3 := orderOf_eq_prime
    (by apply Subtype.ext; change f z ^ 3 = 1; rw [← map_pow, hz3, map_one])
    (fun he => hzout (congrArg Subtype.val he))
  have hthree : 3 ∣ K.index := by
    rw [← hk, index_ker]
    simpa only [hz] using orderOf_dvd_natCard (f.rangeRestrict z)
  have htwelve : 12 ∣ K.index :=
    (by decide : Nat.Coprime 3 4).mul_dvd_of_dvd_of_dvd hthree hfour
  exact Nat.dvd_antisymm hd htwelve

/-- Full projective action follows from the actual index and inner inclusion. -/
theorem LocalResult.marked_action_surjective {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) :
    Function.Surjective ((markedAction r.marking).comp
      (inclusion (h.normalizes_component s.earlier))) := by
  let : Group.IsPerfect L := h.perfect
  let a := (markedAction r.marking).comp (inclusion (h.normalizes_component s.earlier))
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,r.marking.F))
  let f := q.comp a
  have hk : f.ker = L.subgroupOf I := by
    ext x
    exact (QuotientGroup.eq_one_iff _).trans
      (markedAction_inner_iff_mem r.marking r.cover.center_core.ge h.component_le
        (h.normalizes_component s.earlier)
        (r.cover.overgroup_centralizer ▸ r.cover.center_plane ▸ centerImage_le L)
        x.property)
  have hc : Nat.card f.range = 12 := by
    rw [← index_ker, hk]
    exact r.component_relIndex s h
  have hf : f.range = ⊤ := eq_of_le_of_card_ge le_top (by
    rw [card_top, hc]
    exact Nat.le_of_dvd (by decide)
      (Matrix.PSL3Four.OuterThreeStructure.outer_card_dvd_twelve_of_card_four r.marking.card))
  have hin : MulAut.innerSubgroup PSL(3,r.marking.F) ≤ a.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, rfl⟩ := SourceBorel.projectiveMap_surjective r.marking x
    exact ⟨inclusion h.component_le l, markedAction_on_component r.marking l⟩
  apply a.range_eq_top.mp
  have hm : a.range.map q = ⊤ := by
    rw [← MonoidHom.range_comp]
    exact hf
  have hh := congrArg (Subgroup.comap q) hm
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk', sup_of_le_left hin,
    comap_top] using hh

/-- The actual center plane has the full order-six action. -/
theorem LocalResult.center_centralizer_relIndex {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) :
    (centralizer (r.cover.borel.W₁ : Set G)).relIndex I = 6 := by
  let V := r.cover.borel.W₁
  obtain ⟨i, hi⟩ := r.plane
  have hV : V = d.action.plane i := hi
  let : IsElementaryAbelian 2 V := d.action.elementary_of_le (hV ▸ d.action.plane_le i)
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hV, d.action.card_plane]; decide)
  let : IsKleinFour V := ⟨hV ▸ d.action.card_plane i, IsElementaryAbelian.exponent_eq_prime⟩
  have hIV : I ≤ normalizer (V : Set G) := by
    dsimp only [V]
    rw [← r.cover.center_plane]
    exact (h.normalizes_component s.earlier).trans
      (normalizer_le_normalizer_characteristic_image L (center L))
  let ρ := V.normalizerMonoidHom.comp (inclusion hIV)
  have hρ (x : I) : ρ x = 1 ↔ (x : G) ∈ centralizer (V : Set G) := by
    constructor
    · intro he v hv
      have hh := congrArg (fun a : MulAut V => (a ⟨v, hv⟩ : G)) he
      change (x : G) * v * (x : G)⁻¹ = v at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hx
      ext v
      change (x : G) * (v : G) * (x : G)⁻¹ = (v : G)
      rw [← hx (v : G) v.property, mul_inv_cancel_right]
  have hk : ρ.ker = (centralizer (V : Set G)).subgroupOf I := by
    ext x
    exact hρ x
  have hSI : d.S ≤ I := le_sup_right.trans h.outside.1.2
  have hYI : d.Yplus ≤ I := le_sup_left.trans h.outside.1.2
  have hntwo : ¬ IsPGroup 2 ρ.range := by
    intro hp
    have hY : IsPPerfect 2 d.Yplus := r.cover.plus.symm ▸ residualY_isPPerfect d.M d.Mc
    have he := hY.hom_eq_one_of_isPGroup hp (ρ.rangeRestrict.comp (inclusion hYI))
    apply r.noncentral s
    intro y hy
    apply (hρ ⟨y, hYI hy⟩).mp
    exact congrArg (fun f : d.Yplus →* ρ.range => (f ⟨y, hy⟩ : MulAut V)) he
  have hnthree : ¬ IsPGroup 3 ρ.range := by
    intro hp
    let f := ρ.comp (inclusion hSI)
    have hp2 : IsPGroup 2 f.range :=
      (d.T.isPGroup'.to_le (show d.S ≤ d.T from inf_le_left)).of_surjective
        f.rangeRestrict f.rangeRestrict_surjective
    have hp3 : IsPGroup 3 f.range := hp.to_le (by
      rintro _ ⟨x, rfl⟩
      exact ⟨inclusion hSI x, rfl⟩)
    have hf : f.range = ⊥ := disjoint_self.mp
      (IsPGroup.disjoint_of_ne 2 3 (by decide) f.range f.range hp2 hp3)
    have hSfix : d.S ≤ centralizer (V : Set G) := by
      intro t ht
      apply (hρ ⟨t, hSI ht⟩).mp
      exact mem_bot.mp (hf ▸ (show f ⟨t, ht⟩ ∈ f.range from ⟨⟨t, ht⟩, rfl⟩))
    have hS : d.S = planeStabilizer d.T (d.action.plane i) :=
      le_antisymm
        (le_inf inf_le_left (RankTwo.planeStabilizer_normalizes_planes
          d.action d.T d.sylow_le 1 i))
        (le_inf inf_le_left (RankTwo.planeStabilizer_normalizes_planes
          d.action d.T d.sylow_le i 1))
    have hc : Nat.card (fixedPlane V d.S) = 2 := by
      rw [hV, hS]
      exact d.action.card_plane_fixed_planeStabilizer d.T d.sylow_le i
    have he : fixedPlane V d.S = V := inf_eq_left.mpr (le_centralizer_iff.mp hSfix)
    rw [he, hV, d.action.card_plane] at hc
    omega
  have hd : Nat.card ρ.range ∣ 6 := by
    rw [← IsKleinFour.card_mulAut V]
    exact ρ.range.card_subgroup_dvd_card
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hd
  have hcases : Nat.card ρ.range ∣ 2 ∨ Nat.card ρ.range ∣ 3 ∨ Nat.card ρ.range = 6 := by
    interval_cases hc : Nat.card ρ.range <;> norm_num at *
  have hc : Nat.card ρ.range = 6 := by
    rcases hcases with htwo | hthree | hfull
    · exact (hntwo (IsPGroup.of_card_dvd_pow (n := 1) (by simpa using htwo))).elim
    · exact (hnthree (IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hthree))).elim
    · exact hfull
  change ((centralizer (V : Set G)).subgroupOf I).index = 6
  rw [← hk, index_ker, hc]

/-- The final field-centralizer argument's literal index-two input. -/
theorem LocalResult.component_index_center_centralizer
    {d : CharacteristicTwo.LocalData G} (s : SourceInputs d)
    {I L : Subgroup G} (h : Setup d I L) (r : LocalResult d I L)
    (hI : I = normalizer (r.cover.borel.W₁ : Set G)) :
    L.relIndex (centralizer (r.cover.borel.W₁ : Set G)) = 2 := by
  have hLC : L ≤ centralizer (r.cover.borel.W₁ : Set G) := by
    rw [← r.cover.center_plane]
    exact le_centralizer_iff.mp (centerImage_centralizes L)
  have hCI : centralizer (r.cover.borel.W₁ : Set G) ≤ I :=
    (Subgroup.centralizer_le_normalizer _).trans hI.ge
  have he := L.relIndex_mul_relIndex _ I hLC hCI
  rw [r.component_relIndex s h, r.center_centralizer_relIndex s h] at he
  omega


end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
