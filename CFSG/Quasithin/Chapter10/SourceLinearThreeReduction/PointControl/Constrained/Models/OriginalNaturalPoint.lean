module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalNaturalActions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalSelection

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Remaining

/-!
# Reselecting the original local natural point

The original local natural module gives a saturated opposite point. The
smaller orbit's maximal point stabilizer escapes M and hence gives a new
original constrained context at that point. The existing quasisimple
exclusion discharges the alternative for the new containing component.

At this local opposite point an actual opposite cubic fixes the local
three-space. This excludes the natural four and orthogonal six actions;
the augmentation seven action was already excluded. The smaller orbit is
therefore an irreducible five- or ten-dimensional SL₅(2) module. Its kernel
still equals the original VI kernel and the FundamentalSetup is unchanged.

Source: Aschbacher–Smith 10.2.9, printed pp.752–753.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
open BinaryNaturalDual.VectorStabilizers
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The unique local point-fixed line is fixed by the entire half-Sylow. -/
theorem Context.local_seed_fixed_by_halfSylow_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G)) :
    u ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G) := by
  let W := ⁅D.moduleSubgroup,L⁆
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let F := W ⊓ centralizer (pointSylow T v : Set G)
  let F₀ := W ⊓ centralizer (S : Set G)
  have hSF : F₀ ≤ F := inf_le_inf_left _
    (centralizer_le (le_inf inf_le_left c.escaping.sylow_normalizes))
  have hne : F₀ ≠ ⊥ := inf_centralizer_ne_bot_of_pGroups S W
    (T.isPGroup'.to_le inf_le_left)
    ((source_original_full_moved_elementary D).isPGroup.to_le
      (commutator_mono (le_componentOrbit _ _) le_rfl))
    ((le_sup_right : S ≤ halfJoin T L).trans c.halfJoin_normalizes_local_moved)
    (Selection.ModuleChoice.local_moved_ne_bot D)
  have hlo := (one_lt_card_iff_ne_bot F₀).mpr hne
  have hcard : Nat.card F = 2 := c.local_point_fixed_card_of_local_natural h
  have he : F₀ = F := eq_of_le_of_card_ge hSF (by omega)
  exact (show u ∈ F₀ from he.symm ▸ hu).2


/-- Conjugating the actual local fixed line gives a point in the opposite
local natural copy, fixed by the whole half-Sylow and saturated in M. -/
theorem Context.local_seed_opposite_saturated_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let w := (MulAut.conj t) u
    pointSylow T w = (T : Subgroup G) ⊓ normalizer (L : Set G) ∧
      Chapter1.IsSylowIn 2 (pointSylow T w)
        (D.maximalLocal ⊓ centralizer ({w} : Set G)) := by
  let w := (MulAut.conj t) u
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun hh => c.escaping.t_not_normalizes (hh c.escaping.t_mem)
  have hi := source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  let N := (normalizer (L : Set G)).subgroupOf (T : Subgroup G)
  let : N.Normal := normal_of_index_eq_two hi
  have hfix := c.local_seed_fixed_by_halfSylow_of_local_natural h hu
  have hSC : S ≤ centralizer ({w} : Set G) := by
    intro x hx
    have hx' : t⁻¹ * x * t ∈ S := by
      have hh := (inferInstance : N.Normal).conj_mem ⟨x,hx.1⟩ hx.2
        (⟨t,c.escaping.t_mem⟩ : (T : Subgroup G))⁻¹
      exact ⟨(T : Subgroup G).mul_mem
        ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem c.escaping.t_mem) hx.1)
        c.escaping.t_mem,by
          change ((⟨t,c.escaping.t_mem⟩ : (T : Subgroup G))⁻¹ * ⟨x,hx.1⟩ *
            ⟨t,c.escaping.t_mem⟩) ∈ N
          simpa only [inv_inv] using hh⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj t) (hfix _ hx')
    have hc : (MulAut.conj t) (t⁻¹ * x * t) = x := by simp [MulAut.conj_apply,mul_assoc]
    simpa only [map_mul,hc] using hh
  have hwW : w ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom :=
    mem_map_of_mem _ ((commutator_mono (le_componentOrbit _ _) le_rfl) hu.1)
  have hwV := partner_le_fullModule D c.escaping.t_mem hwW
  have hwne : w ≠ 1 := fun he => hne ((MulAut.conj t).map_eq_one_iff.mp he)
  have hw0 : w ∉ centralizer (localOrbit T L : Set G) := by
    intro hh
    exact hwne (mem_bot.mp (c.full_fixed_eq_bot ▸
      (show w ∈ D.fullModule ⊓ centralizer (localOrbit T L : Set G) from ⟨hwV,hh⟩)))
  have hCM : D.maximalLocal ⊓ centralizer ({w} : Set G) ≤ normalizer (L : Set G) :=
    source_nonnormal_element_centralizer_stabilizes D hn (c.escaping.crossed hwW) hw0
  have he : pointSylow T w = S := le_antisymm
    (le_inf inf_le_left (by
      intro x hx
      exact hCM ⟨le_normalizer_componentOrbit L T hx.1,hx.2⟩))
    (le_inf inf_le_left hSC)
  refine ⟨he,?_⟩
  rw [he]
  exact (source_nonnormal_stabilizer_sylow D hn).restrict
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) hSC)
    (le_inf inf_le_left hCM)


/-- Escape at the saturated local point supplies a new original constrained context. -/
theorem Context.reselect_local_point_of_escaping_centralizer_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1)
    (hout : ¬ centralizer ({(MulAut.conj t) u} : Set G) ≤ D.maximalLocal) :
    let w := (MulAut.conj t) u
    ∃ J : Subgroup G, Context D t w J ∧
      w ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom ∧
      pointSylow T w = (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  let w := (MulAut.conj t) u
  have hw : w ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom :=
    mem_map_of_mem _ ((commutator_mono (le_componentOrbit _ _) le_rfl) hu.1)
  have hwne : w ≠ 1 := fun he => hne ((MulAut.conj t).map_eq_one_iff.mp he)
  have hs := c.local_seed_opposite_saturated_of_local_natural h hu hne
  have hp := pointSylowControl_of_thompson_centralizes D c.many
    c.escaping.t_mem c.escaping.t_not_normalizes c.escaping.crossed
    (c.full_thompson_fixed_of_three (c.three_dvd_of_prepared (c.prepared_of_three h.three_dvd)))
  obtain ⟨J,hJ⟩ := escapingComponent_of_local_sylow D c.escaping.t_mem
    c.escaping.t_not_normalizes c.escaping.crossed c.escaping.half_unique hp hw hwne hs.2 hout
  have hnJ : ¬ IsQuasisimple J := by
    intro hq
    let := hq
    exact Quasisimple.quasisimple_impossible D hJ c.nonA5
  have hwV := partner_le_fullModule D c.escaping.t_mem hw
  have hCW := (Subgroup.centralizer_le_normalizer _).trans hJ.moved_normalizer
  refine ⟨J,⟨c.many,c.minimal,c.nonA5,hJ,hnJ,?_,?_⟩,mem_map_of_mem _ hu.1,hs.1⟩
  · exact source_a5_point_component_characteristicTwo D hwV hwne (c.escaping.crossed hw)
      hCW J hJ.le_centralizer hJ.component hnJ
  · exact source_a5_point_component_reduced_module D hwV hwne (c.escaping.crossed hw)
      hCW J hJ.strict.le hJ.le_centralizer hJ.component hJ.normalizes hnJ hJ.sylow


/-- The containing component is the literal cubic residual of its point centralizer. -/
theorem Context.component_eq_point_residual_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) :
    (primeToResidual 3 (centralizer ({v} : Set G))).map
      (centralizer ({v} : Set G)).subtype = I := by
  let := c.reduced.normal
  let := c.reduced.elementary
  obtain ⟨_,_,d,hd,⟨E⟩⟩ := c.original_binary_source_action (c.actionFacts_of_three h.three_dvd)
  exact c.component_eq_point_residual_of_binary_actor hd E

/-- A point in the opposite local natural copy has a genuine opposite
cubic in the original containing component, centralizing the entire full moved subgroup. -/
theorem Context.opposite_cubic_of_local_natural_point
    (c : Context D t v I) (h : LocalNaturalCover D)
    (hvlocal : v ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom) :
    ∃ y : G, orderOf y = 3 ∧ y ∈ I ∧ y ∈ centralizer ({v} : Set G) ∧
      y ∈ normalizer (L : Set G) ∧
      y ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  obtain ⟨e,⟨s⟩⟩ := h
  have hf : LocalNaturalCover D := ⟨e,⟨s⟩⟩
  obtain ⟨w,hw,hwt⟩ := hvlocal
  let wW : (⁅D.moduleSubgroup,L⁆ : Subgroup G) := ⟨w,hw⟩
  have hwne : wW ≠ 1 := by
    intro he
    apply c.escaping.v_ne
    rw [←hwt,show w = 1 from congrArg Subtype.val he,map_one]
  let C := L ⊓ centralizer ({w} : Set G)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hi : (C.subgroupOf L).index = 7 :=
    s.linearThree_pointCentralizer_index q
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) wW hwne
  have hc := (C.subgroupOf L).index_mul_card
  rw [hi,Nat.card_congr (subgroupOfEquivOfLe (show C ≤ L from inf_le_left)).toEquiv] at hc
  have hL : Nat.card L = 168 * Nat.card (pCore 2 L) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 L),
      Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
  have hC : Nat.card C = 24 * Nat.card (pCore 2 L) := by omega
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 3
    (by rw [hC]; exact dvd_mul_of_dvd_left (by decide) _)
  let y := (MulAut.conj t) (x : G)
  have hy3 : orderOf y = 3 := ((MulAut.conj t).orderOf_eq (x:G)).trans
    ((Subgroup.orderOf_coe x).trans hx)
  have hyv : y ∈ centralizer ({v} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg (MulAut.conj t) (mem_centralizer_singleton_iff.mp x.property.2)
    change (MulAut.conj t) w = v at hwt
    simpa only [map_mul,hwt] using he
  have hyI : y ∈ I := by
    rw [←c.component_eq_point_residual_of_local_natural hf]
    apply mem_map_of_mem (centralizer ({v} : Set G)).subtype (x := ⟨y,hyv⟩)
    apply mem_primeToResidual_of_pow (n := 1)
    apply Subtype.ext
    change y ^ (3 ^ 1) = 1
    simpa only [pow_one,hy3] using pow_orderOf_eq_one y
  have hyB : y ∈ L.map (MulAut.conj t).toMonoidHom := mem_map_of_mem _ x.property.1
  refine ⟨y,hy3,hyI,hyv,?_,le_centralizer_iff.mp c.moved_centralizes_opposite hyB⟩
  apply source_nonnormal_orbit_le_normalizer D
    (fun hh => c.escaping.t_not_normalizes (hh c.escaping.t_mem))
  exact (mem_normalizer_iff.mp (le_normalizer_componentOrbit L T c.escaping.t_mem) (x:G)).mp
    ((le_componentOrbit L T) x.property.1)

private theorem cubic_aut_eq_one_of_fixed_eight
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 16)
    (a : MulAut E) (ha : a ^ 3 = 1)
    (hfix : 8 ≤ Nat.card (FixedPoints.subgroup (zpowers a) E)) : a = 1 := by
  let P := zpowers a
  let F := FixedPoints.subgroup P E
  have hp : IsPGroup 3 P := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr ha)
  have hmod := hp.card_modEq_card_fixedPoints E
  change Nat.card E % 3 = Nat.card F % 3 at hmod
  rw [hE] at hmod
  have hdiv : Nat.card F ∣ 16 := hE ▸ F.card_subgroup_dvd_card
  have hmem := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
  have hdivs : (16 : ℕ).divisors = {1,2,4,8,16} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  change 8 ≤ Nat.card F at hfix
  have hcard : Nat.card F = 16 := by omega
  have htop := F.eq_top_of_card_eq (hcard.trans hE.symm)
  apply MulEquiv.ext
  intro x
  exact (show x ∈ F from htop ▸ mem_top x) ⟨a,mem_zpowers a⟩

/-- At a point in the local opposite three-space, the smaller orbit cannot
have dimension four: the opposite cubic fixes a hyperplane and would lie in O₂(I). -/
theorem Context.no_four_dimensional_local_orbit_of_local_natural_point
    (c : Context D t v I) (h : LocalNaturalCover D)
    (hvlocal : v ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom)
    {u : G} (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1)
    (hd : letI := (c.local_seed_orbit_reduced hu).elementary
      Module.finrank (ZMod 2)
        (Additive ((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I))) = 4) : False := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let R := conjugateSpanBy (zpowers u) I
  let U := R.subgroupOf H
  let W := ⁅D.moduleSubgroup,L⁆
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  have hspan : W ≤ R := by
    change ⁅D.moduleSubgroup,L⁆ ≤ conjugateSpanBy (zpowers u) I
    rw [←c.local_orbit_eq_seed_orbit_of_local_natural h hu hne]
    exact le_conjugateSpanBy _ _
  have hRVI : R ≤ orbitModule D v I := conjugateSpanBy_mono (zpowers_le.mpr
    ⟨(commutator_mono (le_componentOrbit _ _) le_rfl) hu.1,hu.2⟩) le_rfl
  have hRH : R ≤ H := hRVI.trans c.orbit_le_join
  obtain ⟨y,hy3,hyI,_,_,hyc'⟩ := c.opposite_cubic_of_local_natural_point h hvlocal
  have hyc : y ∈ centralizer (W : Set G) :=
    centralizer_le (commutator_mono (le_componentOrbit _ _) le_rfl) hyc'
  let yH : H := ⟨y,(le_sup_left : I ≤ H) hyI⟩
  let a : MulAut U := MulAut.conjNormal yH
  have ha : a ^ 3 = 1 := by
    rw [←map_pow]
    have hy : yH ^ 3 = 1 := Subtype.ext (hy3 ▸ pow_orderOf_eq_one y)
    rw [hy,map_one]
  have hU : Nat.card U = 16 := by
    change Nat.card (Additive U) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    rfl
  have hW : Nat.card W = 8 := c.local_moved_card_of_local_natural h
  let F := FixedPoints.subgroup (zpowers a) U
  let j : W → F := fun w =>
    ⟨⟨⟨w,hRH (hspan w.property)⟩,hspan w.property⟩,by
      let wU : U := ⟨⟨w,hRH (hspan w.property)⟩,hspan w.property⟩
      have haw : a wU = wU := by
        apply Subtype.ext
        apply Subtype.ext
        change y * (w : G) * y⁻¹ = w
        rw [←hyc w w.property,mul_inv_cancel_right]
      have hle : zpowers a ≤ MulAction.stabilizer (MulAut U) wU := zpowers_le.mpr haw
      intro b
      exact hle b.property⟩
  have hj : Function.Injective j := by
    intro w z he
    apply Subtype.ext
    exact congrArg (fun x : F => (((x : U) : H) : G)) he
  have hone : a = 1 := cubic_aut_eq_one_of_fixed_eight hU a ha
    (hW ▸ Nat.card_le_card_of_injective j hj)
  have hyC : yH ∈ centralizer (U : Set H) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact hone
  let yK : K := ⟨yH,hyI⟩
  have hyker : yK ∈ ((actionMk U).subgroupMap K).ker :=
    Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hyC)
  rw [c.local_seed_component_kernel_of_local_natural h hu hne] at hyker
  let z : pCore 2 K := ⟨yK,hyker⟩
  have hz3 : orderOf z = 3 := (Subgroup.orderOf_coe z).symm.trans
    ((Subgroup.orderOf_coe yK).symm.trans ((Subgroup.orderOf_coe yH).symm.trans hy3))
  have hzne : z ≠ 1 := by intro he; rw [he,orderOf_one] at hz3; omega
  have htwo := (pCore_isPGroup (p := 2) (G := K)).dvd_orderOf hzne
  rw [hz3] at htwo
  norm_num at htwo


/-- The reselected local-point configuration leaves only dimensions five,
six or ten; both the four-dimensional action and the augmentation cover are excluded. -/
theorem Context.local_seed_dimension_of_local_natural_point
    (c : Context D t v I) (h : LocalNaturalCover D)
    (hvlocal : v ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom)
    {u : G} (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)
    letI := (c.local_seed_orbit_reduced hu).elementary
    Module.finrank (ZMod 2) (Additive U) = 5 ∨
      Module.finrank (ZMod 2) (Additive U) = 6 ∨
      Module.finrank (ZMod 2) (Additive U) = 10 :=
  (c.local_seed_dimension_without_seven_of_local_natural h hu hne).resolve_left
    (c.no_four_dimensional_local_orbit_of_local_natural_point h hvlocal hu hne)

/-- The natural six-dimensional action is impossible at a local opposite
point. The local three-space is maximal isotropic, so its pointwise-fixing
opposite cubic would lie in the actual two-core kernel. -/
theorem Context.no_orthogonal_local_orbit_of_local_natural_point
    (c : Context D t v I) (h : LocalNaturalCover D)
    (hvlocal : v ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom)
    {u : G} (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf H).map (actionMk U)
    ∀ (_E : ActionEquiv ((action U).comp A.subtype) (alternatingNatural 8)), False := by
  obtain ⟨e,⟨r⟩⟩ := h
  have hf : LocalNaturalCover D := ⟨e,⟨r⟩⟩
  let H := pointJoin T v I
  let U := (conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)
  let R := conjugateSpanBy (zpowers u) I
  let K := I.subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let W := ⁅D.moduleSubgroup,L⁆
  let : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le
    (show W ≤ ⁅D.fullModule,L⁆ from commutator_mono (le_componentOrbit _ _) le_rfl)
  let A := K.map (actionMk U)
  dsimp only
  intro E
  have hWI : W ≤ I := (commutator_mono (le_componentOrbit _ _) le_rfl).trans
    ((source_full_moved_le_component D).trans c.escaping.strict.le)
  have hRI : R ≤ I := conjugateSpanBy_le_self (zpowers_le.mpr (hWI hu.1))
  have hRH : R ≤ H := hRI.trans le_sup_left
  have hspan : W ≤ R := by
    change ⁅D.moduleSubgroup,L⁆ ≤ conjugateSpanBy (zpowers u) I
    rw [←c.local_orbit_eq_seed_orbit_of_local_natural hf hu hne]
    exact le_conjugateSpanBy _ _
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ρ : Representation (ZMod 2) L (Fin 3 → ZMod 2) :=
    (specialLinearNatural (k := ZMod 2) 3).comp q
  let : IsIrreducible ρ := (irreducible_comp_surjective_iff q hq _).mpr
    BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  let f : I →* A := ((actionMk U).subgroupMap K).comp
    (subgroupOfEquivOfLe (show I ≤ H from le_sup_left)).symm.toMonoidHom
  let φ := E.groupEquiv.toMonoidHom.comp f
  let τ := (alternatingNatural 8).comp φ
  let j : R ≃* U := (subgroupOfEquivOfLe hRH).symm
  let s : BinaryConjugationSection I R ⊥ τ := {
    section_le := hRI
    kernel_le := bot_le
    normalized := le_normalizer_conjugateSpanBy _ _
    coordinates := {
      toFun w := Multiplicative.ofAdd (E.linearEquiv (Additive.ofMul (j w)))
      map_one' := by change E.linearEquiv (Additive.ofMul (j 1)) = 0; rw [map_one]; exact E.linearEquiv.map_zero
      map_mul' x y := by
        change E.linearEquiv (Additive.ofMul (j (x*y))) =
          E.linearEquiv (Additive.ofMul (j x)) + E.linearEquiv (Additive.ofMul (j y))
        rw [map_mul]; exact E.linearEquiv.map_add _ _ }
    onto := by
      intro w
      exact ⟨j.symm (E.linearEquiv.symm w.toAdd).toMul,by
        change E.linearEquiv (Additive.ofMul (j (j.symm _))) = w.toAdd
        rw [j.apply_symm_apply]
        exact E.linearEquiv.apply_symm_apply _⟩
    kernel_eq := by
      ext w
      change E.linearEquiv (Additive.ofMul (j w)) = 0 ↔ (w:G) = 1
      rw [E.linearEquiv.map_eq_zero_iff]
      change j w = 1 ↔ (w:G) = 1
      rw [j.map_eq_one_iff]
      exact Subtype.val_inj.symm
    equivariant := by
      intro i w
      have ha : action U (f i).val (Additive.ofMul (j w)) =
          Additive.ofMul (j ⟨(i:G)*w*(i:G)⁻¹,
            (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy _ _ i.property) w).mp w.property⟩) := by
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg H.subtype
          (action_apply U ⟨i,(show I ≤ H from le_sup_left) i.property⟩ (Additive.ofMul (j w)))
      exact (congrArg E.linearEquiv ha.symm).trans (E.intertwines (f i) _) }
  have hzero (b : ρ.IntertwiningMap ρ.dual) : b = 0 := by
    let b' : BinaryLinearThree.W.IntertwiningMap BinaryLinearThree.W.dual := {
      toLinearMap := b.toLinearMap
      isIntertwining' := by
        intro g
        obtain ⟨l,rfl⟩ := hq g
        apply LinearMap.ext
        intro w
        apply LinearMap.ext
        intro x
        have he := congrArg (fun z => z x) (LinearMap.congr_fun (b.isIntertwining' l) w)
        change b (ρ l w) x = b w (specialLinearNatural 3 (q l⁻¹) x) at he
        change b (ρ l w) x = b w (specialLinearNatural 3 ((q l)⁻¹) x)
        simpa only [map_inv q] using he }
    have he := BinaryLinearThree.NaturalDual.natural_dual_zero b'
    apply Representation.IntertwiningMap.ext
    exact congrArg (fun z : BinaryLinearThree.W.IntertwiningMap BinaryLinearThree.W.dual => z.toLinearMap) he
  let B := BinaryPermutation.naturalPairing (Fin 8)
  have hB : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
    ((LinearMap.ker_eq_bot).mpr (BinaryPermutation.naturalPairing_injective (Fin 8)))
  have hinv (i : I) (x z : BinaryPermutation.natural (Fin 8)) :
      B (τ i x) (τ i z) = B x z := by
    obtain ⟨u,rfl⟩ := BinaryPermutation.coreToNatural_surjective x
    obtain ⟨w,rfl⟩ := BinaryPermutation.coreToNatural_surjective z
    change BinaryPermutation.naturalPairing (Fin 8)
      (BinaryPermutation.naturalRepresentation (Fin 8) (φ i).val (BinaryPermutation.coreToNatural (Fin 8) u))
      (BinaryPermutation.naturalRepresentation (Fin 8) (φ i).val (BinaryPermutation.coreToNatural (Fin 8) w)) = _
    rw [←BinaryPermutation.coreToNatural_equivariant,←BinaryPermutation.coreToNatural_equivariant,
      BinaryPermutation.naturalPairing_apply_core,BinaryPermutation.naturalPairing_apply_core]
    change (∑ j, u.val ((φ i).val.symm j) * w.val ((φ i).val.symm j)) = ∑ j, u.val j * w.val j
    exact Equiv.sum_comp (φ i).val.symm (fun j => u.val j * w.val j)
  have hdim : Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 8)) =
      2 * Module.finrank (ZMod 2) (Fin 3 → ZMod 2) := by
    rw [BinaryPermutation.finrank_natural_even (Fin 8) (by decide),Module.finrank_fin_fun]
    decide
  let : Nontrivial (BinaryPermutation.natural (Fin 8)) :=
    Module.nontrivial_of_finrank_pos (by rw [hdim,Module.finrank_fin_fun]; decide)
  obtain ⟨y,hy3,hyI,_,_,hyC⟩ := c.opposite_cubic_of_local_natural_point hf hvlocal
  let yI : I := ⟨y,hyI⟩
  have hy : yI ^ 3 = 1 := Subtype.ext (hy3 ▸ pow_orderOf_eq_one y)
  have hyact : τ yI = 1 := r.cubic_eq_one_of_centralizes_generator τ s
    c.escaping.strict.le hspan (conjugateSpanBy_mono (zpowers_le.mpr hu.1) le_rfl)
    hzero hdim B hB hinv yI hy
    (centralizer_le (commutator_mono (le_componentOrbit _ _) le_rfl) hyC)
  have hf1 : f yI = 1 := by
    apply E.groupEquiv.map_eq_one_iff.mp
    apply Subtype.ext
    apply BinaryPermutation.naturalRepresentation_injective (Fin 8) (by decide)
    exact hyact.trans (map_one (BinaryPermutation.naturalRepresentation (Fin 8))).symm
  let yH : H := ⟨y,(le_sup_left : I ≤ H) hyI⟩
  let yK : K := ⟨yH,hyI⟩
  have hyker : yK ∈ ((actionMk U).subgroupMap K).ker := hf1
  have hycore := (c.local_seed_component_kernel_of_local_natural hf hu hne).le hyker
  let z : pCore 2 K := ⟨yK,hycore⟩
  have hz3 : orderOf z = 3 := (Subgroup.orderOf_coe z).symm.trans
    ((Subgroup.orderOf_coe yK).symm.trans ((Subgroup.orderOf_coe yH).symm.trans hy3))
  have hzne : z ≠ 1 := by intro he; rw [he,orderOf_one] at hz3; omega
  have htwo := (pCore_isPGroup (p := 2) (G := K)).dvd_orderOf hzne
  rw [hz3] at htwo
  norm_num at htwo

/-- At a local opposite point all binary-four actions are excluded. The
actual smaller orbit has the full SL₅(2) actor and is irreducible of dimension five or ten. -/
theorem Context.local_seed_five_of_local_natural_point
    (c : Context D t v I) (h : LocalNaturalCover D)
    (hvlocal : v ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom)
    {u : G} (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf H).map (actionMk U)
    Nonempty (A ≃* SL(5,ZMod 2)) ∧ A = ⊤ ∧
      IsIrreducible ((action U).comp A.subtype) ∧
      (Module.finrank (ZMod 2) (Additive U) = 5 ∨
        Module.finrank (ZMod 2) (Additive U) = 10) := by
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  have he : Nonempty (((I.subgroupOf (pointJoin T v I)).map
      (actionMk ((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)))) ≃*
        SL(5,ZMod 2)) := by
    cases c.local_seed_single_action_of_local_natural h hu hne with
    | natural d hd _ E =>
      rcases hd with rfl | rfl
      · exact (c.no_four_dimensional_local_orbit_of_local_natural_point h hvlocal hu hne
          (E.linearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2)))).elim
      · exact ⟨E.groupEquiv⟩
    | orthogonal _ model _ =>
      rcases model with h6 | h7
      · exact (c.no_orthogonal_local_orbit_of_local_natural_point h hvlocal hu hne h6.some).elim
      · exact (c.no_augmentation_cover_of_local_seed hu hne h7.some).elim
    | exterior E _ _ _ => exact ⟨E⟩
  exact ⟨he,c.local_seed_irreducible_of_binary_five_of_local_natural h hu hne he.some⟩


/-- Every nonzero local point-fixed seed has a maximal point centralizer
in the literal containing join. -/
theorem Context.local_seed_point_maximal_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    IsCoatom (((pointJoin T v I) ⊓ centralizer ({u} : Set G)).subgroupOf
      (pointJoin T v I)) := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let S := (pointSylow T v).subgroupOf H
  let R := conjugateSpanBy (zpowers u) I
  let U := R.subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let q := actionMk U
  let A := K.map q
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have huR : u ∈ R := le_conjugateSpanBy _ _ (mem_zpowers u)
  have hRVI : R ≤ orbitModule D v I := conjugateSpanBy_mono (zpowers_le.mpr
    ⟨(commutator_mono (le_componentOrbit _ _) le_rfl) hu.1,hu.2⟩) le_rfl
  have hRH : R ≤ H := hRVI.trans c.orbit_le_join
  let w : Additive U := Additive.ofMul ⟨⟨u,hRH huR⟩,huR⟩
  have hw : w ≠ 0 := fun he => hne (congrArg (fun a : Additive U => ((a.toMul:H):G)) he)
  let B := representationStabilizer (action U) w
  have hfix (x : H) : q x ∈ B ↔ (x:G) ∈ centralizer ({u} : Set G) := by
    change action U (q x) w = w ↔ _
    constructor
    · intro hx
      apply mem_centralizer_singleton_iff.mpr
      have he := congrArg (fun a : Additive U => ((a.toMul:H):G)) hx
      have ha := congrArg H.subtype (action_apply U x w)
      exact mul_inv_eq_iff_eq_mul.mp (ha.symm.trans he)
    · intro hx
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      have ha := congrArg H.subtype (action_apply U x w)
      exact ha.trans (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx))
  have hSB : S.map q ≤ B := by
    rintro _ ⟨x,hx,rfl⟩
    exact (hfix x).mpr (mem_centralizer_singleton_iff.mpr (hu.2 x hx))
  have hKS : K ⊔ S = ⊤ := by
    rw [←subgroupOf_sup (show I ≤ H from le_sup_left)
      (show pointSylow T v ≤ H from le_sup_right),subgroupOf_self]
  have hAB : A ⊔ B = ⊤ := by
    apply top_unique
    have hh : A ⊔ S.map q = ⊤ := by
      rw [←Subgroup.map_sup,hKS,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [←hh]
    exact sup_le_sup_left hSB A
  obtain ⟨P,hP⟩ := c.join_sylow
  obtain ⟨S₀,hS₀⟩ := P.exists_subgroupOf_eq_of_normal K
  let Q := S₀.mapSurjective (q.subgroupMap_surjective K)
  have hQ (a : A) (ha : a ∈ (Q : Subgroup A)) : action U a.val w = w := by
    obtain ⟨x,hx,rfl⟩ := ha
    have hxP : (x:H) ∈ (P : Subgroup H) := by
      change x ∈ (P : Subgroup H).subgroupOf K
      rw [←hS₀]
      exact hx
    have hxS : ((x:H):G) ∈ pointSylow T v := hP ▸ mem_map_of_mem H.subtype hxP
    exact (hfix (x:H)).mpr (mem_centralizer_singleton_iff.mpr (hu.2 _ hxS))
  have hmax : IsCoatom (B.subgroupOf A) := by
    cases c.local_seed_single_action_of_local_natural h hu hne with
    | natural d hd ht E =>
      change A = ⊤ at ht
      rcases hd with rfl | rfl
      · have hh := BinaryFourPointStabilizers.natural_isCoatom
          (E.linearEquiv w) (fun he => hw (E.linearEquiv.map_eq_zero_iff.mp he))
        apply (OrderIso.isCoatom_iff E.groupEquiv.mapSubgroup _).mp
        change IsCoatom ((representationStabilizer ((action U).comp A.subtype) w).map E.groupEquiv.toMonoidHom)
        rw [BinaryNaturalDual.Transport.stabilizer_map _ _ E.groupEquiv E.linearEquiv E.intertwines]
        exact hh
      · have hE := c.local_seed_irreducible_of_binary_five_of_local_natural h hu hne E.groupEquiv
        have hma : IsCoatom B := by
          let : IsIrreducible (action U) := (irreducible_comp_surjective_iff A.subtype
            (by intro a; exact ⟨⟨a,ht.symm ▸ mem_top a⟩,rfl⟩) _).mp hE.2.1
          let e : ActionQuotient U ≃* SL(5,ZMod 2) :=
            (topEquiv.symm.trans (MulEquiv.subgroupCongr ht.symm)).trans E.groupEquiv
          exact (BinaryFivePointStabilizers.natural_structure (action U) (action_faithful U) e
            (E.linearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))) w hw).1
        have he : B.subgroupOf A = B.comap A.subtype := rfl
        rw [he]
        exact isCoatom_comap_of_surjective
          (by intro a; exact ⟨⟨a,ht.symm ▸ mem_top a⟩,rfl⟩) hma
    | orthogonal _ model _ =>
      rcases model with hn | ha
      · let E := hn.some
        let Q' := Q.mapSurjective (f := E.groupEquiv.toMonoidHom) E.groupEquiv.surjective
        have hh := BinaryFourPointStabilizers.orthogonal_isCoatom Q' (E.linearEquiv w)
          (fun he => hw (E.linearEquiv.map_eq_zero_iff.mp he)) (by
            rintro _ ⟨a,ha,rfl⟩
            exact (E.intertwines a w).symm.trans (congrArg E.linearEquiv (hQ a ha)))
        apply (OrderIso.isCoatom_iff E.groupEquiv.mapSubgroup _).mp
        change IsCoatom ((representationStabilizer ((action U).comp A.subtype) w).map E.groupEquiv.toMonoidHom)
        rw [BinaryNaturalDual.Transport.stabilizer_map _ _ E.groupEquiv E.linearEquiv E.intertwines]
        exact hh
      · exact (c.no_augmentation_cover_of_local_seed hu hne ha.some).elim
    | exterior E ht hi hd =>
      change A = ⊤ at ht
      let : IsIrreducible (action U) := (irreducible_comp_surjective_iff A.subtype
        (by intro a; exact ⟨⟨a,ht.symm ▸ mem_top a⟩,rfl⟩) _).mp hi
      let e : ActionQuotient U ≃* SL(5,ZMod 2) :=
        (topEquiv.symm.trans (MulEquiv.subgroupCongr ht.symm)).trans E
      let P' := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
      have hPB : (P' : Subgroup (ActionQuotient U)) ≤ B := by
        rintro _ ⟨x,hx,rfl⟩
        exact (hfix x).mpr (mem_centralizer_singleton_iff.mpr
          (hu.2 x (hP ▸ mem_map_of_mem H.subtype hx)))
      have hm := (BinaryFivePointStabilizers.exterior_structure (action U) e hd P' w hw hPB).1
      exact isCoatom_comap_of_surjective
        (by intro a; exact ⟨⟨a,ht.symm ▸ mem_top a⟩,rfl⟩) hm
  have hm : IsCoatom B := isCoatom_of_subgroupOf_normal_supplement A B hAB hmax
  have hc : (H ⊓ centralizer ({u} : Set G)).subgroupOf H = B.comap q := by
    ext x
    exact ⟨fun hx => (hfix x).mpr hx.2, fun hx => ⟨x.property,(hfix x).mp hx⟩⟩
  rw [hc]
  exact isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective _) hm

/-- The local-point selection is available for every original local natural
marking, including the binary-four containing actions. -/
theorem Context.reselect_local_point_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let w := (MulAut.conj t) u
    ∃ J : Subgroup G, Context D t w J ∧
      w ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom ∧
      pointSylow T w = (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  apply c.reselect_local_point_of_escaping_centralizer_of_local_natural h hu hne
  intro hh
  have hmax := c.local_seed_point_maximal_of_local_natural h hu hne
  apply c.local_seed_point_escapes_of_maximal hu.1 hne hmax
  intro x hx
  have hx' : (MulAut.conj t) x ∈ centralizer ({(MulAut.conj t) u} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg (MulAut.conj t) (mem_centralizer_singleton_iff.mp hx.2)
  exact (mem_normalizer_iff.mp
    (D.maximalLocal.le_normalizer (le_normalizer_componentOrbit L T c.escaping.t_mem)) x).mpr
      (hh hx')

/-- The original local natural marking supplies a new original constrained context at a
local opposite point, with an actual irreducible five- or ten-dimensional
smaller orbit. The same setup D and full moved subgroup are retained. -/
theorem Context.local_binary_five_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let w := (MulAut.conj t) u
    ∃ J : Subgroup G, ∃ c' : Context D t w J,
      w ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom ∧
      pointSylow T w = (T : Subgroup G) ⊓ normalizer (L : Set G) ∧
      ∃ hu' : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T w : Set G),
      let H := pointJoin T w J
      let U := (conjugateSpanBy (zpowers u) J).subgroupOf H
      letI := (c'.local_seed_orbit_reduced hu').normal
      letI := (c'.local_seed_orbit_reduced hu').elementary
      let A := (J.subgroupOf H).map (actionMk U)
      centralizer (U : Set H) = centralizer (internalModule D w J : Set H) ∧
      Nonempty (A ≃* SL(5,ZMod 2)) ∧ A = ⊤ ∧
      IsIrreducible ((action U).comp A.subtype) ∧
      (Module.finrank (ZMod 2) (Additive U) = 5 ∨
        Module.finrank (ZMod 2) (Additive U) = 10) := by
  obtain ⟨J,c',hw,hs⟩ := c.reselect_local_point_of_local_natural h hu hne
  have hu' : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T ((MulAut.conj t) u) : Set G) := by
    rw [hs]
    exact ⟨hu.1,c.local_seed_fixed_by_halfSylow_of_local_natural h hu⟩
  refine ⟨J,c',hw,hs,hu',?_⟩
  exact ⟨c'.local_seed_centralizer_eq_of_local_natural h hu' hne,
    c'.local_seed_five_of_local_natural_point h hw hu' hne⟩


end CFSG.Quasithin.Chapter10.PointControl.Constrained
