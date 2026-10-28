module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionFixedResidual
public import Theory.GroupTheory.GeneralizedFitting.NormalInnerInvolution
public import Theory.GroupTheory.RankOneInvariantKernelOrbit
public import Theory.Mathieu.SchurMultipliers.FiniteCovers
public import Theory.SpecificGroups.PSL3Three.FourNormalizer.Automorphisms
public import Theory.SpecificGroups.PSL3Three.Simplicity
public import Theory.SpecificGroups.PSL2.OrdinaryBorelGeometry
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.Suzuki.RootOmega

/-!
# Component actions and the original Sylow central omega

A centerless component whose order is divisible by sixteen is normal:
two distinct conjugates would force a factor 256 in the centralizer order,
whose Sylow two-subgroups have order 128. The involution implementing the
original inner action lies in the marked Sylow central omega <z,w>.
It is z or zw, so every other component would centralize z, contrary to
the original 1.1.5 catalogue. Thus this component is the entire layer.
The literal quotient C/<w> acts faithfully on it by conjugation, retaining
both the quotient Sylow order 64 and the original centralizer order 192.
These bounds exclude M11, its central covers, PSL3(3), PSL2(16) and PSL2(32).

Separately, a centerless component with Sylow order 64 has a Sylow subgroup
complementary to the central line <w> in the original Sylow. Its central
omega therefore has order at most two. The actual root-center calculations
exclude PSL2(64), PSL3(4) and Sz(8). The final catalogue application retains
the original action, fixed Sylow and fixed-residual order dividing 48.
The L3(4) central cover and the remaining small and odd rows are explicit;
quotient recognition and final core collapse remain with this source owner.

Source: Aschbacher--Smith 14.3.22, printed p.999, inspecting the two marked
local centralizers after 1.1.5(3); refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)

include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs hc s


/-- A centerless normal component with the original inner action is the entire layer. -/
theorem source_triple_layer_eq_of_normal_inner
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    [D.Normal] (hzD : center D = ⊥) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2) :
    componentLayer (ResidualFusion.C (tripleProduct d a)) = D := by
  let C := ResidualFusion.C (tripleProduct d a)
  let w := tripleProduct d a
  have hlocal := source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨S,M₁,hS,hSc,hM₁,h115,_,hmodels⟩ := source_triple_component_catalogue
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hzC : z ∈ C := hlocal.plane_centralizes (F.le_seed 1 (s.point.symm ▸ mem_zpowers z))
  let zC : C := ⟨z,hzC⟩
  have ha : MulAut.conjNormal zC = α := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact (hα x).symm
  have hzc : zC ∈ centralizer (S : Set C) := by
    intro t ht
    exact Subtype.ext (h115.central _ (mem_map_of_mem C.subtype ht))
  obtain ⟨x,hx,he,hxO⟩ := normal_inner_involution_implementer_mem_omegaCenter hzD zC α ho hi ha S hzc
  obtain ⟨hxS,hxc,hx2⟩ := (mem_omegaCenterIn_iff _ _).mp hxO
  have hxOG : (x : G) ∈ omegaCenterIn ((T : Subgroup G) ⊓ C) := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hS ▸ mem_map_of_mem C.subtype hxS, ?_, congrArg C.subtype hx2⟩
    intro t ht
    have ht' : t ∈ (S : Subgroup C).map C.subtype := by rw [hS]; exact ht
    obtain ⟨t,htS,rfl⟩ := ht'
    exact congrArg C.subtype (hxc t htS)
  have hzsq : z*z=1 := by simpa only [h115.involution,pow_two] using pow_orderOf_eq_one z
  have hwsq : w*w=1 := by simpa only [hlocal.involution,pow_two] using pow_orderOf_eq_one (tripleProduct d a)
  have hzw : Commute z w := mem_centralizer_singleton_iff.mp hzC
  have hxne : (x : G) ≠ 1 := by
    intro hh
    have hx1 : x=1 := Subtype.ext (Subtype.ext hh)
    rw [hx1,orderOf_one] at hx
    contradiction
  have hxw : (x : G) ≠ w := by
    intro hh
    have hxZ : x ∈ center D := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      apply Subtype.ext
      change (y : G) * (x : G) = (x : G) * (y : G)
      rw [hh]
      exact mem_centralizer_singleton_iff.mp ((y : C).property)
    have hx1 : x=1 := mem_bot.mp (hzD ▸ hxZ)
    exact hxne (congrArg (fun t : D => (t : G)) hx1)
  have hxeq : (x : G) = z ∨ (x : G) = z*w := by
    rcases (mem_closure_pair_iff z w hzsq hwsq hzw (x : G)).mp
      (hlocal.omega_center ▸ hxOG) with hh | hh | hh | hh
    · exact (hxne hh).elim
    · exact Or.inl hh
    · exact (hxw hh).elim
    · exact Or.inr hh
  have huniq (E : Subgroup C) (hE : IsComponent C E) : E=D := by
    by_contra hn
    have hcE : E ≤ centralizer (D : Set C) :=
      commutator_eq_bot_iff_le_centralizer.mp (hE.commutator_eq_bot_of_ne hD hn)
    obtain ⟨_,hEout,_⟩ := hmodels E hE
    apply hEout
    rintro _ ⟨y,hy,rfl⟩
    apply h115.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    change (y : G) * z = z * (y : G)
    have hyx : (x : G) * (y : G) = (y : G) * (x : G) :=
      congrArg C.subtype (hcE hy x x.property)
    rcases hxeq with hh | hh
    · rw [hh] at hyx
      exact hyx.symm
    · rw [hh] at hyx
      have hyw : (y : G)*w=w*(y : G) := mem_centralizer_singleton_iff.mp y.property
      apply mul_right_cancel (b := w)
      simpa only [mul_assoc,←hyw] using hyx.symm
  apply le_antisymm
  · exact sSup_le fun E hE => (huniq E hE).le
  · exact le_sSup hD


/-- The order bound forces a centerless component with two-part at least sixteen to be normal. -/
theorem source_triple_centerless_component_normal
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hzD : center D = ⊥) (h16 : 16 ∣ Nat.card D) : D.Normal := by
  obtain ⟨S,M₁,hS,hSc,_⟩ := source_triple_component_catalogue
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  apply hD.normal_of_square_not_dvd hzD h16
  intro hd
  have hh := S.pow_dvd_card_of_pow_dvd_card (n := 8) hd
  rw [hSc] at hh
  norm_num at hh

/-- The original quotient acts faithfully on this actual component by its original conjugation. -/
theorem source_triple_centerless_component_action
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hzD : center D = ⊥) (h16 : 16 ∣ Nat.card D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2) :
    let C := ResidualFusion.C (tripleProduct d a)
    let W := ResidualFusion.W (tripleProduct d a)
    ∃ ρ : (C ⧸ W) →* MulAut D, Function.Injective ρ ∧
      ∀ (c : C) (x : D), ((ρ (QuotientGroup.mk' W c) x : C) : G) =
        (c : G) * (x : G) * (c : G)⁻¹ := by
  intro C W
  let := source_triple_centerless_component_normal
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD h16
  have hL := source_triple_layer_eq_of_normal_inner
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD hα hi ho
  have hker : (MulAut.conjNormal : C →* MulAut D).ker = W := by
    rw [MulAut.conjNormal_ker_eq_centralizer,←hL]
    exact source_triple_layer_centralizer_eq
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  let ρ := QuotientGroup.lift W (MulAut.conjNormal : C →* MulAut D) hker.symm.le
  exact ⟨ρ,(QuotientGroup.injective_lift_iff _ _ _).mpr hker.symm,fun c x => rfl⟩

/-- The faithful action forces a factor sixty-four in the full component automorphism group. -/
theorem source_triple_centerless_component_automorphism_bound
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hzD : center D = ⊥) (h16 : 16 ∣ Nat.card D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2) :
    64 ∣ Nat.card (MulAut D) := by
  obtain ⟨ρ,hρ,_⟩ := source_triple_centerless_component_action
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD h16 hα hi ho
  obtain ⟨S,M₁,hS,hSc,_⟩ := source_triple_component_catalogue
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hw := (source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).involution
  have hcore := source_triple_twoCore_eq
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hd := (S.mapSurjective (f := QuotientGroup.mk' (ResidualFusion.W (tripleProduct d a)))
    (QuotientGroup.mk'_surjective _)).toSubgroup.card_subgroup_dvd_card
  rw [quotient_sylow_card hw hcore S hSc] at hd
  exact hd.trans (card_dvd_of_injective ρ hρ)

/-- M₁₁, including a proposed central two-cover, cannot be the original component. -/
theorem source_triple_not_mathieuEleven
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2) :
    ¬ Nonempty ((D ⧸ pCore 2 D) ≃* Sporadic.Mathieu.M11) := by
  rintro ⟨eD⟩
  let := hD.2
  obtain ⟨_,hZ,_⟩ := source_triple_component_center
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD
  let eZ := (QuotientGroup.quotientMulEquivOfEq hZ).trans eD
  let f := PerfectCentralCovering.centralQuotientCover eZ
  have hk : f.toMonoidHom.ker = ⊥ := Sporadic.Mathieu.SchurMultipliers.m11_cover_kernel_eq_bot f
  have hzD : center D = ⊥ := (PerfectCentralCovering.centralQuotientCover_ker eZ).symm.trans hk
  let eM : D ≃* Sporadic.Mathieu.M11 := MulEquiv.ofBijective f.toMonoidHom
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hk,f.surjective⟩
  have h16 : 16 ∣ Nat.card D := by
    rw [Nat.card_congr eM.toEquiv,Sporadic.Mathieu.m11_order]
    decide
  have hd := source_triple_centerless_component_automorphism_bound
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD h16 hα hi ho
  let eA : Sporadic.Mathieu.M11 ≃* MulAut Sporadic.Mathieu.M11 :=
    MulEquiv.ofBijective MulAut.conj
      ⟨MulAut.conj_injective_of_center_eq_bot Sporadic.Mathieu.m11_center_eq_bot,
        fun a => by obtain ⟨x,hx⟩ := Sporadic.Mathieu.m11_automorphism_inner a; exact ⟨x,hx⟩⟩
  rw [Nat.card_congr (MulAut.congr eM).toEquiv,←Nat.card_congr eA.toEquiv,
    Sporadic.Mathieu.m11_order] at hd
  norm_num at hd

/-- PSL₃(3) has too small an automorphism two-part for the original quotient. -/
theorem source_triple_not_linearThreeThree
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2) :
    ¬ ClassicalGroup.IsPSL D 3 3 := by
  rintro ⟨E,hEfield,hEfinite,hE,⟨eD⟩⟩
  let := hD.2
  let := hEfield
  let := hEfinite
  let := Fintype.ofFinite E
  let aE : E ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hE)
  let eM := eD.trans (Atlas.fieldEquivPSL 3 aE)
  let := isSimpleGroup_psl3_three
  let : IsSimpleGroup D := eM.isSimpleGroup
  have hzD : center D = ⊥ := center_eq_bot_of_simple_perfect
  have h16 : 16 ∣ Nat.card D := by
    rw [Nat.card_congr eM.toEquiv,Matrix.PSL3Three.card_PSL]
    decide
  have hd := source_triple_centerless_component_automorphism_bound
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD h16 hα hi ho
  rw [Nat.card_congr (MulAut.congr eM).toEquiv,
    Matrix.PSL3Three.FourGeometry.card_fullAutomorphismGroup] at hd
  norm_num at hd

/-- The original point centralizer embeds in the centralizer of the same component action. -/
theorem source_triple_centerless_component_action_centralizer_bound
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hzD : center D = ⊥) (h16 : 16 ∣ Nat.card D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2) :
    192 ∣ Nat.card (centralizer ({α} : Set (MulAut D))) := by
  let C := ResidualFusion.C (tripleProduct d a)
  let W := ResidualFusion.W (tripleProduct d a)
  let q := QuotientGroup.mk' W
  have hlocal := source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  let zC : C := ⟨z,hlocal.plane_centralizes (F.le_seed 1 (s.point.symm ▸ mem_zpowers z))⟩
  obtain ⟨ρ,hρ,hact⟩ := source_triple_centerless_component_action
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD h16 hα hi ho
  have he : ρ (q zC) = α := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact (hact zC x).trans (hα x).symm
  let j : centralizer ({q zC} : Set (C ⧸ W)) →* centralizer ({α} : Set (MulAut D)) :=
    (ρ.comp (centralizer ({q zC} : Set (C ⧸ W))).subtype).codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      rw [←he]
      exact ((show Commute (x : C ⧸ W) (q zC) from
        mem_centralizer_singleton_iff.mp x.property).map ρ).eq)
  have hj : Function.Injective j := by
    intro x y hh
    exact Subtype.ext (hρ (congrArg Subtype.val hh))
  have hd := card_dvd_of_injective j hj
  rwa [source_triple_quotient_point_centralizer_card
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself zC rfl] at hd

/-- Of the large binary linear parameters left by the two-part sieve, only six survives. -/
theorem source_triple_binary_linear_large_parameter
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hDs : IsSimpleGroup D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2)
    {n : ℕ} (hn : 4 ≤ n) (hn6 : n ≤ 6) (hm : ClassicalGroup.IsPSL D 2 (2^n)) : n = 6 := by
  obtain ⟨E,hEfield,hEfinite,hE,⟨eD⟩⟩ := hm
  let := hD.2
  let := hDs
  let := hEfield
  let := hEfinite
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hE
  have hzD : center D = ⊥ := center_eq_bot_of_simple_perfect
  have h16 : 16 ∣ Nat.card D := by
    have hd := (BenderSuzuki.Converse.PUnip E).card_subgroup_dvd_card
    rw [BenderSuzuki.Converse.PUnip_card,hE,←Nat.card_congr eD.toEquiv] at hd
    exact (Nat.pow_dvd_pow 2 hn).trans hd
  have hd := source_triple_centerless_component_action_centralizer_bound
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD h16 hα hi ho
  obtain ⟨x,hx,he,_⟩ := MulAut.inner_involution_representative hzD α ho
    (by obtain ⟨x,hx⟩ := hi; exact ⟨x,hx.symm⟩)
  rw [he,MulAut.card_centralizer_conj_congr eD x] at hd
  have hzM : center (Theory.PSL2.Group E) = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro y hy
    have hh := (centerCongr eD).symm ⟨y,hy⟩ |>.property
    have hh1 : eD.symm y = 1 := mem_bot.mp (hzD ▸ hh)
    exact eD.symm.injective (hh1.trans eD.symm.map_one.symm)
  have hb := MulAut.centralizer_conj_card_dvd hzM (eD x)
  rw [Theory.PSL2.binary_involution_centralizer_card (eD x) ((eD.orderOf_eq x).trans hx),
    hE,Theory.PSL2.outer_card_eq_field_degree E hE] at hb
  have hh := hd.trans hb
  interval_cases n <;> norm_num at *

/-- A centerless component with Sylow order sixty-four has central omega of order at most two. -/
theorem source_triple_centerless_sylow_omega_bound
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hzD : center D = ⊥) (h64 : ∀ P : Sylow 2 D, Nat.card P = 64) :
    ∃ P : Sylow 2 D, Nat.card (omegaCenterIn (P : Subgroup D)) ≤ 2 := by
  let C := ResidualFusion.C (tripleProduct d a)
  let W := ResidualFusion.W (tripleProduct d a)
  have hlocal := source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨S,M₁,hS,hSc,hM₁,h115,_,_⟩ := source_triple_component_catalogue
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal D hD.1
  let P₀ := (P : Subgroup D).map D.subtype
  have hPS : P₀ ≤ (S : Subgroup C) := by
    rintro _ ⟨x,hx,rfl⟩
    change x ∈ (S : Subgroup C).subgroupOf D
    rwa [←hP]
  have hPc : Nat.card P₀ = 64 := by rw [card_map_of_injective D.subtype_injective,h64]
  have hWc : Nat.card W = 2 := by
    change Nat.card (zpowers (ResidualFusion.point (tripleProduct d a))) = 2
    rw [Nat.card_zpowers,←orderOf_coe]
    exact hlocal.involution
  have hWS : W ≤ (S : Subgroup C) := by
    change ResidualFusion.W (tripleProduct d a) ≤ (S : Subgroup C)
    rw [←twoCore_eq_markedKernel (source_triple_twoCore_eq
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself)]
    exact pCore_isPGroup.le_sylow_of_normal S
  have hd : Disjoint P₀ W := by
    apply disjoint_iff.mpr
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hx.1
    have hyZ : y ∈ center D := mem_center_iff.mpr fun t =>
      Subtype.ext (mem_center_iff.mp (ResidualFusion.W_central _ hx.2) t)
    exact congrArg D.subtype (show y=1 from mem_bot.mp (hzD ▸ hyZ))
  have hOc : Nat.card (omegaCenterIn (S : Subgroup C)) = 4 := by
    rw [←card_map_of_injective C.subtype_injective,
      NilesRankOneKernel.omegaCenterIn_map_injective _ C.subtype_injective,hS,hlocal.omega_center]
    let := isKleinFour_closure_pair_of_orderOf z (tripleProduct d a)
      h115.involution hlocal.involution
      (fun hh => hlocal.nonfusion (hh ▸ IsConj.refl z))
      (mem_centralizer_singleton_iff.mp
        (hlocal.plane_centralizes (F.le_seed 1 (s.point.symm ▸ mem_zpowers z))))
    exact IsKleinFour.card_four
  have hb := omegaCenter_card_le_two_of_central_line (S : Subgroup C) W P₀
    hSc hWc hPc hWS hPS (ResidualFusion.W_central _) hd hOc
  refine ⟨P,?_⟩
  rw [←NilesRankOneKernel.omegaCenterIn_map_injective _ D.subtype_injective,
    card_map_of_injective D.subtype_injective] at hb
  exact hb

/-- The sixty-four-element elementary Sylow of PSL₂(64) contradicts the marked central omega. -/
theorem source_triple_not_binary_linear_six
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hDs : IsSimpleGroup D) : ¬ ClassicalGroup.IsPSL D 2 64 := by
  rintro ⟨E,hEfield,hEfinite,hE,⟨eD⟩⟩
  let := hD.2
  let := hDs
  let := hEfield
  let := hEfinite
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card (f := 6) hE
  have hp (P : Sylow 2 D) : IsElementaryAbelian 2 P ∧ Nat.card P = 64 := by
    let Q := P.mapSurjective (f := eD.toMonoidHom) eD.surjective
    let eP : P ≃* Q := eD.subgroupMap (P : Subgroup D)
    let := Theory.PSL2.OrdinaryBorel.sylow_elementary Q
    exact ⟨IsElementaryAbelian.of_surjective eP.symm.toMonoidHom eP.symm.surjective,
      (Nat.card_congr eP.toEquiv).trans ((Theory.PSL2.OrdinaryBorel.sylow_card Q).trans hE)⟩
  obtain ⟨P,hP⟩ := source_triple_centerless_sylow_omega_bound
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD
    center_eq_bot_of_simple_perfect (fun P => (hp P).2)
  let := (hp P).1
  have he : omegaCenterIn (P : Subgroup D) = P := by
    apply le_antisymm (fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).1)
    intro x hx
    apply (mem_omegaCenterIn_iff _ _).mpr
    exact ⟨hx,fun y hy => congrArg (fun t : P => (t : D))
      (mul_comm' (⟨y,hy⟩ : P) ⟨x,hx⟩),elemPow_eq_one_of_isElementaryAbelian x hx⟩
  rw [he,(hp P).2] at hP
  omega

/-- The four-element central root group of a PSL₃(4) Sylow contradicts the original omega-center. -/
theorem source_triple_not_linearThreeFour
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hDs : IsSimpleGroup D) : ¬ ClassicalGroup.IsPSL D 3 4 := by
  rintro ⟨E,hEfield,hEfinite,hE,⟨eD⟩⟩
  let := hD.2
  let := hDs
  let := hEfield
  let := hEfinite
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card (f := 2) hE
  let model (P : Sylow 2 D) : Matrix.PSL3Even.UnipotentGeometry.U E ≃* P :=
    let Q := P.mapSurjective (f := eD.toMonoidHom) eD.surjective
    let eP : P ≃* Q := eD.subgroupMap (P : Subgroup D)
    ((Matrix.PSL3.LinearThree.unipotentEquiv E).trans
      (Sylow.equiv (Matrix.PSL3.LinearThree.unipotentSylow E (by decide : 0 < 2) hE) Q)).trans eP.symm
  have hp64 (P : Sylow 2 D) : Nat.card P = 64 := by
    rw [←Nat.card_congr (model P).toEquiv,Matrix.PSL3Even.UnipotentGeometry.card_U,hE]
    norm_num
  obtain ⟨P,hP⟩ := source_triple_centerless_sylow_omega_bound
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD
    center_eq_bot_of_simple_perfect hp64
  let Z := Matrix.PSL3Even.UnipotentGeometry.Z E
  let i : Z →* D := (P : Subgroup D).subtype.comp ((model P).toMonoidHom.comp Z.subtype)
  have hi : Function.Injective i := (P : Subgroup D).subtype_injective.comp
    ((model P).injective.comp Z.subtype_injective)
  have himem (x : Z) : i x ∈ omegaCenterIn (P : Subgroup D) := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨((model P) x).property,?_,?_⟩
    · intro y hy
      have hxZ : (x : Matrix.PSL3Even.UnipotentGeometry.U E) ∈ center _ :=
        (Matrix.PSL3Even.UnipotentGeometry.Z_eq_center E) ▸ x.property
      have hZ := (centerCongr (model P) ⟨x,hxZ⟩).property
      exact congrArg (P : Subgroup D).subtype (mem_center_iff.mp hZ ⟨y,hy⟩)
    · have hx2 : x^2=1 := Subtype.ext
        (Matrix.PSL3Even.UnipotentGeometry.Z_exponent_two E x x.property)
      exact (map_pow i x 2).symm.trans ((congrArg i hx2).trans (map_one i))
  let j := i.codRestrict (omegaCenterIn (P : Subgroup D)) himem
  have hj : Function.Injective j := fun x y hh => hi (congrArg (fun t : omegaCenterIn (P : Subgroup D) => (t : D)) hh)
  have hc := Nat.card_le_card_of_injective j hj
  have hZc : Nat.card Z = 4 := (Matrix.PSL3Even.UnipotentGeometry.card_Z E).trans hE
  rw [hZc] at hc
  omega

/-- The eight-element root center of Sz(8) contradicts the same marked omega-center. -/
theorem source_triple_not_suzukiEight
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hDs : IsSimpleGroup D) :
    ¬ Nonempty (D ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) := by
  rintro ⟨eD⟩
  let := hD.2
  let := hDs
  let R := BenderSuzuki.MatrixGroups.SuzukiRootSubgroup 1
  obtain ⟨Q₀,hQ₀⟩ := BenderSuzuki.MatrixGroups.suzukiRootSubgroup_isSylow 1 (by decide)
  let model (P : Sylow 2 D) : R ≃* P :=
    let Q := P.mapSurjective (f := eD.toMonoidHom) eD.surjective
    let eP : P ≃* Q := eD.subgroupMap (P : Subgroup D)
    ((MulEquiv.subgroupCongr hQ₀.symm).trans (Sylow.equiv Q₀ Q)).trans eP.symm
  have hp64 (P : Sylow 2 D) : Nat.card P = 64 := by
    rw [←Nat.card_congr (model P).toEquiv]
    exact BenderSuzuki.MatrixGroups.suzukiRootSubgroup_card 1 (by decide)
  obtain ⟨P,hP⟩ := source_triple_centerless_sylow_omega_bound
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD
    center_eq_bot_of_simple_perfect hp64
  let Z := center R
  let i : Z →* D := (P : Subgroup D).subtype.comp ((model P).toMonoidHom.comp Z.subtype)
  have hi : Function.Injective i := (P : Subgroup D).subtype_injective.comp
    ((model P).injective.comp Z.subtype_injective)
  have himem (x : Z) : i x ∈ omegaCenterIn (P : Subgroup D) := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨((model P) x).property,?_,?_⟩
    · intro y hy
      have hZ := (centerCongr (model P) x).property
      exact congrArg (P : Subgroup D).subtype (mem_center_iff.mp hZ ⟨y,hy⟩)
    · have hx2 : x^2=1 := Subtype.ext
        ((BenderSuzuki.MatrixGroups.suzukiRootSubgroup_square_iff_center 1 (by decide) x).mpr x.property)
      exact (map_pow i x 2).symm.trans ((congrArg i hx2).trans (map_one i))
  let j := i.codRestrict (omegaCenterIn (P : Subgroup D)) himem
  have hj : Function.Injective j := fun x y hh => hi (congrArg (fun t : omegaCenterIn (P : Subgroup D) => (t : D)) hh)
  have hc := Nat.card_le_card_of_injective j hj
  have hZc : Nat.card Z = 8 := BenderSuzuki.MatrixGroups.suzukiRootSubgroup_center_card 1 (by decide)
  rw [hZc] at hc
  omega

/-- The characteristic-two rows surviving the original Sylow central omega and action. -/
@[expose] def OmegaLieModels (X : Type*) [Group X] : Prop :=
  (∃ f : ℕ, (f = 2 ∨ f = 3) ∧ ClassicalGroup.IsPSL X 2 (2^f)) ∨
  ClassicalGroup.IsPSL X 3 2 ∨ Nonempty (X ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (X ≃* commutator (Atlas.G2.Model (ZMod 2)))

/-- Remaining genuine component models; the L₃(4) central cover remains explicit. -/
inductive OmegaModels (X : Type*) [Group X] : Prop
  | lie (simple : IsSimpleGroup X) (model : OmegaLieModels X)
  | two_cover (nontrivial_center : center X ≠ ⊥) (center_eq : center X = pCore 2 X)
      (model : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 3 4)
  | odd (model : ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL X 2 p)

/-- Apply the faithful quotient action and central-omega exclusions to the literal component.
The original automorphism, fixed Sylow and fixed-residual bound all survive. -/
theorem source_triple_omega_marked_component
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let C := ResidualFusion.C (tripleProduct d a)
    ∃ (D : Subgroup C) (α : MulAut D) (P : Sylow 2 D),
      IsComponent C D ∧
      (∀ x : D, ((α x : C) : G) = z * (x : G) * z⁻¹) ∧
      OmegaModels D ∧ α ∈ (MulAut.conj (G := D)).range ∧ orderOf α = 2 ∧
      Nat.card P ∣ 128 ∧ (∀ x : P, α (x : D) = x) ∧
      Nat.card α.fixedSubgroup ∣ 384 ∧ Nat.card (pResidual 2 α.fixedSubgroup) ∣ 48 ∧
      ¬128 ∣ Nat.card (D ⧸ pCore 2 D) := by
  intro C
  obtain ⟨D,α,P,hD,hα,hm,hi,ho,hP,hfix,hfc,hrc,hsmall⟩ := source_triple_residual_marked_component
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hmodels : OmegaModels D := by
    cases hm with
    | lie hsimple hm =>
      apply OmegaModels.lie hsimple
      rcases hm with hlin | hsuz | hl2 | hl4 | halt | hg2
      · obtain ⟨n,hn,hn6,hm⟩ := hlin
        left
        refine ⟨n,?_,hm⟩
        by_cases h4 : 4 ≤ n
        · have hn6 := source_triple_binary_linear_large_parameter
            hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hsimple hα hi ho h4 hn6 hm
          subst n
          exact (source_triple_not_binary_linear_six
            hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hsimple hm).elim
        · omega
      · exact (source_triple_not_suzukiEight
          hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hsimple hsuz).elim
      · exact Or.inr (Or.inl hl2)
      · exact (source_triple_not_linearThreeFour
          hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hsimple hl4).elim
      · exact Or.inr (Or.inr (Or.inl halt))
      · exact Or.inr (Or.inr (Or.inr hg2))
    | two_cover hn hz hm => exact .two_cover hn hz hm
    | odd hm =>
      rcases hm with hm | hm
      · exact (source_triple_not_linearThreeThree
          hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hα hi ho hm).elim
      · exact .odd hm
    | mathieuEleven hm =>
      exact (source_triple_not_mathieuEleven
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hα hi ho hm).elim
  exact ⟨D,α,P,hD,hα,hmodels,hi,ho,hP,hfix,hfc,hrc,hsmall⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
