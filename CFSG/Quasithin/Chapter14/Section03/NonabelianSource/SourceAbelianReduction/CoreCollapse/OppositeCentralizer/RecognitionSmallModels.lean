module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionComponentAction
public import Theory.GroupTheory.GeneralizedFitting.IndexTwoOrbitNormality
public import Theory.SpecificGroups.AlternatingSix.CubicAbsorption
public import Theory.SpecificGroups.PSL2.AdjacentPowerOddCore
public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import Theory.SpecificGroups.PSL2.CubicNormalizerCongruence
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.SL2.ThreeResidualCore
public import GorensteinWalter.LinearThreeEquiv

/-!
# Small and odd-parameter component exclusions

The quotient order and the two-component orbit bound force normality of the
small centerless components with Sylow order at least eight. The resulting
faithful quotient action excludes PSL₂(8), PSL₃(2), and A₆. For odd parameters,
the centralizer of the original involution action reduces the Fermat--Mersenne
list to A₅. Finally, the literal SL₂(3) subgroup contains the original z and
is two-perfect. It normalizes every component, so its nontrivial z-action
cannot have a two-group automorphism centralizer. This excludes A₅ even when
the component is not normal. The intermediate catalogue retains the original
component, z-action, and Sylow marking for the remaining cover and G₂ cases.

Source: Aschbacher--Smith 14.3.22, printed p.999; refs/quasithin.pdf.
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


/-- The original quotient acts faithfully on this actual component by its original conjugation. -/
theorem source_triple_normal_component_action
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    [D.Normal] (hzD : center D = ⊥) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2) :
    let C := ResidualFusion.C (tripleProduct d a)
    let W := ResidualFusion.W (tripleProduct d a)
    ∃ ρ : (C ⧸ W) →* MulAut D, Function.Injective ρ ∧
      ∀ (c : C) (x : D), ((ρ (QuotientGroup.mk' W c) x : C) : G) =
        (c : G) * (x : G) * (c : G)⁻¹ := by
  intro C W
  have hL := source_triple_layer_eq_of_normal_inner
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD hα hi ho
  have hker : (MulAut.conjNormal : C →* MulAut D).ker = W := by
    rw [MulAut.conjNormal_ker_eq_centralizer,←hL]
    exact source_triple_layer_centralizer_eq
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  let ρ := QuotientGroup.lift W (MulAut.conjNormal : C →* MulAut D) hker.symm.le
  exact ⟨ρ,(QuotientGroup.injective_lift_iff _ _ _).mpr hker.symm,fun c x => rfl⟩


/-- The faithful action forces a factor sixty-four in the full component automorphism group. -/
theorem source_triple_normal_component_automorphism_bound
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    [D.Normal] (hzD : center D = ⊥) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2) :
    64 ∣ Nat.card (MulAut D) := by
  obtain ⟨ρ,hρ,_⟩ := source_triple_normal_component_action
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD hα hi ho
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


/-- The original point centralizer embeds in the centralizer of the same component action. -/
theorem source_triple_normal_component_action_centralizer_bound
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    [D.Normal] (hzD : center D = ⊥) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2) :
    192 ∣ Nat.card (centralizer ({α} : Set (MulAut D))) := by
  let C := ResidualFusion.C (tripleProduct d a)
  let W := ResidualFusion.W (tripleProduct d a)
  let q := QuotientGroup.mk' W
  have hlocal := source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  let zC : C := ⟨z,hlocal.plane_centralizes (F.le_seed 1 (s.point.symm ▸ mem_zpowers z))⟩
  obtain ⟨ρ,hρ,hact⟩ := source_triple_normal_component_action
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD hα hi ho
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


/-- The three-rank bound makes an A₆ component normal; its automorphism
order then contradicts the original quotient Sylow order. -/
theorem source_triple_not_inner_alternatingSix
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2) :
    ¬ Nonempty (D ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨eD⟩
  let := hD.2
  have hw := (source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).involution
  have hr : primeRank 3 (ResidualFusion.C (tripleProduct d a)) ≤ 2 :=
    (hG.twoLocal_sqtk (isTwoLocal_involution_centralizer hw)).stronglyQuasithin
      3 Nat.prime_three (by decide)
  let := AlternatingSix.ShadowLocal.component_normal_of_three_rank D hD eD hr
  have hzD : center D = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hh : eD x ∈ center (alternatingGroup (Fin 6)) := (centerCongr eD ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact eD.map_eq_one_iff.mp hh
  have hd := source_triple_normal_component_automorphism_bound
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD
    hzD hα hi ho
  rw [Nat.card_congr (MulAut.congr eD).toEquiv,AlternatingSix.ShadowLocal.card_aut] at hd
  norm_num at hd

/-- The larger prime-parameter rows have a large dihedral two-centralizer.
Their normal component action cannot contain the actual order-192 point centralizer. -/
theorem source_triple_odd_parameter_le_nine
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hm : ClassicalGroup.IsPSL D 2 p) : p ≤ 9 := by
  by_contra! hl
  obtain ⟨E,hEfield,hEfinite,hE,⟨eD⟩⟩ := hm
  let := hD.2
  let := hEfield
  let := hEfinite
  let : Fact p.Prime := ⟨hp.1⟩
  have hpodd : Odd p := hp.1.odd_of_ne_two (by omega)
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card E) :=
    ⟨p,1,hp.1,hpodd,by decide,by simpa using hE⟩
  have hzD : center D = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hh : eD x ∈ center (Theory.PSL2.Group E) := (centerCongr eD ⟨x,hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot,mem_bot] at hh
    exact eD.map_eq_one_iff.mp hh
  obtain ⟨x,hx,he,_⟩ := MulAut.inner_involution_representative hzD α ho
    (by obtain ⟨x,hx⟩ := hi; exact ⟨x,hx.symm⟩)
  have hxM : orderOf (eD x) = 2 := (eD.orderOf_eq x).trans hx
  have hpower : ∃ k : ℕ, p-1=2^k ∨ p+1=2^k := by
    rcases hp.2 with ⟨k,hk⟩ | ⟨k,hk⟩
    · exact ⟨2^k,Or.inl (by omega)⟩
    · exact ⟨k,Or.inr hk⟩
  obtain ⟨k,hk⟩ := hpower
  let X := centralizer ({eD x} : Set (Theory.PSL2.Group E))
  have hX : IsPGroup 2 X := Theory.PSL2.involutionCentralizer_isTwoGroup_of_adjacent_power
    hodd (by omega) (by simpa only [hE] using hk) (eD x) hxM
  obtain ⟨m,hm⟩ := hX.exists_card_eq
  have hmlarge : 4 ≤ m := by
    have hh := Theory.PSL2.involution_centralizer_card_cases hodd (eD x)
      (orderOf_eq_prime_iff.mp hxM).symm
    change Nat.card X = _ ∨ Nat.card X = _ at hh
    rw [hm,hE] at hh
    by_contra! hsmall
    interval_cases m <;> norm_num at hh <;> omega
  have h16 : 16 ∣ Nat.card D := by
    rw [Nat.card_congr eD.toEquiv]
    exact (show 2^4 ∣ Nat.card X from hm ▸ Nat.pow_dvd_pow 2 hmlarge).trans
      X.card_subgroup_dvd_card
  have hd := source_triple_centerless_component_action_centralizer_bound
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD h16 hα hi ho
  rw [he,MulAut.card_centralizer_conj_congr eD x] at hd
  have hb := MulAut.centralizer_conj_card_dvd
    (GorensteinWalter.psl2_center_eq_bot E) (eD x)
  have hout : Nat.card (MulAut.Outer (Theory.PSL2.Group E)) = 2 := by
    change Nat.card ((MulAut (Theory.PSL2.Group E)) ⧸ (MulAut.conj (G := Theory.PSL2.Group E)).range) = 2
    rw [←index_eq_card]
    exact Theory.PSL2.prime_card_inner_index E hpodd (by omega) hE
  change _ ∣ Nat.card X * _ at hb
  rw [hm,hout,←Nat.pow_succ] at hb
  have h3 : 3 ∣ 2^(m+1) := (by decide : 3 ∣ 192).trans (hd.trans hb)
  exact (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h3)

/-- An eight-divisible centerless component is normal in the original centralizer:
its two-conjugate alternative would already exceed the quotient Sylow order. -/
theorem source_triple_centerless_component_normal_eight
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hzD : center D = ⊥) (h8 : 8 ∣ Nat.card D) : D.Normal := by
  let C := ResidualFusion.C (tripleProduct d a)
  let W := ResidualFusion.W (tripleProduct d a)
  let q := QuotientGroup.mk' W
  have hw := (source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).involution
  have hcore := source_triple_twoCore_eq
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hZ := (source_triple_component_center
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD).2.1
  have hi : Function.Injective (q.comp D.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [component_quotient_kernel hcore hD,←hZ,hzD]
  obtain ⟨S,M₁,hS,hSc,_⟩ := source_triple_component_catalogue
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  exact hD.normal_of_injective_image_twice_square_not_dvd hzD
    (hG.twoLocal_sqtk (isTwoLocal_involution_centralizer hw)).stronglyQuasithin
    q (QuotientGroup.mk'_surjective _) hi h8
    (by simpa using quotient_not_128_dvd hw hcore S hSc)

/-- The full PSL₂(8) automorphism group has insufficient two-part. -/
theorem source_triple_not_binary_linear_three
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hDs : IsSimpleGroup D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2) :
    ¬ ClassicalGroup.IsPSL D 2 (2^3) := by
  rintro ⟨E,hEfield,hEfinite,hE,⟨eD⟩⟩
  let := hD.2
  let := hDs
  let := hEfield
  let := hEfinite
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hE
  have hzD : center D = ⊥ := center_eq_bot_of_simple_perfect
  have h8 : 8 ∣ Nat.card D := by
    have hd := (BenderSuzuki.Converse.PUnip E).card_subgroup_dvd_card
    rwa [BenderSuzuki.Converse.PUnip_card,hE,←Nat.card_congr eD.toEquiv] at hd
  let := source_triple_centerless_component_normal_eight
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD h8
  have hd := source_triple_normal_component_automorphism_bound
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD hα hi ho
  rw [Nat.card_congr (MulAut.congr eD).toEquiv] at hd
  have hh := hd.trans (Theory.PSL2.BinaryAutomorphismOrder.aut_card_dvd hE)
  norm_num at hh

/-- The binary three-dimensional model also has insufficient automorphism two-part. -/
theorem source_triple_not_linearThreeTwo
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    (hDs : IsSimpleGroup D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2) :
    ¬ ClassicalGroup.IsPSL D 3 2 := by
  rintro ⟨E,hEfield,hEfinite,hE,⟨eD⟩⟩
  let := hD.2
  let := hDs
  let := hEfield
  let := hEfinite
  let := Fintype.ofFinite E
  let aE : E ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hE)
  let eM := eD.trans (Atlas.fieldEquivPSL 3 aE)
  have hzD : center D = ⊥ := center_eq_bot_of_simple_perfect
  have h8 : 8 ∣ Nat.card D := by
    rw [Nat.card_congr eM.toEquiv,←Nat.card_congr Matrix.PSL3Two.equiv.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  let := source_triple_centerless_component_normal_eight
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD h8
  have hd := source_triple_normal_component_automorphism_bound
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hzD hα hi ho
  rw [Nat.card_congr (MulAut.congr eM).toEquiv,Matrix.PSL3Two.Automorphisms.card_aut] at hd
  norm_num at hd

/-- The prime-parameter alternative is exactly the remaining A₅ model. -/
theorem source_triple_odd_model_is_alternatingFive
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2)
    (hm : ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL D 2 p) :
    Nonempty (D ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨p,hp,hm⟩ := hm
  have hsmall := source_triple_odd_parameter_le_nine
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hα hi ho hp hm
  have hcases : p=2 ∨ p=3 ∨ p=5 ∨ p=7 := by
    have hprime := hp.1
    interval_cases p <;> first | omega | norm_num at hprime
  obtain ⟨E,hEfield,hEfinite,hE,⟨eD⟩⟩ := hm
  let := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  let := hEfield
  let := hEfinite
  let := Fintype.ofFinite E
  rcases hcases with rfl | rfl | rfl | rfl
  · let := Theory.PSL2.OuterSolvable.isSolvable_of_card_two hE
    exact (Group.IsPerfect.not_isSolvable D
      (Group.isSolvable_of_isSolvable_injective (f := eD.toMonoidHom) eD.injective)).elim
  · let aE : E ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hE)
    let eM := (eD.trans (Atlas.fieldEquivPSL 2 aE)).trans
      GorensteinWalter.psl2_three_equiv_alternatingGroup
    let := alternatingGroup_fin_four_isSolvable
    exact (Group.IsPerfect.not_isSolvable D
      (Group.isSolvable_of_isSolvable_injective (f := eM.toMonoidHom) eM.injective)).elim
  · let aE : E ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hE)
    exact ⟨(eD.trans (Atlas.fieldEquivPSL 2 aE)).trans
      Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some⟩
  · let : Fact (Nat.Prime 7) := ⟨by decide⟩
    let aE : E ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hE)
    let eM := (eD.trans (Atlas.fieldEquivPSL 2 aE)).trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two
    let := Atlas.Comparisons.Exceptional.psl3Two_simple
    let : IsSimpleGroup D := eM.isSimpleGroup
    have hm : ClassicalGroup.IsPSL D 3 2 := ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨eM⟩⟩
    exact (source_triple_not_linearThreeTwo
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD
      inferInstance hα hi ho hm).elim


/-- The literal SL₂(3) factor contains z, so the centralizer of the component
z-action cannot be a two-group. The argument uses the full two-component orbit bound. -/
theorem source_triple_component_action_centralizer_not_two
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (ho : orderOf α = 2) :
    ¬ IsPGroup 2 (centralizer ({α} : Set (MulAut D))) := by
  intro hp
  let C := ResidualFusion.C (tripleProduct d a)
  let N := normalizer (D : Set C)
  have hlocal := source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨B,_,⟨eB⟩,_,hinter,hgen⟩ := source_triple_residual_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  have hBC : B ≤ C := (hgen ▸ le_sup_right).trans inf_le_right
  have hBH : B ≤ F.H := ((hgen ▸ le_sup_right).trans inf_le_left).trans (map_subtype_le _)
  have hBperf : IsPPerfect 2 B := GLS3.Chapter5.SchurPresentation.sl23_twoPerfect.of_surjective
    eB.symm.toMonoidHom eB.symm.surjective
  have hBN : ∀ b : B, inclusion hBC b ∈ N := by
    rcases hD.normal_or_index_two_of_odd_rank_le_two
      (hG.twoLocal_sqtk (isTwoLocal_involution_centralizer hlocal.involution)).stronglyQuasithin with hn | hi
    · let := hn
      intro b
      change inclusion hBC b ∈ normalizer (D : Set C)
      rw [normalizer_eq_top]
      trivial
    · let : N.Normal := normal_of_index_eq_two hi
      have hN : IsPGroup 2 (C ⧸ N) := IsPGroup.of_card (n := 1) (by
        simpa only [index_eq_card,pow_one] using hi)
      let f := (QuotientGroup.mk' N).comp (inclusion hBC)
      have hf := hBperf.hom_eq_one_of_isPGroup hN f
      intro b
      exact (QuotientGroup.eq_one_iff _).mp (DFunLike.congr_fun hf b)
  let j : B →* N := (inclusion hBC).codRestrict N hBN
  let ρ := D.normalizerMonoidHom.comp j
  have hact (b : B) (x : D) : ((ρ b x : C) : G) = (b : G) * (x : G) * (b : G)⁻¹ := rfl
  have hcomm (b : B) : ρ b ∈ centralizer ({α} : Set (MulAut D)) := by
    apply mem_centralizer_singleton_iff.mpr
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change ((ρ b (α x) : C) : G) = ((α (ρ b x) : C) : G)
    rw [hact,hα,hα,hact]
    have hbz : Commute (b : G) z := by
      apply mem_centralizer_singleton_iff.mp
      rw [←F.H_eq_centralizer (by decide) z s.point]
      exact hBH b.property
    calc
      (b : G) * (z * (x : G) * z⁻¹) * (b : G)⁻¹ =
          ((b : G)*z) * (x : G) * ((b : G)*z)⁻¹ := by group
      _ = (z*(b : G)) * (x : G) * (z*(b : G))⁻¹ := by rw [hbz.eq]
      _ = z * ((b : G) * (x : G) * (b : G)⁻¹) * z⁻¹ := by group
  let ψ := ρ.codRestrict _ hcomm
  have hψ := hBperf.hom_eq_one_of_isPGroup hp ψ
  have hzB : z ∈ B := by
    have hz : z ∈ F.Vi 1 := s.point.symm ▸ mem_zpowers z
    rw [←hinter] at hz
    exact hz.2
  let zB : B := ⟨z,hzB⟩
  have he : ρ zB = α := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact (hact zB x).trans (hα x).symm
  have hα1 : α = 1 := he.symm.trans
    (congrArg (fun y : centralizer ({α} : Set (MulAut D)) => (y : MulAut D))
      (DFunLike.congr_fun hψ zB))
  rw [hα1,orderOf_one] at ho
  contradiction

/-- A₅ has two-group centralizer for its inner involutions and is excluded by
that literal SL₂(3) marking, including the possibility of two components. -/
theorem source_triple_not_alternatingFive
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D) {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := D)).range) (ho : orderOf α = 2) :
    ¬ Nonempty (D ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨eD⟩
  let E := GaloisField 2 2
  have hE : Nat.card E = 2^2 := GaloisField.card 2 2 (by decide)
  let eM := eD.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := E) hE).some.symm
  have hzD : center D = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hh : eD x ∈ center (alternatingGroup (Fin 5)) := (centerCongr eD ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact eD.map_eq_one_iff.mp hh
  obtain ⟨x,hx,he,_⟩ := MulAut.inner_involution_representative hzD α ho
    (by obtain ⟨x,hx⟩ := hi; exact ⟨x,hx.symm⟩)
  have hd : Nat.card (centralizer ({α} : Set (MulAut D))) ∣ 2^3 := by
    rw [he,MulAut.card_centralizer_conj_congr eM x]
    have hb := MulAut.centralizer_conj_card_dvd (GorensteinWalter.psl2_center_eq_bot E) (eM x)
    rw [Theory.PSL2.binary_involution_centralizer_card (eM x) ((eM.orderOf_eq x).trans hx),
      hE,Theory.PSL2.outer_card_eq_field_degree E hE] at hb
    exact hb
  exact source_triple_component_action_centralizer_not_two
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hα ho
    (IsPGroup.of_card_dvd_pow hd)

/-- The actual component is A₅, a nontrivial binary cover of L₃(4), or G₂(2)′.
All equivalences retain the original component and its original z-action. -/
inductive FinalThreeModels (X : Type*) [Group X] : Prop
  | five (model : Nonempty (X ≃* alternatingGroup (Fin 5)))
  | two_cover (nontrivial_center : center X ≠ ⊥) (center_eq : center X = pCore 2 X)
      (model : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 3 4)
  | g2 (model : Nonempty (X ≃* commutator (Atlas.G2.Model (ZMod 2))))

/-- Apply the small-model and odd-parameter exclusions to the original marked catalogue. -/
theorem source_triple_final_three_marked_component
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let C := ResidualFusion.C (tripleProduct d a)
    ∃ (D : Subgroup C) (α : MulAut D) (P : Sylow 2 D),
      IsComponent C D ∧
      (∀ x : D, ((α x : C) : G) = z * (x : G) * z⁻¹) ∧
      FinalThreeModels D ∧ α ∈ (MulAut.conj (G := D)).range ∧ orderOf α = 2 ∧
      Nat.card P ∣ 128 ∧ (∀ x : P, α (x : D) = x) ∧
      Nat.card α.fixedSubgroup ∣ 384 ∧ Nat.card (pResidual 2 α.fixedSubgroup) ∣ 48 ∧
      ¬128 ∣ Nat.card (D ⧸ pCore 2 D) := by
  intro C
  obtain ⟨D,α,P,hD,hα,hm,hi,ho,hP,hfix,hfc,hrc,hsmall⟩ := source_triple_omega_marked_component
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hmodels : FinalThreeModels D := by
    cases hm with
    | lie hsimple hm =>
      rcases hm with hlin | hl2 | halt | hg2
      · obtain ⟨n,hn,hm⟩ := hlin
        rcases hn with rfl | rfl
        · obtain ⟨E,hEfield,hEfinite,hE,⟨eD⟩⟩ := hm
          let := hEfield
          let := hEfinite
          exact .five ⟨eD.trans
            (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hE).some⟩
        · exact (source_triple_not_binary_linear_three
            hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD
            hsimple hα hi ho hm).elim
      · exact (source_triple_not_linearThreeTwo
          hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD
          hsimple hα hi ho hl2).elim
      · exact (source_triple_not_inner_alternatingSix
          hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hα hi ho halt).elim
      · exact .g2 hg2
    | two_cover hn hz hm => exact .two_cover hn hz hm
    | odd hm => exact .five (source_triple_odd_model_is_alternatingFive
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hα hi ho hm)
  exact ⟨D,α,P,hD,hα,hmodels,hi,ho,hP,hfix,hfc,hrc,hsmall⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
