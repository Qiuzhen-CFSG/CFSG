module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaNineExtraspecial
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaNineActor
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.Sylow
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.Centralizer
public import Theory.GroupAction.Extraspecial27ElementaryActor

/-!
# The core involution in the extraspecial Omega branch

The original Rc* acts faithfully on Y*: a kernel element induces a
square-one element centralizing the full A₃×A₃ actor residual, so its
actor image is trivial, and faithfulness of Rc* on V kills it. Rc* is
elementary abelian, inherited from the actual Sylow actor of order four.
It fixes Z(Y*) by source15.2.3(5). The extraspecial order27 actor bound
therefore makes |Rc*| at most two. The previously constructed inverter
makes its order exactly two and determines the action of every nonidentity
member of the original Rc image.

Source: Aschbacher--Smith15.2.3(1)(ii), printed p.1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem sylow_le_partner (T : Sylow 2 G) {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    (T : Subgroup G) ≤ Mc := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  intro t ht
  exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)

private theorem eq_of_ne_one_of_card_two {H : Type*} [Group H]
    (hc : Nat.card H = 2) (x y : H) (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  let e : H ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hc (by simp)
  apply e.injective
  have he : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by decide
  exact he (e x) (e y) (fun h => hx (e.injective (h.trans e.map_one.symm)))
    (fun h => hy (e.injective (h.trans e.map_one.symm)))

/-- In the extraspecial branch the actual Rc image has order two and inverts Y-bar. -/
theorem source_omega_extraspecial_core_inversion (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 9)
    (hstar : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (QuotientGroup.mk' (pCore 2 M))) = 27)
    (hex : IsExtraspecial 3 (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (QuotientGroup.mk' (pCore 2 M)))) :
    let f := (actionHom M V hV.normalized).rangeRestrict
    let Rbar := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f
    let Ybar := ((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map f
    Nat.card Rbar = 2 ∧ ∀ r ∈ Rbar, r ≠ 1 → ∀ y ∈ Ybar, r * y * r⁻¹ = y⁻¹ := by
  let Y := (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let P := Y.map q
  let R := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map q
  let f := (actionHom M V hV.normalized).rangeRestrict
  let g := omegaStarActor hV.normalized ho
  let Rbar := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f
  let S := (T.subtype hTM).mapSurjective (actionHom M V hV.normalized).rangeRestrict_surjective
  let : Y.Normal := source_omega_lemma_15_2_3_2 T hTM hV.normalized ho
  let : P.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsExtraspecial 3 P := hex
  have hTMc := sylow_le_partner T hu
  have hRT : (M ⊓ Mc).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf hTM hTMc))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le (le_inf hTM hTMc)] using hh
  have hRS : R.map g ≤ (S : Subgroup (actionHom M V hV.normalized).range) := by
    rw [omegaStarActor_map]
    exact map_mono (comap_mono hRT)
  have hd : Disjoint R g.ker := source_omega_nine_rc_star_disjoint_kernel T hTM hu hV ho hcard
  have hi : Function.Injective (g.domRestrict R) := by
    apply (injective_iff_map_eq_one _).mpr
    intro r hr
    exact Subtype.ext (disjoint_def.mp hd r.property hr)
  let j : R →* S := (g.domRestrict R).codRestrict (S : Subgroup _) (fun r => hRS (mem_map_of_mem g r.property))
  have hj : Function.Injective j := fun a b h => hi (congrArg Subtype.val h)
  let : IsElementaryAbelian 2 S :=
    (SymmetricThreeProductResidual.sylow_elementary_four ho.2.2.2.1.some S).1
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.of_injective j hj
  let action := (MulAut.conjNormal : (M ⧸ pCore 2 M) →* MulAut P).domRestrict R
  have ha : Function.Injective action := by
    apply (injective_iff_map_eq_one action).mpr
    intro r hr
    have hr2 : (r : M ⧸ pCore 2 M) ^ 2 = 1 :=
      congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 R) r)
    have hf2 : (g r) ^ 2 = 1 := by rw [← map_pow, hr2, map_one]
    have hc : ∀ y ∈ pResidual 2 (actionHom M V hV.normalized).range,
        g r * y = y * g r := by
      intro y hy
      rw [← source_omega_nine_image_eq T hTM hV.normalized ho hcard] at hy
      obtain ⟨u, huY, rfl⟩ := hy
      let z : P := ⟨q u, mem_map_of_mem q huY⟩
      have hz : (r : M ⧸ pCore 2 M) * q u * (r : M ⧸ pCore 2 M)⁻¹ = q u :=
        congrArg Subtype.val (congrArg (fun a : MulAut P => a z) hr)
      have hh := congrArg g (mul_inv_eq_iff_eq_mul.mp hz)
      have hgq : g (q u) = f u := rfl
      simpa only [map_mul, hgq] using hh
    have hgr := SymmetricThreeProductResidual.eq_one_of_square_of_centralizes_residual
      ho.2.2.2.1.some (g r) hf2 hc
    exact hi (hgr.trans (map_one (g.domRestrict R)).symm)
  have hfix : ∀ r : R, ∀ z ∈ center P, action r z = z := by
    intro r z hz
    have hk : (z : M ⧸ pCore 2 M) ∈ g.ker := by
      change z ∈ (g.domRestrict P).ker
      rw [source_omega_extraspecial_star_kernel T hTM hu hV ho hcard hex]
      exact hz
    have hC : g.ker ≤ centralizer ((P ⊔ R : Subgroup (M ⧸ pCore 2 M)) : Set _) := by
      rw [omegaStarActor_ker]
      apply le_centralizer_iff.mpr
      rw [sup_comm]
      exact source_omega_lemma_15_2_3_5 T hTM hu hV ho
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp (hC hk) r ((show R ≤ P ⊔ R from le_sup_right) r.property))
  have hsmall : Nat.card R ≤ 2 :=
    MulAut.elementary_two_center_preserving_card_le_two hstar action ha hfix
  have hRsmall : Nat.card Rbar ≤ 2 := by
    have hh := Nat.card_le_card_of_surjective (g.subgroupMap R) (g.subgroupMap_surjective R)
    rw [omegaStarActor_map] at hh
    exact hh.trans hsmall
  obtain ⟨r, hr, hro, hinv⟩ := source_omega_nine_image_inverter T hTM hTMc hV.normalized ho hcard
  let rbar : Rbar := ⟨f r, mem_map_of_mem f hr⟩
  have hrc : orderOf rbar = 2 := (Subgroup.orderOf_coe rbar).symm.trans hro
  have hReq : Nat.card Rbar = 2 := le_antisymm hRsmall
    (Nat.le_of_dvd (Nat.card_pos (α := Rbar)) (hrc ▸ orderOf_dvd_natCard rbar))
  refine ⟨hReq, ?_⟩
  intro s hs hs1 y hy
  have hr1 : rbar ≠ 1 := by
    intro hh
    have h := congrArg orderOf hh
    rw [hrc, orderOf_one] at h
    omega
  have hh := eq_of_ne_one_of_card_two hReq (⟨s, hs⟩ : Rbar) rbar
    (fun he => hs1 (congrArg Subtype.val he)) hr1
  have he : s = f r := congrArg Subtype.val hh
  rw [he]
  exact hinv y hy

end CFSG.Quasithin.Chapter15.Section02
end
