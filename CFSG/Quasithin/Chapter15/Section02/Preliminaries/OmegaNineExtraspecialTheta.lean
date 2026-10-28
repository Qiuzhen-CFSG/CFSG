module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaNineExtraspecial
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PResidual.CubicClosureTwoKernel

/-!
# The exact theta identity in the extraspecial Omega branch

The kernel on Y* is Z(Y*), so the intrinsic central preimage O₂,Z(Y) is
C_Y(V). Every cubic in C_M(V)* lies in this center. Normality of Y in M
removes the possible two-group difference and places each original cubic
of C_M(V) in C_Y(V). Thus their theta closures agree. The map from C_Y(V)
to M/O₂(M) has two-group kernel and cubic image; prime-regular lifting
identifies its cubic closure with its two-residual.

This gives the literal identity O²(O₂,Z(Y)) = theta(C_M(V)) of
Aschbacher--Smith15.2.3(1)(ii), printed pp.1104--1105, with the original
Y, chosen module, quotient maps and central preimage.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem residual_notation (H : Subgroup G) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    exact ⟨hN, IsPGroup.of_card hn⟩
  · rintro ⟨hN, hp⟩
    exact ⟨hN, IsPGroup.iff_card.mp hp⟩

private theorem theta_eq_residual_of_cube_image {H : Type*} [Group H]
    (W : Subgroup G) (f : W →* H) (hk : IsPGroup 2 f.ker)
    (hcube : ∀ x : W, (f x) ^ 3 = 1) : theta W = twoResidualAmbient W := by
  rw [residual_notation, ← cubic_closure_eq_twoResidual_of_cube_image f hk hcube,
    MonoidHom.map_closure, theta]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, ho⟩
    exact ⟨⟨x, hx⟩, (orderOf_coe _).symm.trans ho, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, (orderOf_coe y).trans hy⟩

/-- The literal intrinsic central preimage is C_Y(V) in the extraspecial branch. -/
theorem source_omega_extraspecial_centralPreimage_eq (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 9)
    (hex : IsExtraspecial 3 (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (QuotientGroup.mk' (pCore 2 M)))) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    (centralPreimage (pCore 2 Y)).map Y.subtype = Y ⊓ centralizer (V : Set G) := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let P := (Y.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))
  let e := omegaResidualCoreQuotientEquivStar T (Mc := Mc) hTM hV.normalized ho
  have hecenter (z : Y ⧸ pCore 2 Y) : z ∈ center (Y ⧸ pCore 2 Y) ↔ e z ∈ center P := by
    constructor
    · intro hz
      apply mem_center_iff.mpr
      intro u
      obtain ⟨v, rfl⟩ := e.surjective u
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hz v)
    · intro hz
      apply mem_center_iff.mpr
      intro u
      apply e.injective
      simpa only [map_mul] using mem_center_iff.mp hz (e u)
  have hy (y : Y) : y ∈ centralPreimage (pCore 2 Y) ↔
      (y : G) ∈ centralizer (V : Set G) := by
    change QuotientGroup.mk' (pCore 2 Y) y ∈ center (Y ⧸ pCore 2 Y) ↔ _
    rw [hecenter, ← source_omega_extraspecial_star_kernel T hTM hu hV ho hcard hex]
    change omegaStarActor hV.normalized ho
      ((e (QuotientGroup.mk' (pCore 2 Y) y)) : M ⧸ pCore 2 M) = 1 ↔ _
    rw [omegaResidualCoreQuotientEquivStar_apply_mk]
    change (actionHom M V hV.normalized).rangeRestrict
      (Subgroup.inclusion (source_omega_caseIIResidual_le T hTM hV.normalized ho) y) = 1 ↔ _
    rw [← MonoidHom.mem_ker, MonoidHom.ker_rangeRestrict, actionHom_ker]
    rfl
  ext x
  constructor
  · rintro ⟨y, hy', rfl⟩
    exact ⟨y.property, (hy y).mp hy'⟩
  · rintro ⟨hxY, hxC⟩
    exact ⟨⟨x, hxY⟩, (hy ⟨x, hxY⟩).mpr hxC, rfl⟩

/-- Every original cubic of C_M(V) belongs to the original residual Y. -/
theorem source_omega_extraspecial_cubic_mem_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 9)
    (he : Nonempty ((((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (QuotientGroup.mk' (pCore 2 M))) ≃* HeisenbergPrime 3))
    (x : G) (hx : x ∈ M ⊓ centralizer (V : Set G)) (hx3 : x ^ 3 = 1) :
    x ∈ caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc := by
  let N := (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M
  let : N.Normal := source_omega_lemma_15_2_3_2 T hM.2 hV.normalized ho
  let Q := pCore 2 M
  let q := QuotientGroup.mk' Q
  let π := QuotientGroup.mk' N
  let a : M := ⟨x, hx.1⟩
  have ha3 : a ^ 3 = 1 := Subtype.ext hx3
  have hqa : q a ∈ (omegaStarActor hV.normalized ho).ker := by
    rw [omegaStarActor_ker]
    exact mem_map_of_mem q hx
  have hs : q a ∈ N.map q := map_subtype_le _
    (source_omega_extraspecial_star_cubic_mem_center hG T hM hu hV ho hcard he
      (q a) hqa (by rw [← map_pow, ha3, map_one]))
  have ha : a ∈ N ⊔ Q := by
    have hm : a ∈ (N.map q).comap q := hs
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk'] using hm
  have hb : π a ∈ Q.map π := by
    have hm := mem_map_of_mem π ha
    simpa only [Subgroup.map_sup, π, QuotientGroup.map_mk'_self, bot_sup_eq] using hm
  let b : Q.map π := ⟨π a, hb⟩
  have hb3 : b ^ 3 = 1 := Subtype.ext (by
    change π a ^ 3 = 1
    rw [← map_pow, ha3, map_one])
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := M)).map π b
  have hb1 : b = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 2 3).pow_left k)
      (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hb3))
  exact (QuotientGroup.eq_one_iff a).mp (congrArg Subtype.val hb1)

/-- The exact theta identity in original15.2.3(1)(ii). -/
theorem source_omega_extraspecial_theta
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 9)
    (he : Nonempty ((((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (QuotientGroup.mk' (pCore 2 M))) ≃* HeisenbergPrime 3)) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    twoResidualAmbient ((centralPreimage (pCore 2 Y)).map Y.subtype) =
      theta (M ⊓ centralizer (V : Set G)) := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let P := (Y.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))
  let W := Y ⊓ centralizer (V : Set G)
  let C := M ⊓ centralizer (V : Set G)
  let q := QuotientGroup.mk' (pCore 2 M)
  have hYM : Y ≤ M := source_omega_caseIIResidual_le T hM.2 hV.normalized ho
  have hWM : W ≤ M := inf_le_left.trans hYM
  let i : W →* M := Subgroup.inclusion hWM
  let f : W →* (M ⧸ pCore 2 M) := q.comp i
  obtain ⟨e⟩ := he
  let : IsExtraspecial 3 P := IsExtraspecial.of_mulEquiv e.symm
    (HeisenbergPrime.isExtraspecial (by decide))
  have htheta : theta C = theta W := by
    apply le_antisymm _ (theta_mono (inf_le_inf_right _ hYM))
    apply (closure_le _).mpr
    rintro x ⟨hx, ho3⟩
    apply Subgroup.subset_closure
    exact ⟨⟨source_omega_extraspecial_cubic_mem_residual hG T hM hu hV ho hcard ⟨e⟩
      x hx (ho3 ▸ pow_orderOf_eq_one x), hx.2⟩, ho3⟩
  have hker : IsPGroup 2 f.ker := by
    rw [show f = q.comp i from rfl, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective i (Subgroup.inclusion_injective hWM)
  have hcube (w : W) : (f w) ^ 3 = 1 := by
    have hwP : f w ∈ P := mem_map_of_mem q w.property.1
    let z : P := ⟨f w, hwP⟩
    have hzker : z ∈ ((omegaStarActor hV.normalized ho).domRestrict P).ker := by
      change (actionHom M V hV.normalized).rangeRestrict (i w) = 1
      apply Subtype.ext
      change i w ∈ (actionHom M V hV.normalized).ker
      rw [actionHom_ker]
      exact w.property.2
    have hzZ : z ∈ center P := by
      rwa [source_omega_extraspecial_star_kernel T hM.2 hu hV ho hcard inferInstance] at hzker
    have hpow : (⟨z, hzZ⟩ : center P) ^ 3 = 1 :=
      (IsExtraspecial.center_order_p 3 P) ▸ pow_card_eq_one' (x := (⟨z, hzZ⟩ : center P))
    exact congrArg (fun u : center P => ((u : P) : M ⧸ pCore 2 M)) hpow
  change twoResidualAmbient ((centralPreimage (pCore 2 Y)).map Y.subtype) = theta C
  rw [source_omega_extraspecial_centralPreimage_eq T hM.2 hu hV ho hcard inferInstance]
  exact (theta_eq_residual_of_cube_image W f hker hcube).symm.trans htheta.symm

end CFSG.Quasithin.Chapter15.Section02
