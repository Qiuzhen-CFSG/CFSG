module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialPartnerPlane
public import Theory.GroupAction.FourAutomorphismOrbit
public import Theory.GroupTheory.TINormalizerControl

/-!
# Fusion of the literal extraspecial moved plane

The original central cubic acts transitively on the three nonidentity
points of U. Every point is therefore conjugate inside the actual partner
to a nonidentity original central seed point. Its full centralizer lies in
the partner. Consequently every transporter between nonidentity points
of U lies in the partner, and distinct conjugates of U intersect trivially.
No normalization of the larger Thompson fixed subgroup is assumed.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Section02.ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

set_option backward.isDefEq.respectTransparency false in
private theorem moved_normalizer_of_image
    (T : Sylow 2 G) {M V X : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (h : PreparedChosenModule T M V) (hXM : X ≤ M)
    (hn : (X.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict ≤
      normalizer (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V h.normalized).rangeRestrict : Set _)) :
    X ≤ normalizer (⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) := by
  let := h.elementary
  let ρ := imageRepresentation M V h.normalized
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
    (actionHom M V h.normalized).rangeRestrict
  let W := subspaceCommutator ρ ⊤ R
  have hs := subspaceCommutator_invariant_normalizer ρ
    (show (X.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict ≤
      subspaceStabilizer ρ ⊤ from le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hn
  have he := ambientSpace_moved h.normalized h.le_selected
    ((ChapterB.thompsonJ_le (T : Subgroup G) 1).trans hTM)
  change ambientSpace V W = _ at he
  rw [←he]
  apply le_normalizer_iff.mpr
  intro x hx v hv
  obtain ⟨v,hv,rfl⟩ := hv
  let a : M := ⟨x,hXM hx⟩
  have ha : (actionHom M V h.normalized).rangeRestrict a ∈
      (X.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict :=
    mem_map_of_mem _ hx
  have hh := (hs ha (Additive.ofMul v)).2 hv
  exact ⟨(ρ ((actionHom M V h.normalized).rangeRestrict a) (Additive.ofMul v)).toMul,
    hh,rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual partner is transitive on the nonidentity elements of the
original Thompson moved plane, using the original central cubic action. -/
theorem PreparedChosenModule.extraspecial_moved_transitive
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃ m ∈ Mc, m * (u : G) * m⁻¹ = v := by
  let := h.elementary
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  have hf : Function.Surjective f := (actionHom M V h.normalized).rangeRestrict_surjective
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let P := pResidual 2 D
  let ZP := (center P).map P.subtype
  have hUcard : Nat.card U = 4 :=
    (h.extraspecial_thompson_moved_seed_and_card hG T hempty hM hmany hJ hfull hex).2
  have hUV : U ≤ V := (h.extraspecial_thompson_moved_le_fixed
    hG T hempty hM hmany hJ hfull hex).trans inf_le_left
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUV
  have hMc := (h.extraspecial_partner_module_and_normalizer
    hG T hempty hM hmany hJ hu hfull hex).2
  have hn : Mc ≤ normalizer (U : Set G) := hMc.le
  let a := actionHom Mc U hn
  obtain ⟨t,ht,htR,hcod⟩ := h.extraspecial_small_thompson_image hG T hempty hM hmany hJ hfull hex
  change zpowers t = R at htR
  change fixedCodim ρ R = 2 at hcod
  obtain ⟨_,_,_,hP,hPc,_,h6,_⟩ := hex
  let : IsExtraspecial 3 P := hP
  have hZcard : Nat.card ZP = 3 := by
    rw [show ZP = (center P).map P.subtype from rfl,card_map_of_injective P.subtype_injective]
    exact IsExtraspecial.center_order_p 3 P
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := ZP) 3 (by rw [hZcard])
  have hcD : orderOf (c : D) = 3 := (Subgroup.orderOf_coe c).trans hc
  have hcgen : zpowers (c : D) = ZP := eq_of_le_of_card_ge (zpowers_le.mpr c.property)
    (by rw [Nat.card_zpowers,hcD,hZcard])
  obtain ⟨m,hm⟩ := hf c
  let X := (ZP.comap f).map M.subtype
  have hXi : (X.subgroupOf M).map f = ZP := by
    apply le_antisymm
    · rintro z ⟨m,hm,rfl⟩
      obtain ⟨b,hb,he⟩ := hm
      exact (show b = m from Subtype.ext he) ▸ hb
    · intro z hz
      obtain ⟨b,hb⟩ := hf z
      exact ⟨b,⟨b,show f b ∈ ZP from hb.symm ▸ hz,rfl⟩,hb⟩
  have htZ : t ∈ centralizer (ZP : Set D) :=
    ExtraspecialBinarySix.small_involution_centralizes_center ρ
      (imageRepresentation_injective M V h.normalized) P hPc h6 t
      (ht ▸ pow_orderOf_eq_one t) (by rw [htR]; exact hcod.le)
  have hZR : ZP ≤ normalizer (R : Set D) := by
    rw [←htR]
    exact (le_centralizer_iff.mp (zpowers_le.mpr htZ)).trans (Subgroup.centralizer_le_normalizer _)
  have hXn : X ≤ normalizer (U : Set G) :=
    moved_normalizer_of_image T hM.1.2 h (map_subtype_le _) (hXi.le.trans hZR)
  have hmX : (m : G) ∈ X := ⟨m,show f m ∈ ZP by rw [hm]; exact c.property,rfl⟩
  have hmMc : (m : G) ∈ Mc := hMc.symm ▸ hXn hmX
  let m₀ : Mc := ⟨m,hmMc⟩
  have hm3 : m ^ 3 ∈ f.ker := by
    change f (m ^ 3) = 1
    rw [map_pow,hm]
    simpa only [hcD] using pow_orderOf_eq_one (c : D)
  have hm3V : (m : G) ^ 3 ∈ centralizer (V : Set G) := by
    have hh : m ^ 3 ∈ (actionHom M V h.normalized).ker := congrArg Subtype.val hm3
    rwa [actionHom_ker] at hh
  have ha3 : (a m₀) ^ 3 = 1 := by
    rw [←map_pow]
    change m₀ ^ 3 ∈ a.ker
    rw [show a = actionHom Mc U hn from rfl,actionHom_ker]
    exact centralizer_le hUV hm3V
  have hane : a m₀ ≠ 1 := by
    intro he
    have hmU : (m : G) ∈ centralizer (U : Set G) := by
      have hh : m₀ ∈ a.ker := he
      rwa [show a = actionHom Mc U hn from rfl,actionHom_ker] at hh
    have hzero := SourceExtraspecialModel.extraspecial_center_fixedSpace_eq_bot ρ
      (imageRepresentation_injective M V h.normalized) P hPc h6
    have hUne : U ≠ ⊥ := by intro hb; rw [hb,card_bot] at hUcard; omega
    obtain ⟨u,hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    let v : V := ⟨u,hUV u.property⟩
    have hv : Additive.ofMul v ∈ fixedSpace ρ ZP := by
      rw [←hcgen,mem_fixedSpace_zpowers_iff]
      rw [←hm]
      apply congrArg Additive.ofMul
      apply Subtype.ext
      change (m : G) * (u : G) * (m : G)⁻¹ = u
      have hc : (u : G) * (m : G) = (m : G) * u := hmU u u.property
      rw [←hc,mul_inv_cancel_right]
    rw [hzero,Submodule.mem_bot] at hv
    apply hu
    exact Subtype.ext (congrArg (fun w : Additive V => (w.toMul : G)) hv)
  have hIcard : Nat.card (zpowers (a m₀)) = 3 := by
    rw [Nat.card_zpowers,orderOf_eq_prime ha3 hane]
  change ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃ m ∈ Mc, m * (u : G) * m⁻¹ = v
  intro u v hu hv
  have horbit := MulAction.nonidentity_mem_orbit_of_four_automorphism_subgroup
    hUcard (zpowers (a m₀)) (by omega) u hu v hv
  obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp horbit
  have hbA : (b : MulAut U) ∈ a.range :=
    (zpowers_le.mpr (show a m₀ ∈ a.range from ⟨m₀,rfl⟩)) b.property
  obtain ⟨n,hn'⟩ := hbA
  refine ⟨n,n.property,?_⟩
  have hb' : (b : MulAut U) u = v := hb
  rw [←hn'] at hb'
  exact congrArg Subtype.val hb'

/-- Every nonidentity point of the original moved plane has its entire
ambient centralizer in the original partner. -/
theorem PreparedChosenModule.extraspecial_moved_point_centralizer_le_partner
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    {u : G} (huU : u ∈ ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆) (hu1 : u ≠ 1) :
    centralizer ({u} : Set G) ≤ Mc := by
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  have hseed := (h.extraspecial_thompson_moved_seed_and_card hG T hempty hM hmany hJ hfull hex).1
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  obtain ⟨m,hm,hmu⟩ := h.extraspecial_moved_transitive hG T hempty hM hmany hJ hu hfull hex
    (⟨z,hseed z.property⟩ : U) ⟨u,huU⟩ (fun he => hz1 (congrArg Subtype.val he))
    (fun he => hu1 (congrArg Subtype.val he))
  change m * (z : G) * m⁻¹ = u at hmu
  have hcz := central_involution_centralizer_le_partner T hu z.property hz1
  intro x hx
  have hxz : m⁻¹ * x * m ∈ centralizer ({(z : G)} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hxu := mem_centralizer_singleton_iff.mp hx
    change x * u = u * x at hxu
    rw [←hmu] at hxu
    have hh := congrArg (fun y : G => m⁻¹ * y * m) hxu
    convert hh using 1 <;> group
  have hh := Mc.mul_mem (Mc.mul_mem hm (hcz hxz)) (Mc.inv_mem hm)
  convert hh using 1
  group

/-- Every transporter between nonidentity elements of the original moved
plane belongs to its actual normalizer, the centralizer partner. -/
theorem PreparedChosenModule.extraspecial_moved_transporter_le_partner
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (g u : G) (huU : u ∈ ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆) (hu1 : u ≠ 1)
    (hgu : g * u * g⁻¹ ∈ ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆) : g ∈ Mc := by
  apply conjugator_mem_of_centralizer_le
    (h.extraspecial_moved_point_centralizer_le_partner hG T hempty hM hmany hJ hu hfull hex huU hu1)
  have hgu1 : g * u * g⁻¹ ≠ 1 := by
    intro he
    apply hu1
    have hh := congrArg (MulAut.conj g).symm he
    change (MulAut.conj g).symm (MulAut.conj g u) = (MulAut.conj g).symm 1 at hh
    simpa only [MulEquiv.symm_apply_apply,map_one] using hh
  exact h.extraspecial_moved_transitive hG T hempty hM hmany hJ hu hfull hex
    ⟨u,huU⟩ ⟨g*u*g⁻¹,hgu⟩ (fun he => hu1 (congrArg Subtype.val he))
    (fun he => hgu1 (congrArg Subtype.val he))

/-- Distinct ambient conjugates of the literal moved plane intersect
trivially. This does not assert strong closure inside the original Sylow. -/
theorem PreparedChosenModule.extraspecial_moved_trivial_intersections
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    ∀ g : G, U ⊓ U.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      U.map (MulAut.conj g).toMonoidHom = U := by
  classical
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  change ∀ g : G, U ⊓ U.map (MulAut.conj g).toMonoidHom = ⊥ ∨
    U.map (MulAut.conj g).toMonoidHom = U
  intro g
  by_cases hb : U ⊓ U.map (MulAut.conj g).toMonoidHom = ⊥
  · exact Or.inl hb
  right
  obtain ⟨x,hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hb
  obtain ⟨u,huU,he⟩ := x.property.2
  change g * u * g⁻¹ = (x : G) at he
  have hu1 : u ≠ 1 := by
    intro hu1
    apply hx
    apply Subtype.ext
    change (x : G) = 1
    rw [←he,hu1,mul_one,mul_inv_cancel]
  have hgu : g * u * g⁻¹ ∈ U := by rw [he]; exact x.property.1
  have hg := h.extraspecial_moved_transporter_le_partner
    hG T hempty hM hmany hJ hu hfull hex g u huU hu1 hgu
  have hn := (h.extraspecial_partner_module_and_normalizer
    hG T hempty hM hmany hJ hu hfull hex).2
  exact mem_normalizer_iff_map_conj_eq.mp (hn ▸ hg)

end CFSG.Quasithin.Chapter15.Section01
