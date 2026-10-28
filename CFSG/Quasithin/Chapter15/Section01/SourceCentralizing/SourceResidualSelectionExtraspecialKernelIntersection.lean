module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelBaer
public import Mathlib.GroupTheory.PGroup

/-!
# The full module meets the partner core in the fixed subgroup or the full module

The actual central cubic preserves V and the partner's two-core Q. It acts
fixed-point-freely on V, so orbit counting makes |V ∩ Q| congruent to one
modulo three. The proved E ≤ Q gives the lower bound sixteen, while |V|=64.
The only possible subgroup orders are therefore sixteen and sixty-four.
This is a source consequence and makes no normalization claim for C_G(U).
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Section02.ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_fixed_free_card_mod_three
    {H : Type*} [Group H] [Finite H]
    (a : MulAut H) (hcube : a ^ 3 = 1)
    (hfixed : ∀ x : H, a x = x → x = 1) : Nat.card H % 3 = 1 := by
  let line := Subgroup.zpowers a
  have hp : IsPGroup 3 line := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [line,Nat.card_zpowers,pow_one] using orderOf_dvd_of_pow_eq_one hcube)
  let fixed := FixedPoints.subgroup line H
  have hbot : fixed = ⊥ := by
    apply bot_unique
    intro x hx
    apply hfixed x
    exact ((FixedPoints.mem_subgroup (M := line) (α := H) (a := x)).mp hx)
      ⟨a,Subgroup.mem_zpowers a⟩
  have hmod := hp.card_modEq_card_fixedPoints H
  change Nat.card H % 3 = Nat.card fixed % 3 at hmod
  simpa only [hbot,Subgroup.card_bot] using hmod

set_option backward.isDefEq.respectTransparency false in
/-- The literal full module meets the original moved-plane centralizer's
core in its fixed sixteen, or is contained in that core. -/
theorem PreparedChosenModule.extraspecial_module_intersection_core
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
    let Q := (centralizer (U : Set G)).pCoreIn 2
    V ⊓ Q = thompsonFixed T V ∨ V ≤ Q := by
  let := h.elementary
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let Q := (centralizer (U : Set G)).pCoreIn 2
  let E := thompsonFixed T V
  let F := V ⊓ Q
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  have hf : Function.Surjective f := (actionHom M V h.normalized).rangeRestrict_surjective
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let P := pResidual 2 D
  let ZP := (center P).map P.subtype
  have hEF : E ≤ F := le_inf inf_le_left
    (h.extraspecial_moved_fixed_le_centralizer_twoCore hG T hempty hM hmany hJ hu hfull hex)
  have hEcard : Nat.card E = 16 :=
    h.extraspecial_thompson_fixed_card hG T hempty hM hmany hJ hfull hex
  have hcore := h.extraspecial_moved_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hQnorm : Mc ≤ normalizer (Q : Set G) := by
    change Mc ≤ normalizer ((centralizer (U : Set G)).pCoreIn 2 : Set G)
    rw [hcore.1]
    exact Mc.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  have hmod := h.extraspecial_partner_module_and_normalizer
    hG T hempty hM hmany hJ hu hfull hex
  obtain ⟨t,ht,htR,hr⟩ := h.extraspecial_small_thompson_image
    hG T hempty hM hmany hJ hfull hex
  change zpowers t = R at htR
  change fixedCodim ρ R = 2 at hr
  obtain ⟨_,_,_,hP,hPc,_,h6,_⟩ := hex
  let : IsExtraspecial 3 P := hP
  have hVcard : Nat.card V = 64 := by
    change Nat.card (Additive V) = 64
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,h6]
    norm_num
  have hZcard : Nat.card ZP = 3 := by
    rw [show ZP = (center P).map P.subtype from rfl,card_map_of_injective P.subtype_injective]
    exact IsExtraspecial.center_order_p 3 P
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := ZP) 3 (by rw [hZcard])
  have hcD : orderOf (c : D) = 3 := (Subgroup.orderOf_coe c).trans hc
  have hcgen : zpowers (c : D) = ZP := eq_of_le_of_card_ge (zpowers_le.mpr c.property)
    (by rw [Nat.card_zpowers,hcD,hZcard])
  have htZ : t ∈ centralizer (ZP : Set D) :=
    ExtraspecialBinarySix.small_involution_centralizes_center ρ
      (imageRepresentation_injective M V h.normalized) P hPc h6 t
      (by simpa only [ht] using pow_orderOf_eq_one t) (by rw [htR]; exact hr.le)
  have hZR : ZP ≤ normalizer (R : Set D) := by
    rw [←htR]
    exact (le_centralizer_iff.mp (zpowers_le.mpr htZ)).trans
      (Subgroup.centralizer_le_normalizer _)
  let WU := subspaceCommutator ρ ⊤ R
  have hZstable : ZP ≤ subspaceStabilizer ρ WU :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hZR
  have hUambient := ambientSpace_moved h.normalized h.le_selected
    ((ChapterB.thompsonJ_le (T : Subgroup G) 1).trans hM.1.2)
  change ambientSpace V WU = U at hUambient
  let X := (ZP.comap f).map M.subtype
  have hXMc : X ≤ Mc := by
    rw [hmod.2]
    change X ≤ normalizer (U : Set G)
    rw [←hUambient]
    apply le_normalizer_iff.mpr
    rintro _ ⟨m,hm,rfl⟩ _ ⟨v,hv,rfl⟩
    exact ⟨(ρ (f m) (Additive.ofMul v)).toMul,
      (hZstable hm (Additive.ofMul v)).2 hv,rfl⟩
  have hXF : X ≤ normalizer (F : Set G) :=
    (le_inf ((map_subtype_le _).trans h.normalized) (hXMc.trans hQnorm)).trans
      inf_normalizer_le_normalizer_inf
  let a := actionHom X F hXF
  obtain ⟨m,hm⟩ := hf c
  let mX : X := ⟨m,⟨m,show f m ∈ ZP by rw [hm]; exact c.property,rfl⟩⟩
  have hm3 : m ^ 3 ∈ f.ker := by
    change f (m ^ 3) = 1
    rw [map_pow,hm]
    simpa only [hcD] using pow_orderOf_eq_one (c : D)
  have hm3V : (m : G) ^ 3 ∈ centralizer (V : Set G) := by
    have hh : m ^ 3 ∈ (actionHom M V h.normalized).ker := congrArg Subtype.val hm3
    rwa [actionHom_ker] at hh
  have ha3 : (a mX) ^ 3 = 1 := by
    rw [←map_pow]
    change mX ^ 3 ∈ a.ker
    rw [show a = actionHom X F hXF from rfl,actionHom_ker]
    exact centralizer_le (show F ≤ V from inf_le_left) hm3V
  have hfixed : ∀ v : F, a mX v = v → v = 1 := by
    intro v hv
    have hzero := SourceExtraspecialModel.extraspecial_center_fixedSpace_eq_bot ρ
      (imageRepresentation_injective M V h.normalized) P hPc h6
    let w : V := ⟨v,v.property.1⟩
    have hw : Additive.ofMul w ∈ fixedSpace ρ ZP := by
      rw [←hcgen,mem_fixedSpace_zpowers_iff,←hm]
      apply congrArg Additive.ofMul
      apply Subtype.ext
      change (m : G) * (v : G) * (m : G)⁻¹ = v
      exact congrArg Subtype.val hv
    rw [hzero,Submodule.mem_bot] at hw
    exact Subtype.ext (congrArg (fun x : Additive V => (x.toMul : G)) hw)
  have hmodF := cubic_fixed_free_card_mod_three (a mX) ha3 hfixed
  have hlow : 16 ≤ Nat.card F := hEcard ▸ card_le_of_le hEF
  have hdiv : Nat.card F ∣ 2 ^ 6 := by
    simpa only [hVcard,show 2 ^ 6 = 64 by decide] using
      card_dvd_of_le (show F ≤ V from inf_le_left)
  have hcards : Nat.card F = 16 ∨ Nat.card F = 64 := by
    obtain ⟨n,hn,hpow⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    interval_cases n <;> norm_num only [Nat.reducePow] at hpow <;> omega
  change F = E ∨ V ≤ Q
  rcases hcards with he | hv
  · exact Or.inl (eq_of_le_of_card_ge hEF (by rw [he,hEcard])).symm
  · have heq : F = V := eq_of_le_of_card_ge inf_le_left (by rw [hv,hVcard])
    exact Or.inr (heq ▸ (show F ≤ Q from inf_le_right))

end CFSG.Quasithin.Chapter15.Section01
