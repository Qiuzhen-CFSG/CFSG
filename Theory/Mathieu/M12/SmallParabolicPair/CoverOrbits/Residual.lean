module

public import Theory.Mathieu.M12.SmallParabolicPair.CoverOrbits.Coordinates
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# The order-96 residual and an extra central involution

Cubic action differences generate both concrete quaternion factors, so the
core lies in the two-residual of the marked involution centralizer.
The residual lies in the kernel of the sign of the existing S₃ quotient.
The core and the cubic element force its order to be divisible by 96;
the sign kernel has precisely that order. Thus the residual is this kernel,
and its normal order-32 core is Sylow and hence its two-core.

The element `leftI * rightI * FirstCore.secondSwap` is an involution with
eight moved points. Exhaustive fusion puts it in the central class. Its
negative sign places it outside the residual, and the two sign values give
the required generation of the entire involution centralizer.

Source: Aschbacher–Smith, I.2.2(5), printed pp.411–412 / PDF pp.422–423.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.CoverOrbits
open Subgroup FirstCore
noncomputable section
set_option maxRecDepth 100000
private def leftIn : Q →* firstParabolic :=
  leftEmbedding.codRestrict firstParabolic (fun q =>
    core_le_firstParabolic ((show leftFactor ≤ core from le_sup_left) ⟨q,rfl⟩))
private def rightIn : Q →* firstParabolic :=
  rightEmbedding.codRestrict firstParabolic (fun q =>
    core_le_firstParabolic ((show rightFactor ≤ core from le_sup_right) ⟨q,rfl⟩))

private theorem difference_mem (x : firstParabolic) :
    x⁻¹ * residualCubic.val * x * residualCubic.val⁻¹ ∈ pResidual 2 firstParabolic := by
  have h := (inferInstance : (pResidual 2 firstParabolic).Normal).conj_mem
    residualCubic.val residualCubic.property x⁻¹
  simpa only [inv_inv, mul_assoc] using
    (pResidual 2 firstParabolic).mul_mem h ((pResidual 2 firstParabolic).inv_mem residualCubic.property)

theorem core_le_coverResidual : core ≤ coverResidual := by
  have hl (q : Q) : leftIn q ∈ pResidual 2 firstParabolic := by
    have h : ∀ q : Q, ∃ u v : Q,
      leftIn q = ((leftIn u)⁻¹ * residualCubic.val * leftIn u * residualCubic.val⁻¹) *
        ((leftIn v)⁻¹ * residualCubic.val * leftIn v * residualCubic.val⁻¹) := by decide +kernel
    obtain ⟨u,v,h⟩ := h q
    rw [h]
    exact (pResidual 2 firstParabolic).mul_mem (difference_mem _) (difference_mem _)
  have hr (q : Q) : rightIn q ∈ pResidual 2 firstParabolic := by
    have h : ∀ q : Q, ∃ u v : Q,
      rightIn q = ((rightIn u)⁻¹ * residualCubic.val * rightIn u * residualCubic.val⁻¹) *
        ((rightIn v)⁻¹ * residualCubic.val * rightIn v * residualCubic.val⁻¹) := by decide +kernel
    obtain ⟨u,v,h⟩ := h q
    rw [h]
    exact (pResidual 2 firstParabolic).mul_mem (difference_mem _) (difference_mem _)
  intro x hx
  obtain ⟨q,r,rfl⟩ := (mem_core x).mp hx
  exact ⟨leftIn q * rightIn r, (pResidual 2 firstParabolic).mul_mem (hl q) (hr r), rfl⟩

def signMap : firstParabolic →* ℤˣ := Equiv.Perm.sign.comp matchingQuotient

theorem signMap_surjective : Function.Surjective signMap := by
  intro u
  obtain ⟨σ,hσ⟩ := Equiv.Perm.sign_surjective (Fin 3) u
  obtain ⟨g,hg⟩ := matchingQuotient_surjective σ
  exact ⟨g, by change Equiv.Perm.sign (matchingQuotient g) = u; rw [hg,hσ]⟩

theorem residual_le_sign_ker : pResidual 2 firstParabolic ≤ signMap.ker := by
  apply sInf_le
  refine ⟨inferInstance, ?_⟩
  apply IsPGroup.of_card (n := 1)
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective signMap
    signMap_surjective).toEquiv, Nat.card_eq_fintype_card, Fintype.card_units_int]
  norm_num

theorem swap_sign : signMap ⟨secondSwap, secondSwap_mem⟩ = -1 := by
  change Equiv.Perm.sign (matchingQuotient _) = _
  rw [swap_image]
  exact Equiv.Perm.sign_swap (by decide)

theorem card_sign_ker : Nat.card signMap.ker = 96 := by
  have h := signMap.ker.card_mul_index
  rw [index_ker, signMap.range_eq_top_of_surjective
    signMap_surjective, card_top,
    card_firstParabolic] at h
  have hc : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  rw [hc] at h
  omega

theorem card_residual : Nat.card (pResidual 2 firstParabolic) = 96 := by
  have h32 : 32 ∣ Nat.card (pResidual 2 firstParabolic) := by
    rw [← card_core, ← Subgroup.card_map_of_injective firstParabolic.subtype_injective]
    exact Subgroup.card_dvd_of_le core_le_coverResidual
  have h3 : 3 ∣ Nat.card (pResidual 2 firstParabolic) := by
    have horder : orderOf residualCubic = 3 := by
      rw [← orderOf_injective (pResidual 2 firstParabolic).subtype
        (pResidual 2 firstParabolic).subtype_injective,
        ← orderOf_injective firstParabolic.subtype firstParabolic.subtype_injective]
      exact cubicActor_order
    rw [← horder]
    exact orderOf_dvd_natCard residualCubic
  have h96 : 96 ∣ Nat.card (pResidual 2 firstParabolic) := by
    have h := Nat.lcm_dvd h32 h3
    norm_num [Nat.lcm] at h
    exact h
  have hle := Subgroup.card_le_of_le residual_le_sign_ker
  rw [card_sign_ker] at hle
  exact le_antisymm hle (Nat.le_of_dvd (Nat.card_pos) h96)

theorem residual_card : Nat.card coverResidual = 96 := by
  rw [coverResidual, Subgroup.card_map_of_injective firstParabolic.subtype_injective]
  exact card_residual

theorem residual_eq_sign_ker : pResidual 2 firstParabolic = signMap.ker :=
  Subgroup.eq_of_le_of_card_ge residual_le_sign_ker (by rw [card_residual,card_sign_ker])

theorem coverResidual_le_firstParabolic : coverResidual ≤ firstParabolic :=
  Subgroup.map_subtype_le _

theorem residual_core : (pCore 2 coverResidual).map coverResidual.subtype = core := by
  have hcard : Nat.card (core.subgroupOf coverResidual) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe core_le_coverResidual).toEquiv,card_core]
  let S : Sylow 2 coverResidual := Sylow.ofCard (core.subgroupOf coverResidual) (by
    rw [hcard,residual_card]
    decide +kernel)
  have hn : (core.subgroupOf coverResidual).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer core_le_coverResidual).mpr
      (coverResidual_le_firstParabolic.trans firstParabolic_normalizes_core)
  have he : pCore 2 coverResidual = core.subgroupOf coverResidual := by
    apply le_antisymm (pCore_isPGroup.le_sylow_of_normal S)
    exact le_sSup ⟨hn, IsPGroup.of_card (n := 5) hcard⟩
  rw [he]
  exact Subgroup.map_subgroupOf_eq_of_le core_le_coverResidual

/-- A central-class involution in the odd coset of the residual. -/
def extra : M12 := leftI * rightI * secondSwap

theorem extra_order : orderOf extra = 2 := by
  apply orderOf_eq_prime <;> decide +kernel

theorem extra_mem : extra ∈ firstParabolic := by
  rw [firstParabolic, Subgroup.mem_centralizer_singleton_iff]
  decide +kernel

private theorem core_sign (q : core) :
    signMap (Subgroup.inclusion core_le_firstParabolic q) = 1 := by
  apply MonoidHom.mem_ker.mp
  apply residual_le_sign_ker
  obtain ⟨g,hg,he⟩ := core_le_coverResidual q.property
  have heq : g = Subgroup.inclusion core_le_firstParabolic q := Subtype.ext he
  exact heq ▸ hg

theorem extra_sign : signMap ⟨extra,extra_mem⟩ = -1 := by
  have hc : leftI * rightI ∈ core := by
    apply (mem_core _).mpr
    exact ⟨QuaternionGroup.a 1,QuaternionGroup.a 1,by decide +kernel⟩
  have he : (⟨extra,extra_mem⟩ : firstParabolic) =
    Subgroup.inclusion core_le_firstParabolic ⟨leftI * rightI,hc⟩ *
      ⟨secondSwap,secondSwap_mem⟩ := rfl
  rw [he,map_mul,core_sign,swap_sign,one_mul]

theorem extra_not_mem : extra ∉ coverResidual := by
  rintro ⟨g,hg,he⟩
  have heq : g = ⟨extra,extra_mem⟩ := Subtype.ext he
  have h := MonoidHom.mem_ker.mp (residual_le_sign_ker hg)
  rw [heq,extra_sign] at h
  exact (by decide : (-1 : ℤˣ) ≠ 1) h

theorem extra_fusion : IsConj z extra :=
  central_fusion_of_support extra extra_order (by decide +kernel)

theorem centralizer_generated : coverResidual ⊔ zpowers extra = firstParabolic := by
  apply le_antisymm (sup_le coverResidual_le_firstParabolic (zpowers_le.mpr extra_mem))
  intro x hx
  let xH : firstParabolic := ⟨x,hx⟩
  have hr (g : firstParabolic) (hg : signMap g = 1) :
      (g : M12) ∈ coverResidual := by
    exact ⟨g, residual_eq_sign_ker.symm ▸ MonoidHom.mem_ker.mpr hg, rfl⟩
  rcases Int.units_eq_one_or (signMap xH) with h | h
  · exact (show coverResidual ≤ coverResidual ⊔ zpowers extra from le_sup_left) (hr xH h)
  · have hk : signMap (xH * (⟨extra,extra_mem⟩ : firstParabolic)⁻¹) = 1 := by
      rw [map_mul,map_inv,h,extra_sign]
      decide +kernel
    have hprod := (coverResidual ⊔ zpowers extra).mul_mem
      ((show coverResidual ≤ coverResidual ⊔ zpowers extra from le_sup_left) (hr _ hk))
      ((show zpowers extra ≤ coverResidual ⊔ zpowers extra from le_sup_right) (mem_zpowers extra))
    simpa only [coe_mul,coe_inv,inv_mul_cancel_right] using hprod
end
end Sporadic.Mathieu.M12SmallPair.CoverOrbits
