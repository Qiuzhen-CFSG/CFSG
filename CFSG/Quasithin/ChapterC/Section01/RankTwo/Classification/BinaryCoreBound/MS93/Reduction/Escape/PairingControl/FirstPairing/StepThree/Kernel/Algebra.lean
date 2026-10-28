module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Recognition

/-!
# Excluding fixed kernels in the intrinsic moving quotient

Conjugation on C/U descends through the actual quotient onto SL₃(2) when
its kernel centralizes C modulo U. If C is its full ambient commutator,
then C/U is its full moving subgroup. The binary small-involution theorem
therefore makes its fixed subgroup trivial. Any subgroup centralized modulo
U meets C inside U.

The quotient, descended action and commutator image are literal; no order
assertion replaces the kernel. These local adapters use the already checked
binary specialization of MS93 (1.4)--(1.5).
Source: Meierfrankenfeld--Stellmacher (1993), pp.842--843, applied to the
intrinsic section in (4.3.2)(3), printed p.884.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.Kernel
open Initial.Natural.Splitting
variable {A : Type*} [Group A] (C U : Subgroup A) [C.Normal] [U.Normal]

noncomputable def action (π : A →* SL) (hπ : Function.Surjective π)
    (hker : ⁅C, π.ker⁆ ≤ U) : SL →* MulAut (C ⧸ U.subgroupOf C) :=
  π.liftOfSurjective hπ ⟨quotientAction C U, quotientAction_kills C U π.ker hker⟩

theorem action_comp (π : A →* SL) (hπ : Function.Surjective π)
    (hker : ⁅C, π.ker⁆ ≤ U) : (action C U π hπ hker).comp π = quotientAction C U := by
  ext g
  unfold action
  rw [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.liftOfRightInverse_comp_apply]

theorem quotientAction_moving :
    commutatorAction (quotientAction C U).range (C ⧸ U.subgroupOf C) =
      (⁅C, (⊤ : Subgroup A)⁆.subgroupOf C).map (QuotientGroup.mk' (U.subgroupOf C)) := by
  have h := quotient_conjugation_commutatorAction_eq_image ⊤ C U ⊤
    le_normalizer_of_normal le_rfl inferInstance
    ((quotientAction C U).comp (topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom)
    (fun g v => quotientAction_apply C U g v)
  have he : ((⊤ : Subgroup A).subgroupOf ⊤).map
      ((quotientAction C U).comp (topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom) = (quotientAction C U).range := by
    rw [top_subgroupOf, ← MonoidHom.range_eq_map, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (topEquiv : (⊤ : Subgroup A) ≃* A).surjective, ← MonoidHom.range_eq_map]
  rwa [he] at h

theorem action_injective (π : A →* SL) (hπ : Function.Surjective π)
    (hker : ⁅C, π.ker⁆ ≤ U) (hfull : ⁅C, (⊤ : Subgroup A)⁆ = C)
    (hne : ¬ C ≤ U) : Function.Injective (action C U π hπ hker) := by
  let ρ := action C U π hπ hker
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  apply ρ.ker_eq_bot_iff.mp
  rcases (inferInstance : ρ.ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact hk
  · exfalso
    apply hne
    rw [← hfull, commutator_comm]
    apply commutator_le.mpr
    intro g _ c hc
    have he : quotientAction C U g = 1 := by
      rw [← action_comp C U π hπ hker]
      change ρ (π g) = 1
      apply MonoidHom.mem_ker.mp
      rw [hk]
      trivial
    have hh := quotientAction_apply C U g ⟨c, hc⟩
    rw [he] at hh
    have h := QuotientGroup.eq_iff_div_mem.mp hh.symm
    change g * c * g⁻¹ / c ∈ U at h
    simpa only [commutatorElement_def, div_eq_mul_inv] using h

theorem intersection_bound [Finite A] [IsElementaryAbelian 2 (C ⧸ U.subgroupOf C)]
    (π : A →* SL) (hπ : Function.Surjective π)
    (hker : ⁅C, π.ker⁆ ≤ U) (hfull : ⁅C, (⊤ : Subgroup A)⁆ = C)
    (hne : ¬ C ≤ U) (hsmall : HasSmallInvolution (action C U π hπ hker))
    (K : Subgroup A) (hK : ⁅K, (⊤ : Subgroup A)⁆ ≤ U) : C ⊓ K ≤ U := by
  let ρ := action C U π hπ hker
  obtain ⟨s⟩ := naturalActionSplitting_of_small_involution ρ
    (action_injective C U π hπ hker hfull hne) hsmall
  have hr : ρ.range = (quotientAction C U).range := by
    rw [← action_comp C U π hπ hker, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr hπ, ← MonoidHom.range_eq_map]
  have hm : commutatorAction ρ.range (C ⧸ U.subgroupOf C) = ⊤ := by
    rw [hr, quotientAction_moving, hfull, subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hf : FixedPoints.subgroup ρ.range (C ⧸ U.subgroupOf C) = ⊥ := by
    have hd := s.disjoint.eq_bot
    simpa only [hm, top_inf_eq] using hd
  intro x hx
  let v : C := ⟨x, hx.1⟩
  have hv : QuotientGroup.mk' (U.subgroupOf C) v ∈
      FixedPoints.subgroup ρ.range (C ⧸ U.subgroupOf C) := by
    intro g
    obtain ⟨t, ht⟩ := g.property
    obtain ⟨a, rfl⟩ := hπ t
    change g.val (QuotientGroup.mk' (U.subgroupOf C) v) = _
    rw [← ht]
    have ha : ρ (π a) = quotientAction C U a :=
      congrArg (fun f : A →* MulAut (C ⧸ U.subgroupOf C) => f a)
        (action_comp C U π hπ hker)
    rw [ha, quotientAction_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change a * x * a⁻¹ / x ∈ U
    have hc : ⁅a, x⁆ ∈ U := by
      rw [commutator_comm] at hK
      exact hK (commutator_mem_commutator (mem_top a) hx.2)
    simpa only [commutatorElement_def, div_eq_mul_inv] using hc
  rw [hf] at hv
  change (v : A) ∈ U
  exact (QuotientGroup.eq_one_iff v).mp hv
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.Kernel
