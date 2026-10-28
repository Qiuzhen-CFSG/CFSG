module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.ResidualCore
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Cubic inversion in images of the full first J₄ centralizer

A quasisimple image of the perfect residual kills the full extraspecial
core. After factoring through the literal quotient 3.M₂₂.2, a central
image of the perfect cover lifts to its scalar center. The marked outer
coset inverts that scalar. Hence no element of order three in the residual
image is centralized by the image of the full involution centralizer.

The application retains the full original centralizer in the exceptional
cubic comparison of Aschbacher–Smith 4.4.3, printed p.623. The native
quotient and matrix certificates retain their ATLAS attribution and license.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.InvolutionCentralizers.First
open QuotientExtension Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem central_cover_image_sq
    {Y : Type*} [Group Y] (f : actionGroup →* Y)
    (y : Y) (hy : y ∈ coverSubgroup.map f) (hne : y ≠ 1)
    (hfix : ∀ c : actionGroup, f c * y = y * f c) : y ^ 2 = 1 := by
  let g := f.comp coverInclusion
  have hyr : y ∈ g.range := by
    obtain ⟨c,hc,rfl⟩ := hy
    obtain ⟨v,rfl⟩ := coverInclusion_range.symm ▸ hc
    exact ⟨v,rfl⟩
  have hgn : g.range ≠ ⊥ := fun he => hne (mem_bot.mp (he ▸ hyr))
  let : Nontrivial g.range := (nontrivial_iff_ne_bot _).mpr hgn
  obtain ⟨v,hv⟩ := hyr
  have hvz : v ∈ center M22TripleCover := by
    rw [← IsQuasisimple.comap_center_of_surjective g.rangeRestrict g.rangeRestrict_surjective]
    apply mem_center_iff.mpr
    rintro ⟨w,⟨u,rfl⟩⟩
    apply Subtype.ext
    change g u * g v = g v * g u
    rw [hv]
    exact hfix (coverInclusion u)
  rw [M22TripleCover.center_eq_zpowers] at hvz
  obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hvz
  have hinv : outerElement * coverInclusion v * outerElement⁻¹ = (coverInclusion v)⁻¹ := by
    rw [←hn,map_zpow]
    change outerElement * scalarElement ^ n * outerElement⁻¹ = (scalarElement ^ n)⁻¹
    rw [←conj_zpow,outerElement_conj_scalar,inv_zpow]
  have hh := congrArg f hinv
  simp only [map_mul,map_inv] at hh
  change f outerElement * g v * (f outerElement)⁻¹ = (g v)⁻¹ at hh
  rw [hv,hfix,mul_assoc,mul_inv_cancel,mul_one] at hh
  calc y ^ 2 = y * y := pow_two y
       _ = y⁻¹ * y := congrArg (fun u => u*y) hh
       _ = 1 := inv_mul_cancel y

/-- The full first centralizer cannot fix a cubic in a surviving quasisimple residual image. -/
theorem no_fixed_residual_cubic
    {Y : Type*} [Group Y] (f : centralizer →* Y)
    [IsQuasisimple ((solvableResidual centralizer).map f)]
    (y : Y) (hy : orderOf y = 3)
    (hmem : y ∈ (solvableResidual centralizer).map f)
    (hfix : ∀ c : centralizer, f c * y = y * f c) : False := by
  have hc : pCore 2 centralizer ≤ f.ker := by
    have hk := residual_quasisimple_image_kills_twoCore (f.subgroupMap _)
      (f.subgroupMap_surjective _)
    intro x hx
    let u : solvableResidual centralizer := ⟨x,twoCore_le_residual hx⟩
    have hu : u ∈ pCore 2 (solvableResidual centralizer) := by
      rw [pCore_eq_comap_of_normal]
      exact hx
    exact congrArg Subtype.val (hk hu)
  let q := centralizerExtension.rightHom
  let g : actionGroup →* Y := (QuotientGroup.lift _ f hc).comp quotientEquiv.symm.toMonoidHom
  have hg : ∀ c : centralizer, g (q c) = f c := by
    intro c
    change QuotientGroup.lift _ f hc
      (quotientEquiv.symm (centralizerExtension.rightHom c)) = f c
    rw [centralizerExtension_rightHom,quotientEquiv.symm_apply_apply]
    rfl
  have hPH : solvableResidual centralizer ≤ H := by
    let : Group.IsSolvable (centralizer ⧸ H) := Group.isSolvable_of_isSolvable_injective
      (f := centralizerQuotientEquivC2.toMonoidHom) centralizerQuotientEquivC2.injective
    exact solvableResidual_le_of_solvable_quotient H
  have hym : y ∈ coverSubgroup.map g := by
    obtain ⟨c,hc,rfl⟩ := hmem
    exact ⟨q c,hPH hc,hg c⟩
  have hne : y ≠ 1 := by intro he; rw [he,orderOf_one] at hy; omega
  have hh := central_cover_image_sq g y hym hne (by
    intro c
    obtain ⟨c,rfl⟩ := centralizerExtension.rightHom_surjective c
    rw [hg]
    exact hfix c)
  have hd := orderOf_dvd_of_pow_eq_one hh
  rw [hy] at hd
  norm_num at hd
end Janko4.InvolutionCentralizers.First
