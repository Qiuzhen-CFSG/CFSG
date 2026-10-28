module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.Basic

/-!
# The residual fusion deduction in 14.7.68

K centralizes U₀. If a right conjugate U₀ᵍ contains u and C_G(u)≤H,
then Kᵍ≤H. Taking the two-residual and comparing finite orders gives
Kᵍ=K. Consequently N_G(K)=H forces g∈H and U₀ᵍ=U₀.
Applying this to z recovers N_G(U₀)=H and zᴳ∩U₀={z} directly.
In particular this last deduction needs no extra maximal-local premise.

The normalizer identity in 14.7.67(4) remains an explicit premise of these
conditional deductions. The source's ambient analysis of that normalizer,
maximality in L*(G,T), and fixed-element centralizer exclusions remain
required before the full 14.7.67–68 assembly. No fusion, uniqueness or
local conclusion is stored in a source hypothesis record.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
proof of 14.7.68, printed p.1071.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- A conjugate residual contained in H is the original residual. -/
theorem conjugate_K_eq_of_le_H (g : G) (h : conjugate (K F) g ≤ F.H) :
    conjugate (K F) g = K F := by
  let a := (MulAut.conj g⁻¹).toMonoidHom
  have hp : IsPPerfect 2 (conjugate (K F) g) :=
    (K_twoPerfect F).of_surjective ((K F).equivMapOfInjective a (MulAut.conj g⁻¹).injective).toMonoidHom
      ((K F).equivMapOfInjective a (MulAut.conj g⁻¹).injective).surjective
  have hr := embedded_pResidual_mono 2 h
  rw [(pResidual_eq_top_iff 2 _).mpr hp, ← MonoidHom.range_eq_map, range_subtype] at hr
  apply eq_of_le_of_card_ge hr
  exact (card_map_of_injective (K := K F) (MulAut.conj g⁻¹).injective).ge

/-- The residual recovers any conjugator returning U₀ to a controlled centralizer. -/
theorem returning_U₀_conjugator_mem_H
    (hn : normalizer (K F : Set G) = F.H) (u g : G)
    (hc : centralizer ({u} : Set G) ≤ F.H) (hu : u ∈ conjugate d.U₀ g) : g ∈ F.H := by
  have hk : conjugate (K F) g ≤ centralizer (conjugate d.U₀ g : Set G) :=
    (map_mono d.K_centralizes_U₀).trans (map_centralizer_le_centralizer_image _ _)
  have hh : conjugate (K F) g ≤ F.H :=
    hk.trans ((centralizer_le (Set.singleton_subset_iff.mpr hu)).trans hc)
  rw [← hn]
  exact (conjugate_eq_iff _ _).mp (conjugate_K_eq_of_le_H g hh)

/-- The uniqueness deduction in 14.7.68, with centralizer control still explicit. -/
theorem U₀_conjugate_eq_of_centralizer_le
    (hn : normalizer (K F : Set G) = F.H) (u g : G)
    (hc : centralizer ({u} : Set G) ≤ F.H) (hu : u ∈ conjugate d.U₀ g) :
    conjugate d.U₀ g = d.U₀ :=
  (conjugate_eq_iff _ _).mpr (d.H_normalizes_U₀
    (d.returning_U₀_conjugator_mem_H hn u g hc hu))

/-- U₀'s normalizer is recovered from K, with no maximal-local certificate. -/
theorem normalizer_U₀_eq_of_normalizer_K (hn : normalizer (K F : Set G) = F.H) :
    normalizer (d.U₀ : Set G) = F.H := by
  apply le_antisymm ?_ d.H_normalizes_U₀
  intro g hg
  apply d.returning_U₀_conjugator_mem_H hn d.z g d.centralizer_eq.ge
  rw [(conjugate_eq_iff _ _).mpr hg]
  exact d.z_mem_U₀

/-- The ambient element class meets the original fixed-space preimage only at z.
The remaining premise is 14.7.67(4), not a fusion or uniqueness premise. -/
theorem fusion_z_of_normalizer_K (hn : normalizer (K F : Set G) = F.H) :
    {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z} := by
  ext x
  constructor
  · rintro ⟨hconj, hx⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hz : d.z ∈ conjugate d.U₀ g := by
      apply mem_map.mpr
      refine ⟨x, hx, ?_⟩
      change g⁻¹ * x * (g⁻¹)⁻¹ = d.z
      rw [← hg]
      group
    have hH := d.returning_U₀_conjugator_mem_H hn d.z g d.centralizer_eq.ge hz
    have hfix := mem_centralizer_singleton_iff.mp (d.centralizer_eq ▸ hH)
    apply Set.mem_singleton_iff.mpr
    rw [← hg, hfix, mul_inv_cancel_right]
  · rintro rfl
    exact ⟨IsConj.refl _, d.z_mem_U₀⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
