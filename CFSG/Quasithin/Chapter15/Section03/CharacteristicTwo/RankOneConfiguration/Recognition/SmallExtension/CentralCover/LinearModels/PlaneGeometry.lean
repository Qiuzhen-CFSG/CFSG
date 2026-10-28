module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearThree
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# Marked binary planes and their prime-to-three residuals

An arbitrary plane in the natural binary three-space can be sent to the
coordinate plane by an actual special linear matrix. In its stabilizer,
the cubic rotation belongs to O^{3′}; commuting it with e₁₂(1) gives e₀₂(1).
Residual transport therefore supplies both marked elements under the same
conjugated quotient map. No residual membership is assumed.

Source: Aschbacher--Smith, C.1.34(1)--(3), 15.3.26--28 and 15.3.31,
printed pp.136, 1130--1132.
-/

@[expose] public section

open Subgroup Matrix Matrix.SpecialLinearGroup Representation Representation.OneCohomology
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover
open LinearThree

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearModels.PlaneGeometry

def plane : Submodule (ZMod 2) Space := LinearMap.ker (LinearMap.proj 2)
noncomputable def stabilizer (W : Submodule (ZMod 2) Space) : Subgroup SL :=
  (BinaryLinear.parabolic W).comap (BinaryLinear.OuterCyclic.slEquivLinear 3).toMonoidHom

private def radicalSecond : SL := transvection (show (1 : Fin 3) ≠ 2 by decide) 1

private theorem rotation_cube : planeRotation ^ 3 = 1 := by decide
private theorem commutator_rotation : planeRotation * radicalSecond * planeRotation⁻¹ * radicalSecond⁻¹ = planeTransvection := by decide

private theorem rotation_mem : planeRotation ∈ stabilizer plane := by
  intro v
  change (natural planeRotation v) 2 = 0 ↔ v 2 = 0
  rw [planeRotation, map_mul, Module.End.mul_apply]
  change (specialLinearNatural 3 _ (specialLinearNatural 3 _ v)) 2 = 0 ↔ _
  rw [SLHigherNatural.action_transvection, SLHigherNatural.action_transvection]
  simp

private theorem second_mem : radicalSecond ∈ stabilizer plane := by
  intro v
  change (natural radicalSecond v) 2 = 0 ↔ v 2 = 0
  rw [radicalSecond, SLHigherNatural.action_transvection]
  simp

theorem marked_mem_residual :
    planeTransvection ∈ (primeToResidual 3 (stabilizer plane)).map (stabilizer plane).subtype ∧
    planeRotation ∈ (primeToResidual 3 (stabilizer plane)).map (stabilizer plane).subtype := by
  let P := stabilizer plane
  let r : P := ⟨planeRotation, rotation_mem⟩
  let s : P := ⟨radicalSecond, second_mem⟩
  let N := primeToResidual 3 P
  have hr : r ∈ N := mem_primeToResidual_of_pow (n := 1)
    (Subtype.ext rotation_cube)
  have hc : r * s * r⁻¹ * s⁻¹ ∈ N := by
    have hn := (inferInstance : N.Normal).conj_mem r⁻¹ (N.inv_mem hr) s
    simpa only [← mul_assoc] using N.mul_mem hr hn
  exact ⟨mem_map.mpr ⟨_, hc, commutator_rotation⟩, mem_map.mpr ⟨r,hr,rfl⟩⟩

theorem plane_finrank : Module.finrank (ZMod 2) plane = 2 := by
  have hs : Function.Surjective (LinearMap.proj 2 : Space →ₗ[ZMod 2] ZMod 2) := by
    intro a
    exact ⟨fun _ => a, rfl⟩
  have h := (LinearMap.proj 2 : Space →ₗ[ZMod 2] ZMod 2).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at h
  simp only [finrank_top, Module.finrank_self, Module.finrank_pi, Fintype.card_fin] at h
  change Module.finrank (ZMod 2) (LinearMap.ker (LinearMap.proj 2 : Space →ₗ[ZMod 2] ZMod 2)) = 2
  omega

theorem exists_plane_coordinates (W : Submodule (ZMod 2) Space)
    (hd : Module.finrank (ZMod 2) W = 2) :
    ∃ a : SL, ∀ v : Space, natural a v ∈ plane ↔ v ∈ W := by
  let f : W ≃ₗ[ZMod 2] plane := LinearEquiv.ofFinrankEq _ _ (hd.trans plane_finrank.symm)
  obtain ⟨g,hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨(BinaryLinear.OuterCyclic.slEquivLinear 3).symm g, ?_⟩
  intro v
  change (BinaryLinear.OuterCyclic.slEquivLinear 3
    ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm g)) v ∈ plane ↔ v ∈ W
  rw [MulEquiv.apply_symm_apply]
  constructor
  · intro hv
    obtain ⟨w,hw⟩ := f.surjective ⟨g v,hv⟩
    have he : g w = g v := (hg w).symm.trans (congrArg Subtype.val hw)
    exact (g.injective he) ▸ w.property
  · intro hv
    rw [← hg ⟨v,hv⟩]
    exact (f ⟨v,hv⟩).property

private theorem stabilizer_conj_iff (W : Submodule (ZMod 2) Space) (a : SL)
    (ha : ∀ v : Space, natural a v ∈ plane ↔ v ∈ W) (g : SL) :
    a * g * a⁻¹ ∈ stabilizer plane ↔ g ∈ stabilizer W := by
  change (∀ v, natural (a * g * a⁻¹) v ∈ plane ↔ v ∈ plane) ↔
    (∀ v, natural g v ∈ W ↔ v ∈ W)
  constructor
  · intro hg v
    have h := hg (natural a v)
    simpa only [map_mul, Module.End.mul_apply, inv_self_apply, ha] using h
  · intro hg v
    have h := (ha (natural g (natural a⁻¹ v))).trans (hg (natural a⁻¹ v))
    have h' := ha (natural a⁻¹ v)
    rw [self_inv_apply] at h'
    simpa only [map_mul, Module.End.mul_apply] using h.trans h'.symm

theorem stabilizer_map_conj (W : Submodule (ZMod 2) Space) (a : SL)
    (ha : ∀ v : Space, natural a v ∈ plane ↔ v ∈ W) :
    (stabilizer W).map (MulAut.conj a).toMonoidHom = stabilizer plane := by
  ext x
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact (stabilizer_conj_iff W a ha g).mpr hg
  · intro hx
    have he : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
    refine mem_map.mpr ⟨a⁻¹ * x * a, ?_, he⟩
    exact (stabilizer_conj_iff W a ha _).mp (he.symm ▸ hx)

theorem marked_mem_image {H : Type*} [Group H] [Finite H]
    (f : H →* SL) (P Y : Subgroup H)
    (hY : Y = (primeToResidual 3 P).map P.subtype)
    (W : Submodule (ZMod 2) Space) (hP : P.map f = stabilizer W)
    (a : SL) (ha : ∀ v : Space, natural a v ∈ plane ↔ v ∈ W) :
    planeTransvection ∈ Y.map ((MulAut.conj a).toMonoidHom.comp f) ∧
    planeRotation ∈ Y.map ((MulAut.conj a).toMonoidHom.comp f) := by
  have himage : Y.map ((MulAut.conj a).toMonoidHom.comp f) =
      (primeToResidual 3 (stabilizer plane)).map (stabilizer plane).subtype := by
    rw [hY, map_embedded_primeToResidual_of_hom, ← Subgroup.map_map, hP,
      stabilizer_map_conj W a ha]
  rw [himage]
  exact marked_mem_residual

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearModels.PlaneGeometry
