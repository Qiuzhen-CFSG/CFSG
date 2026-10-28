module

public import Theory.SpecificGroups.BinaryLinear.FourParabolicRadical

/-!
# Coordinates on every binary four-space plane radical

An isomorphism of two-dimensional subspaces extends to the whole vector
space. Transporting the checked block shears along that extension identifies
the radical of any supplied plane with the additive two-by-two matrices,
and hence with the elementary abelian group of order sixteen.

Source: Aschbacher–Smith, 15.3.24, second paragraph of the proof,
combined manuscript (1 March 2004), printed p.1129. The concrete shear
calculation is `BinaryLinear.FourParabolicRadical.range_upper`.
-/

public section
open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation.PlaneGeometry

private theorem map_radical {V U : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup U] [Module (ZMod 2) U] (e : V ≃ₗ[ZMod 2] U)
    (W : Submodule (ZMod 2) V) :
    (radical W).map (linearGroupCongr e).toMonoidHom = radical (W.map e.toLinearMap) := by
  ext g
  rw [mem_map_equiv]
  change (∀ w ∈ W, ((linearGroupCongr e).symm g) w = w) ∧
      (∀ v, ((linearGroupCongr e).symm g) v - v ∈ W) ↔ _
  have happly (v : V) : (linearGroupCongr e).symm g v = e.symm (g (e v)) := rfl
  simp_rw [happly]
  constructor
  · rintro ⟨hfix, hmove⟩
    constructor
    · rintro w ⟨v, hv, rfl⟩
      apply e.symm.injective
      change e.symm (g (e v)) = e.symm (e v)
      rw [e.symm_apply_apply]
      exact hfix v hv
    · intro u
      rw [Submodule.mem_map_equiv]
      simpa only [map_sub, e.apply_symm_apply] using hmove (e.symm u)
  · rintro ⟨hfix, hmove⟩
    constructor
    · intro v hv
      rw [hfix (e v) (Submodule.mem_map.mpr ⟨v, hv, rfl⟩), e.symm_apply_apply]
    · intro v
      have hh := hmove (e v)
      rw [Submodule.mem_map_equiv] at hh
      simpa only [map_sub, e.symm_apply_apply] using hh

private def planeEquiv : FourParabolicRadical.plane ≃ₗ[ZMod 2] FourParabolicRadical.Vec where
  toFun v := v.val.1
  invFun v := ⟨(v, 0), by simp [FourParabolicRadical.plane]⟩
  left_inv v := by
    apply Subtype.ext
    change (v.val.1, 0) = v.val
    exact Prod.ext rfl (show v.val.2 = 0 from v.property).symm
  right_inv v := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem exists_plane_coordinates (W : Submodule (ZMod 2) (Space 4))
    (hdim : Module.finrank (ZMod 2) W = 2) :
    ∃ e : FourParabolicRadical.Space ≃ₗ[ZMod 2] Space 4,
      FourParabolicRadical.plane.map e.toLinearMap = W := by
  let e₀ := FourParabolicRadical.spaceEquiv
  let W₀ := FourParabolicRadical.plane.map e₀.toLinearMap
  have hd₀ : Module.finrank (ZMod 2) W₀ = 2 := by
    rw [e₀.finrank_map_eq]
    rw [planeEquiv.finrank_eq]
    exact Module.finrank_fin_fun (ZMod 2)
  let f : W₀ ≃ₗ[ZMod 2] W := LinearEquiv.ofFinrankEq _ _ (hd₀.trans hdim.symm)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨e₀.trans g, ?_⟩
  change FourParabolicRadical.plane.map (g.toLinearMap.comp e₀.toLinearMap) = W
  rw [Submodule.map_comp]
  change W₀.map g.toLinearMap = W
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    change g v ∈ W
    rw [← hg ⟨v, hv⟩]
    exact (f ⟨v, hv⟩).property
  · intro w hw
    obtain ⟨v, hv⟩ := f.surjective ⟨w, hw⟩
    exact ⟨v, v.property, (hg v).symm.trans (congrArg Subtype.val hv)⟩

private def matrixCoordinates : FourParabolicRadical.Mat ≃ₗ[ZMod 2] Space 4 :=
  (show FourParabolicRadical.Mat ≃ₗ[ZMod 2] FourParabolicRadical.Space from
    { toFun := fun A => (A 0, A 1)
      invFun := fun v => ![v.1, v.2]
      left_inv := by intro A; ext i j; fin_cases i <;> rfl
      right_inv := by intro v; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }).trans FourParabolicRadical.spaceEquiv

/-- Every binary plane radical has its full elementary order-sixteen coordinates. -/
noncomputable def radicalCoordinates (W : Submodule (ZMod 2) (Space 4))
    (hdim : Module.finrank (ZMod 2) W = 2) :
    radical W ≃* Multiplicative (Fin 4 → ZMod 2) := by
  let e := Classical.choose (exists_plane_coordinates W hdim)
  have he := Classical.choose_spec (exists_plane_coordinates W hdim)
  let a := (radical FourParabolicRadical.plane).equivMapOfInjective
    (linearGroupCongr e).toMonoidHom (linearGroupCongr e).injective
  have ha : (radical FourParabolicRadical.plane).map (linearGroupCongr e).toMonoidHom =
      radical W := by rw [map_radical, he]
  let b := (MonoidHom.ofInjective FourParabolicRadical.upper_injective).trans
    (MulEquiv.subgroupCongr FourParabolicRadical.range_upper)
  exact ((a.trans (MulEquiv.subgroupCongr ha)).symm.trans b.symm).trans
    matrixCoordinates.toAddEquiv.toMultiplicative

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation.PlaneGeometry
