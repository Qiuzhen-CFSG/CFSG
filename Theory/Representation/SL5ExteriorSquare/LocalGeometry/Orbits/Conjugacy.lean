module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Involutions

/-!
# Displacement ranks and separation of the two binary SL₅ involution classes

Conjugation carries the displacement image by the corresponding invertible
linear action. Thus both natural and exterior displacement ranks are invariant.
Their computed values distinguish the two marked representatives and give the
source rank conclusions for every member of their respective conjugacy classes.
For an arbitrary nonidentity involution, square-zero natural displacement puts
its image inside its kernel, so rank-nullity bounds its positive rank by two.
This does not yet construct the Jordan basis needed for conjugacy exhaustion.

Source: Aschbacher–Smith, 12.5.5(1), printed p.819/PDF p.836.
-/

@[expose] public section

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

private noncomputable def actionEquiv {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Group W) (g : Group) : W ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
    (by change ρ g * ρ g⁻¹ = 1; rw [← map_mul, mul_inv_cancel, map_one])
    (by change ρ g⁻¹ * ρ g = 1; rw [← map_mul, inv_mul_cancel, map_one])

private theorem representation_range_conj {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) Group W) (h g : Group) :
    LinearMap.range (ρ (h * g * h⁻¹) - LinearMap.id) =
      (LinearMap.range (ρ g - LinearMap.id)).map (actionEquiv ρ h).toLinearMap := by
  have cancel (a : Group) (x : W) : ρ a (ρ a⁻¹ x) = x := by
    change (ρ a * ρ a⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨(ρ g (ρ h⁻¹ v) - ρ h⁻¹ v), ⟨ρ h⁻¹ v, rfl⟩, ?_⟩
    change ρ h (ρ g (ρ h⁻¹ v) - ρ h⁻¹ v) = ρ (h * g * h⁻¹) v - v
    simp only [map_sub, map_mul, Module.End.mul_apply, cancel]
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨ρ h v, ?_⟩
    change ρ (h * g * h⁻¹) (ρ h v) - ρ h v = ρ h (ρ g v - v)
    have hc : ρ h⁻¹ (ρ h v) = v := by
      have hi := cancel h⁻¹ v
      rwa [inv_inv] at hi
    simp only [map_mul, Module.End.mul_apply, hc, map_sub]

private theorem representation_finrank_conj {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) Group W) (h g : Group) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ (h * g * h⁻¹) - LinearMap.id)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) := by
  rw [representation_range_conj, LinearEquiv.finrank_map_eq]

theorem finrank_displacement_conj (h g : Group) :
    Module.finrank (ZMod 2) (LinearMap.range (displacement (h * g * h⁻¹))) =
      Module.finrank (ZMod 2) (LinearMap.range (displacement g)) :=
  representation_finrank_conj (exteriorAction 2) h g

theorem finrank_naturalDisplacement_conj (h g : Group) :
    Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement (h * g * h⁻¹))) =
      Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement g)) :=
  representation_finrank_conj (specialLinearNatural 5) h g

theorem finrank_displacement_eq_of_isConj {g h : Group} (hc : IsConj g h) :
    Module.finrank (ZMod 2) (LinearMap.range (displacement g)) =
      Module.finrank (ZMod 2) (LinearMap.range (displacement h)) := by
  obtain ⟨a, rfl⟩ := isConj_iff.mp hc
  exact (finrank_displacement_conj a g).symm

theorem finrank_naturalDisplacement_eq_of_isConj {g h : Group} (hc : IsConj g h) :
    Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement g)) =
      Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement h)) := by
  obtain ⟨a, rfl⟩ := isConj_iff.mp hc
  exact (finrank_naturalDisplacement_conj a g).symm

theorem not_isConj_j₁_j₂ : ¬ IsConj j₁ j₂ := by
  intro h
  have hr := finrank_naturalDisplacement_eq_of_isConj h
  rw [finrank_naturalDisplacement_j₁, finrank_naturalDisplacement_j₂] at hr
  omega

theorem involution_classes_disjoint (g : Group) : ¬ (IsConj j₁ g ∧ IsConj j₂ g) := by
  rintro ⟨h₁, h₂⟩
  exact not_isConj_j₁_j₂ (h₁.trans h₂.symm)

theorem naturalDisplacement_square_zero {g : Group} (hg : g * g = 1)
    (v : Fin 5 → ZMod 2) : naturalDisplacement g (naturalDisplacement g v) = 0 := by
  have hgg : specialLinearNatural 5 g (specialLinearNatural 5 g v) = v := by
    change (specialLinearNatural 5 g * specialLinearNatural 5 g) v = v
    rw [← map_mul, hg, map_one]
    rfl
  change specialLinearNatural 5 g (specialLinearNatural 5 g v - v) -
    (specialLinearNatural 5 g v - v) = 0
  rw [map_sub, hgg]
  calc
    v - specialLinearNatural 5 g v - (specialLinearNatural 5 g v - v) =
        (v + v) - (specialLinearNatural 5 g v + specialLinearNatural 5 g v) := by abel
    _ = 0 := by rw [ZModModule.add_self, ZModModule.add_self, sub_self]

theorem finrank_naturalDisplacement_le_two {g : Group} (hg : g * g = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement g)) ≤ 2 := by
  have hk : LinearMap.range (naturalDisplacement g) ≤ LinearMap.ker (naturalDisplacement g) := by
    rintro x ⟨v, rfl⟩
    exact naturalDisplacement_square_zero hg v
  have he := LinearMap.finrank_range_add_finrank_ker (naturalDisplacement g)
  have hm := Submodule.finrank_mono hk
  have hd : Module.finrank (ZMod 2) (Fin 5 → ZMod 2) = 5 := by simp
  omega

theorem naturalDisplacement_eq_zero_iff (g : Group) : naturalDisplacement g = 0 ↔ g = 1 := by
  rw [naturalDisplacement, sub_eq_zero]
  constructor
  · intro h
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.toLinearMap_injective
    change specialLinearNatural 5 g = specialLinearNatural 5 1
    rw [map_one]
    exact h
  · rintro rfl
    exact map_one _

theorem finrank_naturalDisplacement_one_or_two {g : Group} (hg : g * g = 1)
    (hne : g ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement g)) = 1 ∨
      Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement g)) = 2 := by
  have hle := finrank_naturalDisplacement_le_two hg
  have hpos : Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement g)) ≠ 0 := by
    intro h
    apply hne
    apply (naturalDisplacement_eq_zero_iff g).mp
    exact LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)
  omega

theorem ranks_of_isConj_j₁ {g : Group} (h : IsConj j₁ g) :
    Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement g)) = 1 ∧
    Module.finrank (ZMod 2) (LinearMap.range (displacement g)) = 3 := by
  exact ⟨(finrank_naturalDisplacement_eq_of_isConj h).symm.trans finrank_naturalDisplacement_j₁,
    (finrank_displacement_eq_of_isConj h).symm.trans finrank_displacement_j₁⟩

theorem ranks_of_isConj_j₂ {g : Group} (h : IsConj j₂ g) :
    Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement g)) = 2 ∧
    Module.finrank (ZMod 2) (LinearMap.range (displacement g)) = 4 := by
  exact ⟨(finrank_naturalDisplacement_eq_of_isConj h).symm.trans finrank_naturalDisplacement_j₂,
    (finrank_displacement_eq_of_isConj h).symm.trans finrank_displacement_j₂⟩

end Representation.SL5ExteriorSquare
