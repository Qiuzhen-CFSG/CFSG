module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.OrthogonalEight.Model
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.CriticalSubspace

/-!
# Transport and dimension consequences for the orthogonal branch

An equivariant linear identification preserves displacement rank. On an
eight-dimensional binary module, quadratic action and displacement rank at
least four force fixed codimension four, by the inclusions of displacement
space in common fixed space and of common fixed space in each fixed kernel.
The final order-four deduction still takes an actor-order upper bound.

Source: Aschbacher–Smith, 13.8.16(1), printed pp.952–953 (PDF pp.969–970).
-/

public section

open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.OrthogonalEight

section Transport
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (f : H →* G) (e : W ≃ₗ[ZMod 2] V)
    (he : ∀ g w, e (ρ g w) = action (f g) (e w))

omit [FiniteDimensional (ZMod 2) W] in
theorem finrank_of_equivariant_model (e : W ≃ₗ[ZMod 2] V) : Module.finrank (ZMod 2) W = 8 :=
  (LinearEquiv.finrank_eq e).trans finrank_binary

omit [FiniteDimensional (ZMod 2) W] in
theorem displacement_rank_eq (e : W ≃ₗ[ZMod 2] V) (he : ∀ g w, e (ρ g w) = action (f g) (e w)) (g : H) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) =
      Module.finrank (ZMod 2) (LinearMap.range (action (f g) - LinearMap.id)) := by
  have hr : (LinearMap.range (ρ g - LinearMap.id)).map e.toLinearMap =
      LinearMap.range (action (f g) - LinearMap.id) := by
    ext v
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      refine ⟨e w, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub, he]
    · rintro ⟨w, rfl⟩
      refine ⟨(ρ g - (LinearMap.id : W →ₗ[ZMod 2] W)) (e.symm w), ⟨e.symm w, rfl⟩, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub,
        he, LinearEquiv.apply_symm_apply]
  have hd := (Submodule.equivMapOfInjective e.toLinearMap e.injective
    (LinearMap.range (ρ g - LinearMap.id))).finrank_eq
  rwa [hr] at hd

theorem no_critical_line_of_equivariant_rank (e : W ≃ₗ[ZMod 2] V) (he : ∀ g w, e (ρ g w) = action (f g) (e w)) (g : H)
    (hr : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (action (f g) - LinearMap.id)))
    (D S : Submodule (ZMod 2) W)
    (hD : Module.finrank (ZMod 2) (W ⧸ D) ≤ 2)
    (hS : Module.finrank (ZMod 2) S ≤ 1) :
    ¬ ∀ d ∈ D, ρ g d - d ∈ S := by
  apply no_critical_line_of_displacement_rank_four ρ D S g hD hS
  rwa [displacement_rank_eq ρ f e he g]

end Transport

section Quadratic
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W)

theorem quadratic_fixedCodim_eq_four
    (hW : Module.finrank (ZMod 2) W = 8) (A : Subgroup H) (hne : A ≠ ⊥)
    (hq : IsQuadratic ρ A)
    (hr : ∀ a ∈ A, a ≠ 1 →
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id))) :
    fixedCodim ρ A = 4 := by
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let d : W →ₗ[ZMod 2] W := ρ a - LinearMap.id
  have hi : LinearMap.range d ≤ fixedSpace ρ A := by
    rintro _ ⟨v, rfl⟩ b
    exact hq b b.property a a.property v
  have hk : fixedSpace ρ A ≤ LinearMap.ker d := by
    intro v hv
    change ρ a v - v = 0
    exact sub_eq_zero.mpr (hv a)
  have hmin := hr (a : H) a.property (by simpa using ha1)
  have hiD := Submodule.finrank_mono hi
  have hkD := Submodule.finrank_mono hk
  have htotal := d.finrank_range_add_finrank_ker
  have hfixed := fixedCodim_add_finrank ρ A
  change 4 ≤ Module.finrank (ZMod 2) (LinearMap.range d) at hmin
  omega

theorem quadratic_actor_card_four [Finite H]
    (hW : Module.finrank (ZMod 2) W = 8) (A : Subgroup H) (hne : A ≠ ⊥)
    (hq : IsQuadratic ρ A)
    (hr : ∀ a ∈ A, a ≠ 1 →
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)))
    (hcard : Nat.card A ≤ 4) (hoff : fixedCodim ρ A ≤ 2 * rank A) :
    Nat.card A = 4 ∧ fixedCodim ρ A = 4 := by
  have hc := quadratic_fixedCodim_eq_four ρ hW A hne hq hr
  refine ⟨?_, hc⟩
  have hlog : 2 ≤ rank A := by omega
  have hp := Nat.pow_log_le_self 2 (Nat.card_ne_zero.mpr ⟨(show Nonempty A from ⟨⟨1, A.one_mem⟩⟩), inferInstance⟩)
  have hlow : 4 ≤ Nat.card A :=
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hlog).trans hp
  omega

end Quadratic
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.OrthogonalEight
