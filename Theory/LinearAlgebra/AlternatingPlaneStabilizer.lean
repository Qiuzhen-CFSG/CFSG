module

public import Theory.LinearAlgebra.AlternatingDisplacementPair
import Mathlib.Tactic.FinCases

/-!
# Stabilizers of alternating displacement planes

Over the binary field there is at most one nonzero linear displacement with
alternating displacement form and image in a given plane. Conjugating by an
isometry preserving that plane therefore fixes the displacement. Consequently
the corresponding actor commutes with the whole plane stabilizer.

Source application: Aschbacher--Smith, 14.3.30--31, printed pp.1002--1003.
This retains the marked moved plane in the symmetric-five exclusion.
-/

public section
namespace Theory.LinearAlgebra
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [FiniteDimensional (ZMod 2) M]

theorem alternating_plane_maps_unique
    (B : LinearMap.BilinForm (ZMod 2) M) (hND : B.Nondegenerate)
    (P : Submodule (ZMod 2) M) (hP : Module.finrank (ZMod 2) P = 2)
    (N D : M →ₗ[ZMod 2] M) (hN : N ≠ 0) (hD : D ≠ 0)
    (hn : ∀ x, B (N x) x = 0) (hd : ∀ x, B (D x) x = 0)
    (hNP : N.range ≤ P) (hDP : D.range ≤ P) : N = D := by
  classical
  by_contra hne
  let f : Fin 3 → M →ₗ[ZMod 2] M := ![0, N, D]
  have hi : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Ne.symm hN, Ne.symm hD, Ne.symm hne]
  have hc := card_le_two_of_alternating_plane_maps B hND P hP f hi
    (by intro i; fin_cases i <;> simp [f, hn, hd])
    (by intro i; fin_cases i
        · simp [f]
        · exact hNP
        · exact hDP)
  norm_num at hc

theorem alternating_plane_actor_commutes
    (B : LinearMap.BilinForm (ZMod 2) M) (hND : B.Nondegenerate)
    (P : Submodule (ZMod 2) M) (hP : Module.finrank (ZMod 2) P = 2)
    (a s : M ≃ₗ[ZMod 2] M) (ha : a ≠ 1)
    (hAlt : ∀ x, B (a x - x) x = 0)
    (hmove : (a.toLinearMap - LinearMap.id).range ≤ P)
    (hs : ∀ x y, B (s x) (s y) = B x y)
    (hSP : P.map s.toLinearMap ≤ P) : Commute a s := by
  let N := a.toLinearMap - LinearMap.id
  let D := (s.toLinearMap.comp N).comp s.symm.toLinearMap
  have hN : N ≠ 0 := by
    intro hz
    apply ha
    ext x
    exact sub_eq_zero.mp (LinearMap.congr_fun hz x)
  have hD : D ≠ 0 := by
    intro hz
    apply hN
    ext x
    have hh := LinearMap.congr_fun hz (s x)
    change s (N (s.symm (s x))) = 0 at hh
    simpa using s.map_eq_zero_iff.mp (by simpa using hh)
  have hDP : D.range ≤ P := by
    rintro _ ⟨x, rfl⟩
    exact hSP ⟨N (s.symm x), hmove (LinearMap.mem_range_self _ _), rfl⟩
  have hd : ∀ x, B (D x) x = 0 := by
    intro x
    change B (s (N (s.symm x))) x = 0
    rw [← s.apply_symm_apply x, hs]
    simpa only [s.symm_apply_apply, N, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply] using hAlt (s.symm x)
  have he := alternating_plane_maps_unique B hND P hP N D hN hD hAlt hd hmove hDP
  apply LinearEquiv.ext
  intro x
  have hh := LinearMap.congr_fun he (s x)
  change a (s x) - s x = s (a (s.symm (s x)) - s.symm (s x)) at hh
  simpa only [s.symm_apply_apply, map_sub, sub_left_inj, LinearEquiv.mul_apply] using hh
end Theory.LinearAlgebra
