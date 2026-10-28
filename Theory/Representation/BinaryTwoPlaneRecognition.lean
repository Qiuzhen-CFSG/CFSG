module

public import Theory.SpecificGroups.OrthogonalFourBinary.NonsingularSix
public import Theory.SpecificGroups.OrthogonalFourBinary.TerminalLines
public import Theory.Representation.GoldschmidtONan.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic


/-!
# Recognition from two permuted binary planes

Transport complementary binary planes to the two anisotropic planes of
the specified split quadratic four-space. Its nonsingular vectors are
exactly the nonzero vectors in either plane. Preservation of that union
therefore gives an embedding into the actual isometry group. The original
actor order 72 makes this embedding onto. The resulting equivalences
retain the given linear action on every vector.

Source: Aschbacher–Smith, 14.1.7, printed p.977; the binary quadratic
model is the one specified on printed pp.1121–1122.
-/

public section

open Subgroup OrthogonalFourBinary Theory.AlgebraicGroup
namespace Representation.BinaryTwoPlaneRecognition

private theorem form_eq_one_iff_axes : ∀ x : Space,
    form x = 1 ↔ x ≠ 0 ∧ (x.1 = 0 ∨ x.2 = 0) := by
  decide +kernel

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem exists_isometry_coordinates (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hcard : Nat.card G = 72)
    (A B : Submodule (ZMod 2) V) (hAB : IsCompl A B)
    (hA : Module.finrank (ZMod 2) A = 2) (hB : Module.finrank (ZMod 2) B = 2)
    (hunion : ∀ g v, (ρ g v ∈ A ∨ ρ g v ∈ B) ↔ (v ∈ A ∨ v ∈ B)) :
    ∃ (c : V ≃ₗ[ZMod 2] Space) (e : G ≃* TerminalLines.IsometryGroup),
      ∀ g v, c (ρ g v) = (e g).val (c v) := by
  let a : A ≃ₗ[ZMod 2] Plane :=
    (Module.finBasisOfFinrankEq (ZMod 2) A hA).equivFun.trans (LinearEquiv.finTwoArrow _ _)
  let b : B ≃ₗ[ZMod 2] Plane :=
    (Module.finBasisOfFinrankEq (ZMod 2) B hB).equivFun.trans (LinearEquiv.finTwoArrow _ _)
  let c : V ≃ₗ[ZMod 2] Space :=
    (Submodule.prodEquivOfIsCompl A B hAB).symm.trans (a.prodCongr b)
  have hcA (v : V) : (c v).1 = 0 ↔ v ∈ B := by
    change a (((Submodule.prodEquivOfIsCompl A B hAB).symm v).1) = 0 ↔ _
    rw [a.map_eq_zero_iff, Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero]
  have hcB (v : V) : (c v).2 = 0 ↔ v ∈ A := by
    change b (((Submodule.prodEquivOfIsCompl A B hAB).symm v).2) = 0 ↔ _
    rw [b.map_eq_zero_iff, Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero]
  have hform (v : V) : form (c v) = 1 ↔ v ≠ 0 ∧ (v ∈ A ∨ v ∈ B) := by
    rw [form_eq_one_iff_axes, hcA, hcB, c.map_ne_zero_iff, or_comm]
  have hpres (g : G) (v : V) : form (c (ρ g v)) = form (c v) := by
    apply (by decide +kernel : ∀ x y : ZMod 2, (x = 1 ↔ y = 1) → x = y)
    rw [hform, hform, hunion]
    exact and_congr_left (fun _ => not_congr
      ⟨fun h => GoldschmidtONan.action_injective g (h.trans (map_zero (ρ g)).symm),
        fun h => h ▸ map_zero (ρ g)⟩)
  let φ : G →* (Space ≃ₗ[ZMod 2] Space) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Space).toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv c).toMonoidHom.comp ρ.asGroupHom)
  have hφ (g : G) (w : Space) : φ g w = c (ρ g (c.symm w)) := rfl
  let f : G →* TerminalLines.IsometryGroup := φ.codRestrict _ (by
    intro g
    apply (mem_quadraticIsometrySubgroup form _).mpr
    intro w
    rw [hφ, hpres, c.apply_symm_apply])
  have hfi : Function.Injective f := by
    intro g h he
    apply hf
    apply LinearMap.ext
    intro v
    have hh := congrArg (fun z : TerminalLines.IsometryGroup => z.val (c v)) he
    change φ g (c v) = φ h (c v) at hh
    rw [hφ, hφ, c.symm_apply_apply] at hh
    exact c.injective hh
  have hbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hfi, hcard.trans isometryGroup_card.symm⟩
  refine ⟨c, MulEquiv.ofBijective f hbij, fun g v => ?_⟩
  change c (ρ g v) = φ g (c v)
  rw [hφ, c.symm_apply_apply]

end Representation.BinaryTwoPlaneRecognition
