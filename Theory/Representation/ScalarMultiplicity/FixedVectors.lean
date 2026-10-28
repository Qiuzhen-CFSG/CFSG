module
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Theory.SpecificGroups.SL2.OddFixedVectors

/-!
# Fixed vectors of scalar multiplicity actions

A scalar multiplicity action on a tensor product has no nonzero fixed vector
when its multiplicity operator has no fixed vector. Over the binary plane, a
faithful odd order element with an odd annihilating power has no nonzero fixed
vector; this is the F₂ specialization used by the M22 code tensor construction.
-/

public noncomputable section
open scoped TensorProduct MatrixGroups
open Matrix
namespace Representation.ScalarMultiplicity
variable {F E J : Type*} [Field F] [AddCommGroup E] [Module F E]
  [Fintype J] [DecidableEq J]

theorem fixed_eq_zero_of_multiplicity
    (T : Module.End F (J → E)) (μ : Module.End F (J → F))
    (h : ∀ c v, T (fun j => c j • v) = fun j => μ c j • v)
    (hf : ∀ c, μ c = c → c = 0) (x : J → E) (hx : T x = x) : x = 0 := by
  let e := TensorProduct.piScalarRight F F E J
  have he (z : E ⊗[F] (J → F)) :
      e (TensorProduct.map LinearMap.id μ z) = T (e z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simpa [e] using (h c v).symm
    | add z w hz hw => simp only [map_add, hz, hw]
  have hi : Function.Injective (μ - 1 : Module.End F (J → F)) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    exact hf c (sub_eq_zero.mp hc)
  have hti := Module.Flat.lTensor_preserves_injective_linearMap (M := E) (μ - 1) hi
  have hz : e.symm x = 0 := by
    apply hti
    rw [map_zero]
    apply e.injective
    have hm : TensorProduct.map (LinearMap.id : Module.End F E) (μ - 1) =
        TensorProduct.map LinearMap.id μ - 1 := by
      ext v c
      simp [TensorProduct.tmul_sub]
    change e (TensorProduct.map LinearMap.id (μ - 1) (e.symm x)) = e 0
    rw [hm, LinearMap.sub_apply, Module.End.one_apply, map_sub, he,
      e.apply_symm_apply, hx, sub_self, map_zero]
  exact e.symm.injective (hz.trans (map_zero e.symm).symm)

theorem plane_odd_fixed_eq_zero_of_subsingleton_units
    {A : Type*} [Group A] [CharP F 2] [Subsingleton Fˣ]
    (ρ : Representation F A (Fin 2 → F))
    (hi : Function.Injective ρ.asGroupHom)
    (g : A) (m : ℕ) (hm : Odd m) (hg : g ^ m = 1) (hne : g ≠ 1)
    (v : Fin 2 → F) (hv : ρ g v = v) : v = 0 := by
  let f : A →* GL (Fin 2) F :=
    Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp ρ.asGroupHom
  have hf : Function.Injective f := Matrix.GeneralLinearGroup.toLin.symm.injective.comp hi
  have hd : Matrix.GeneralLinearGroup.det (f g) = 1 := Subsingleton.elim _ _
  let a : SL(2, F) := ⟨(f g).val, congrArg Units.val hd⟩
  have he : a.toGL = f g := Units.ext rfl
  have ha : a ^ m = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, he, ←map_pow, hg, map_one, map_one]
  have hna : a ≠ 1 := by
    intro hh
    apply hne
    apply hf
    rw [←he, hh, map_one, map_one]
  apply Matrix.SL2.odd_power_fixed_eq_zero a m hm ha hna
  have hfρ : GeneralLinearGroup.toLin (f g) = ρ.asGroupHom g :=
    GeneralLinearGroup.toLin.apply_symm_apply _
  have hh := congrArg (fun u : LinearMap.GeneralLinearGroup F (Fin 2 → F) =>
    u.val v) hfρ
  change (f g).val *ᵥ v = ρ g v at hh
  exact hh.trans hv
theorem binary_plane_odd_fixed_eq_zero {A : Type*} [Group A]
    (ρ : Representation (ZMod 2) A (Fin 2 → ZMod 2))
    (hi : Function.Injective ρ.asGroupHom)
    (g : A) (m : ℕ) (hm : Odd m) (hg : g ^ m = 1) (hne : g ≠ 1)
    (v : Fin 2 → ZMod 2) (hv : ρ g v = v) : v = 0 := by
  exact plane_odd_fixed_eq_zero_of_subsingleton_units (F := ZMod 2) ρ hi g m hm hg hne v hv

end Representation.ScalarMultiplicity
