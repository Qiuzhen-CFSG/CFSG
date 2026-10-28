module
public import Theory.Representation.QuadraticFourGroup.CubicSections.FixedSpace
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.ElementaryAbelian.Basic

/-!
# Binary quotients of a fixed-free cubic action

Coprime fixed-point lifting shows that a quotient of a fixed-point-free
operator of exponent three is again fixed-point-free. Its binary dimension
is even, since the nontrivial irreducible cubic action has degree two.

Source application: Aschbacher--Smith 13.7.4(1), printed p.938.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- Every equivariant quotient of a fixed-free cubic action has even binary dimension. -/
theorem even_finrank_of_fixedFree_cubic_quotient
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (z : G) (hz : z ^ 3 = 1) (hfix : ∀ v, ρ z v = v → v = 0) :
    Even (Module.finrank (ZMod 2) W) := by
  have hfixed : ∀ w, σ z w = w → w = 0 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Representation.QuadraticFourGroup.exists_cubic_fixed_lift f hf hz hw
    rw [hfix v hv, map_zero]
  let P := zpowers z
  have hP : IsPGroup 3 P :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 3) hz).isPGroup 3 P
  have hzero : Representation.invariants (σ.comp P.subtype) = ⊥ := by
    apply bot_unique
    intro w hw
    exact hfixed w (hw ⟨z, mem_zpowers z⟩)
  have hh := orderOf_two_dvd_finrank_of_isPGroup (σ.comp P.subtype)
    Nat.prime_three (by decide) hP hzero
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_three] at hh
  exact even_iff_two_dvd.mpr hh
end Representation.BinaryOffender
