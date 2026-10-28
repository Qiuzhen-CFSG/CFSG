module

public import Theory.Representation.PSL3Two.SmallModules
public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces.Certificates
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Fixed vectors of a binary transvection on the natural plus dual module

Every nonidentity involution in SL₃(2) is conjugate to I + E₀₂. Its
natural and contragredient fixed planes together have sixteen elements.
The dot-product equivalence identifies the literal dual with row vectors;
representation operators transport the standard matrix calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.58
and the first paragraph proving 15.3.61(2), printed pp.1148–1150.
-/

@[expose] public section

open Matrix BinaryLinearThree
namespace BinaryLinearThree.TransvectionFixed
/-- The natural binary three-space and its actual linear dual. -/
abbrev Space := Vector × Module.Dual (ZMod 2) Vector
/-- The simultaneous natural and contragredient action. -/
noncomputable abbrev action := W.prod W.dual

/-- Fixed vectors for one matrix actor. -/
def Fixed (g : Group) := {w : Space // action g w = w}

private theorem dual_fixed_iff (g : Group) (hg : g * g = 1) (d : Vector) :
    W.dual g (dotProductEquiv (ZMod 2) (Fin 3) d) = dotProductEquiv (ZMod 2) (Fin 3) d ↔
      d ᵥ* g.val = d := by
  have hi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have he : W.dual g (dotProductEquiv (ZMod 2) (Fin 3) d) =
      dotProductEquiv (ZMod 2) (Fin 3) (d ᵥ* g.val) := by
    apply LinearMap.ext
    intro w
    change d ⬝ᵥ (g⁻¹.val *ᵥ w) = (d ᵥ* g.val) ⬝ᵥ w
    rw [hi, Matrix.dotProduct_mulVec]
  rw [he]
  exact (dotProductEquiv (ZMod 2) (Fin 3)).injective.eq_iff

private theorem standard_card :
    Nat.card (Fixed FourGroupGeometry.FixedSpaces.involution) = 16 := by
  let τ := FourGroupGeometry.FixedSpaces.involution
  let e : (Vector × Vector) ≃ Space :=
    (Equiv.refl Vector).prodCongr (dotProductEquiv (ZMod 2) (Fin 3)).toEquiv
  have he (w : Vector × Vector) : FourGroupGeometry.FixedSpaces.fixes τ w ↔
      action τ (e w) = e w := by
    change (_ ∧ _) ↔ (W τ w.1, W.dual τ (dotProductEquiv (ZMod 2) (Fin 3) w.2)) =
      (w.1, dotProductEquiv (ZMod 2) (Fin 3) w.2)
    rw [Prod.mk.injEq, dual_fixed_iff τ (by decide)]
    rfl
  let e' : {w : Vector × Vector // FourGroupGeometry.FixedSpaces.fixes τ w} ≃ Fixed τ :=
    e.subtypeEquiv he
  rw [← Nat.card_congr e', Nat.card_eq_fintype_card]
  decide +kernel

/-- An inner involution fixes a four-dimensional space in the natural plus dual module. -/
theorem card_fixed (g : Group) (hg : g ≠ 1) (hsq : g * g = 1) :
    Nat.card (Fixed g) = 16 := by
  obtain ⟨k, hk⟩ := FourGroupGeometry.FixedSpaces.exists_involution_conjugator g hg hsq
  let τ := FourGroupGeometry.FixedSpaces.involution
  let e : Space ≃ₗ[ZMod 2] Space := LinearEquiv.ofBijective (action k) (action.apply_bijective k)
  have he (w : Space) : action τ w = w ↔ action g (e w) = e w := by
    have heq : action g (e w) = e (action τ w) := by
      change action g (action k w) = action k (action τ w)
      rw [← Module.End.mul_apply, ← map_mul, hk, map_mul, Module.End.mul_apply]
    rw [heq]
    exact e.injective.eq_iff.symm
  exact (Nat.card_congr (e.toEquiv.subtypeEquiv he)).symm.trans standard_card
/-- The same fixed space with its multiplicative elementary-abelian structure. -/
noncomputable def fixedSubgroup (g : Group) : Subgroup (Multiplicative Space) :=
  (action g).toAddMonoidHom.toMultiplicative.eqLocus (MonoidHom.id _)

/-- Fixedness is the actual natural and contragredient action equation. -/
theorem mem_fixedSubgroup (g : Group) (w : Multiplicative Space) :
    w ∈ fixedSubgroup g ↔ action g w.toAdd = w.toAdd := Iff.rfl

end BinaryLinearThree.TransvectionFixed
