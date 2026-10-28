module
public import Theory.Representation.SL2NaturalFirstCohomology.FourOuter
import Mathlib.Tactic.Ring

/-!
# Contragredient transport of the Frobenius cohomology bound

The trace-determinant self-duality identifies the contragredient with the same
natural SL₂(4) module and retains its marking. The pairing is balanced over F₄:
moving an F₄ scalar from either argument to the other does not change it.
Consequently the contragredient of a Frobenius-semilinear involution is again
Frobenius-semilinear in these coordinates. Transport on H¹ then gives the
binary dimension bound for the actual contragredient representation.

Application: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(3) and J.2.5, printed pp.432 and 434 (PDF pp.443 and 445).
-/

@[expose] public section
noncomputable section
namespace Representation.SL2NaturalH1.FourOuter
open Representation.OneCohomology SL2FourNatural
variable {G : Type*} [Group G]

/-- Transport the contragredient back to the natural binary coordinates. -/
def dualCoordinates (ρ : Representation (ZMod 2) G V) : Representation (ZMod 2) G V :=
  selfDual.symm.conjRingEquiv.toMonoidHom.comp ρ.dual

lemma dualCoordinates_apply (ρ : Representation (ZMod 2) G V) (g : G) (v : V) :
    dualCoordinates ρ g v = selfDual.symm (ρ.dual g (selfDual v)) := rfl

lemma dualCoordinates_restriction (ρ : Representation (ZMod 2) G V)
    (ι : SL →* G) (hr : ∀ g v, ρ (ι g) v = action g v) (g : SL) (v : V) :
    dualCoordinates ρ (ι g) v = action g v := by
  apply selfDual.injective
  rw [dualCoordinates_apply, selfDual.apply_symm_apply, selfDual_equivariant]
  apply LinearMap.ext
  intro w
  change selfDual v (ρ (ι g)⁻¹ w) = selfDual v (action g⁻¹ w)
  rw [← map_inv ι, hr]

lemma pairing_balanced (a : F) (v w : V) : selfDual (a • v) w = selfDual v (a • w) := by
  change QuadraticAlgebra.trace (wedge (a • v) w) = QuadraticAlgebra.trace (wedge v (a • w))
  congr 1
  simp only [wedge, Pi.smul_apply, smul_eq_mul]
  ring

lemma dualCoordinates_semilinear (ρ : Representation (ZMod 2) G V)
    (t : G) (ht : t * t = 1)
    (hs : ∀ (a : F) (v : V), ρ t (a • v) = fieldFrobenius a • ρ t v)
    (a : F) (v : V) :
    dualCoordinates ρ t (a • v) = fieldFrobenius a • dualCoordinates ρ t v := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  apply selfDual.injective
  rw [dualCoordinates_apply, selfDual.apply_symm_apply]
  apply LinearMap.ext
  intro w
  change selfDual (a • v) (ρ t⁻¹ w) =
    selfDual (fieldFrobenius a • dualCoordinates ρ t v) w
  rw [hti, pairing_balanced, pairing_balanced, dualCoordinates_apply]
  rw [selfDual.apply_symm_apply]
  change selfDual v (a • ρ t w) = selfDual v (ρ t⁻¹ (fieldFrobenius a • w))
  rw [hti, hs, fieldFrobenius_involutive]

/-- The same bound holds for the contragredient, with the original marking retained. -/
theorem finrank_dual_le_one [Finite G] (ρ : Representation (ZMod 2) G V)
    (ι : SL →* G) (hr : ∀ g v, ρ (ι g) v = action g v)
    (hn : ∀ (g : G) (x : SL), ∃ y : SL, ι x * g = g * ι y)
    (t : G) (ht : t * t = 1) (σ : SL →* SL)
    (hc : ∀ g, t * ι (σ g) = ι g * t)
    (hs : ∀ (a : F) (v : V), ρ t (a • v) = fieldFrobenius a • ρ t v) :
    Module.finrank (ZMod 2) (H1 ρ.dual) ≤ 1 := by
  have hb := finrank_le_one
    (dualCoordinates ρ) ι (dualCoordinates_restriction ρ ι hr) t σ hc
    (dualCoordinates_semilinear ρ t ht hs) hn
  let e := H1Congr (dualCoordinates ρ) ρ.dual (MulEquiv.refl G) selfDual
    (by intro g v; simp only [dualCoordinates_apply, selfDual.apply_symm_apply, MulEquiv.refl_apply])
  rw [← e.finrank_eq]
  exact hb
end Representation.SL2NaturalH1.FourOuter
