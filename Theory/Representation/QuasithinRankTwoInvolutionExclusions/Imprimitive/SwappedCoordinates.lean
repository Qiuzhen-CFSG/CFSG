module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.Split
public import Mathlib.LinearAlgebra.Projection

/-!
# Coordinates from an actual exchanged submodule

If an involution t exchanges complementary submodules P and tP, the map
(v,w) ↦ v + t w identifies P × P with the original space. This identification
makes t the plain coordinate swap. An operator commuting with t has its second
block determined by its restriction to P. Displacement ranks then double for
diagonal operators, and an exchanging involution moves one full summand.

These constructions supply the coordinate changes, rather than assumptions
about coordinates, for Aschbacher–Smith G.11.2(8),(12), printed p.364/PDF p.375,
and their exclusions in 6.2.19, printed p.691/PDF p.708.
-/

@[expose] public section

namespace Representation.RankTwo.Imprimitive
variable {k V U : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup U] [Module k U]

noncomputable def swappedCoordinates (t : Module.End k V) (ht : t * t = 1)
    (P : Submodule k V) (hP : IsCompl P (P.map t)) : (P × P) ≃ₗ[k] V :=
  ((LinearEquiv.refl k P).prodCongr (Submodule.equivMapOfInjective t
    (Function.LeftInverse.injective (fun v => LinearMap.congr_fun ht v)) P)).trans
    (P.prodEquivOfIsCompl (P.map t) hP)

@[simp] theorem swappedCoordinates_apply (t : Module.End k V) (ht : t * t = 1)
    (P : Submodule k V) (hP : IsCompl P (P.map t)) (v w : P) :
    swappedCoordinates t ht P hP (v,w) = (v : V) + t w := rfl

theorem swappedCoordinates_swap (t : Module.End k V) (ht : t * t = 1)
    (P : Submodule k V) (hP : IsCompl P (P.map t)) (v w : P) :
    t (swappedCoordinates t ht P hP (v,w)) = swappedCoordinates t ht P hP (w,v) := by
  rw [swappedCoordinates_apply, map_add, show t (t w) = w from LinearMap.congr_fun ht w,
    swappedCoordinates_apply, add_comm]

/-- Commutation with the exchanging involution determines the second block
from the action on the first submodule. -/
theorem action_swappedCoordinates (t : Module.End k V) (ht : t * t = 1)
    (P : Submodule k V) (hP : IsCompl P (P.map t))
    (b : Module.End k V) (a : Module.End k P) (hbt : Commute b t)
    (ha : ∀ v : P, b v = a v) (v w : P) :
    b (swappedCoordinates t ht P hP (v,w)) =
      swappedCoordinates t ht P hP (a v,a w) := by
  have hc (z : V) : b (t z) = t (b z) := LinearMap.congr_fun hbt.eq z
  rw [swappedCoordinates_apply, map_add, hc, ha, ha, swappedCoordinates_apply]

/-- Coordinates intertwining a block operator preserve its moved-space rank. -/
theorem finrank_of_block_coordinates [FiniteDimensional k U]
    (f : (U × U) ≃ₗ[k] V) (b : Module.End k V) (a : Module.End k U)
    (hf : ∀ v w, b (f (v,w)) = f (a v,a w)) :
    Module.finrank k (LinearMap.range (b - 1)) =
      2 * Module.finrank k (LinearMap.range (a - 1)) := by
  have he := (displacementRangeEquiv f (a.prodMap a) b
    (fun z => hf z.1 z.2)).finrank_eq
  rw [finrank_block] at he
  omega

/-- An exchanging involution moves one full summand, in arbitrary coordinates. -/
theorem finrank_of_exchanging_coordinates
    (f : (U × U) ≃ₗ[k] V) (b : Module.End k V) (a c : Module.End k U)
    (hf : ∀ v w, b (f (v,w)) = f (c w,a v)) (hb : b * b = 1) :
    Module.finrank k (LinearMap.range (b - 1)) = Module.finrank k U := by
  let d := f.symm.conjRingEquiv b
  have hd : ∀ v w, d (v,w) = (c w,a v) := by
    intro v w
    change f.symm (b (f (v,w))) = _
    rw [hf, f.symm_apply_apply]
  have hd2 : d * d = 1 := by
    change f.symm.conjRingEquiv b * f.symm.conjRingEquiv b = 1
    rw [← map_mul, hb, map_one]
  have he := (displacementRangeEquiv f d b (fun z => by
    change b (f z) = f (f.symm (b (f z)))
    rw [f.apply_symm_apply])).finrank_eq
  exact he.symm.trans (finrank_of_exchanges d a c hd hd2)
end Representation.RankTwo.Imprimitive