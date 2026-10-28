module
public import Theory.FieldTheory.QuadraticUnitAction
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Eliminating a quadratic field factor on the original Hall subgroup

Mutually normalizing subgroups give commutators in their intersection. If
the Hall subgroup is abelian, its elements fix those commutators. A surjective
field-unit marking of the torus therefore makes the field automorphism act
quadratically on every unit. The characteristic-two field calculation forces
that automorphism to be identity.

Source: Aschbacher–Smith, proof of 10.2.3(4), printed pp.745–746. The component and
normalization arguments producing the two relative normalizer inclusions
remain with the moving-Hall assembly owner; no Hall placement is assumed.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter10.MovingHall

/-- A field action compatible with the original torus conjugation is trivial
when the abelian actor and torus normalize each other. -/
theorem field_factor_eq_one {G F : Type*} [Group G] [Field F] [CharP F 2]
    (D B : Subgroup G) [IsMulCommutative B]
    (hBD : B ≤ normalizer (D : Set G))
    (hDB : D ≤ normalizer (B : Set G))
    (q : D →* Fˣ) (hq : Function.Surjective q)
    (b : B) (σ : F ≃+* F)
    (he : ∀ d : D, q (D.normalizerMonoidHom (inclusion hBD b) d) =
      Units.map σ.toMonoidHom (q d)) : σ = 1 := by
  apply RingEquiv.eq_one_of_quadratic_units
  intro u
  obtain ⟨d,rfl⟩ := hq u
  let α := D.normalizerMonoidHom (inclusion hBD b)
  let δ : D := α d * d⁻¹
  have hδB : (δ : G) ∈ B :=
    (le_normalizer_iff_commutator_le_left.mp hDB)
      (commutator_mem_commutator b.property d.property)
  have hfix : α δ = δ := by
    apply Subtype.ext
    change (b : G) * (δ : G) * (b : G)⁻¹ = (δ : G)
    have hc : (b : G) * (δ : G) = (δ : G) * (b : G) :=
      congrArg Subtype.val (mul_comm b (⟨δ,hδB⟩ : B))
    rw [hc, mul_inv_cancel_right]
  have hqδ : q δ = Units.map σ.toMonoidHom (q d) * (q d)⁻¹ := by
    change q (α d * d⁻¹) = _
    rw [map_mul,map_inv,he]
  rw [← hqδ, ← he, hfix]

end CFSG.Quasithin.Chapter10.MovingHall
