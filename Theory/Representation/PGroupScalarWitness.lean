module

public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.GroupTheory.PGroup

/-!
# Scalars in faithful absolutely irreducible prime-group representations

Schur's lemma over the original field makes central elements scalar when the
representation is absolutely irreducible. A nontrivial finite `q`-group has a
central element of order `q`. Faithfulness preserves its order, giving a scalar
of order `q` in the original field, without any descent assumption.

This supplies the scalar step in Aschbacher–Smith, Lemma A.3.21(c),
printed pp. 55–56 of `refs/quasithin.pdf`.
-/

public section

namespace Representation

/-- Central elements act by base-field scalars in an absolutely irreducible
finite-dimensional representation. -/
theorem exists_scalar_of_mem_center_of_absolutelyIrreducible
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (ρ : Representation F G V)
    [IsAbsolutelyIrreducible ρ] (g : G) (hg : g ∈ Subgroup.center G) :
    ∃ a : F, ρ g = a • LinearMap.id := by
  let : IsIrreducible ρ :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible ρ
  obtain ⟨a, ha⟩ := (isAbsolutelyIrreducible_iff_surjective ρ).mp inferInstance
    (RepMap.centralMul ρ g hg)
  exact ⟨a, (congrArg IntertwiningMap.toLinearMap ha).symm⟩

/-- A faithful absolutely irreducible representation of a nontrivial finite
`q`-group contains a base-field scalar of order `q`. -/
theorem exists_scalar_order_prime_of_absolutelyIrreducible
    {F G V : Type*} [Field F] [Group G] [Finite G] [Nontrivial G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [IsAbsolutelyIrreducible ρ]
    (hi : Function.Injective ρ) {q : ℕ} [Fact q.Prime] (hG : IsPGroup q G) :
    ∃ a : Fˣ, orderOf a = q ∧ ∃ g : G, ρ g = (a : F) • LinearMap.id := by
  let : Nontrivial (Subgroup.center G) := hG.center_nontrivial
  have hZ : IsPGroup q (Subgroup.center G) :=
    hG.of_injective (Subgroup.center G).subtype Subtype.val_injective
  obtain ⟨n, hn, hcard⟩ := hZ.nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' q
    (hcard ▸ dvd_pow_self q (Nat.ne_of_gt hn))
  obtain ⟨a, ha⟩ := exists_scalar_of_mem_center_of_absolutelyIrreducible ρ z z.property
  let : IsIrreducible ρ :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible ρ
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hane : a ≠ 0 := by
    intro heq
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    apply (Representation.apply_bijective ρ z).injective
    simp [ha, heq]
  refine ⟨Units.mk0 a hane, ?_, z, ha⟩
  have hscalar : (algebraMap F (Module.End F V)) a = ρ z := ha.symm
  calc
    orderOf (Units.mk0 a hane) = orderOf a :=
      (orderOf_injective (Units.coeHom F) Units.val_injective _).symm
    _ = orderOf ((algebraMap F (Module.End F V)) a) :=
      (orderOf_injective (algebraMap F (Module.End F V)).toMonoidHom
        (algebraMap F (Module.End F V)).injective a).symm
    _ = orderOf (ρ z) := by rw [hscalar]
    _ = orderOf (z : G) := orderOf_injective ρ hi z
    _ = orderOf z := orderOf_injective (Subgroup.center G).subtype Subtype.val_injective z
    _ = q := hz

end Representation
