module

public import Theory.Representation.ConjugateRep
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Tactic

/-!
# Displacement of an actor moving the component commutant

Let a normal subgroup act irreducibly. If an ambient operator T fails to
commute with a component endomorphism f, then Tf-fT is a nonzero intertwiner
from the component representation to its conjugate. Schur's lemma makes this
map injective. On the fixed space of T it is (T-1)f, so that fixed space embeds
in the displacement space. Hence twice the displacement is at least the
ambient dimension.

This argument works over any field, keeps the original operators, and does
not require absolute irreducibility or an involution hypothesis. It supplies
the endomorphism-field-moving branch of the proper-extension argument used in
Guralnick--Malle, *Classification of 2F-modules, II*, Proposition 2.5 and
Lemma 8.6, internal pp.6, 56--57. It does not classify the remaining operators.
-/

@[expose] public section

namespace Representation

/-- The operator commutes with every endomorphism of the restricted representation. -/
def CentralizesCommutant {E H W : Type*} [Field E] [Group H]
    [AddCommGroup W] [Module E W] (σ : Representation E H W) (N : Subgroup H)
    (t : H) : Prop :=
  ∀ (f : IntertwiningMap (σ.comp N.subtype) (σ.comp N.subtype)) (v : W),
    σ t (f v) = f (σ t v)

variable {E H W : Type*} [Field E] [Group H] [AddCommGroup W] [Module E W]
  [FiniteDimensional E W] (σ : Representation E H W) (N : Subgroup H) [N.Normal]
  [IsIrreducible (σ.comp N.subtype)]

/-- A moved component endomorphism forces displacement of at least half the space. -/
theorem finrank_le_twice_displacement_of_not_commuting
    (t : H) (f : IntertwiningMap (σ.comp N.subtype) (σ.comp N.subtype))
    (hf : ∃ v, σ t (f v) ≠ f (σ t v)) :
    Module.finrank E W ≤ 2 * Module.finrank E (LinearMap.range (σ t - LinearMap.id)) := by
  let τ := σ.comp N.subtype
  let τ' := conjugateRep τ t
  have ht (a : N) (v : W) : σ t (σ a v) = τ' a (σ t v) := by
    change σ t (σ a v) = σ (t * (a : H) * t⁻¹) (σ t v)
    simp only [← Module.End.mul_apply, ← map_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  let D : IntertwiningMap τ τ' := {
    toLinearMap := (σ t).comp f.toLinearMap - f.toLinearMap.comp (σ t)
    isIntertwining' := by
      intro a
      ext v
      change σ t (f (σ a v)) - f (σ t (σ a v)) =
        τ' a (σ t (f v) - f (σ t v))
      have hfa (v : W) : f (σ a v) = σ a (f v) :=
        IntertwiningMap.isIntertwining _ _ f a v
      have hfc (v : W) : f (τ' a v) = τ' a (f v) :=
        IntertwiningMap.isIntertwining _ _ f
          ⟨t * (a : H) * t⁻¹, (inferInstance : N.Normal).conj_mem a a.property t⟩ v
      rw [hfa, ht, ht, hfc, map_sub] }
  have hD : D ≠ 0 := by
    obtain ⟨v, hv⟩ := hf
    intro hz
    have he := congrArg (fun g : IntertwiningMap τ τ' => g v) hz
    exact hv (sub_eq_zero.mp he)
  have hi : Function.Injective D := (IsIrreducible.injective_or_eq_zero D).resolve_right hD
  let K := LinearMap.ker (σ t - LinearMap.id)
  let j : K →ₗ[E] LinearMap.range (σ t - LinearMap.id) :=
    ((σ t - LinearMap.id).comp (f.toLinearMap.comp K.subtype)).codRestrict _
      (fun v => ⟨f v, rfl⟩)
  have hj (v : K) : (j v : W) = D v := by
    have hv : σ t (v : W) = v := sub_eq_zero.mp v.property
    change σ t (f v) - f v = σ t (f v) - f (σ t v)
    rw [hv]
  have hji : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply hi
    simpa only [hj] using congrArg Subtype.val hxy
  have hb := LinearMap.finrank_le_finrank_of_injective hji
  have hr := (σ t - LinearMap.id).finrank_range_add_finrank_ker
  change Module.finrank E (LinearMap.ker (σ t - LinearMap.id)) ≤ _ at hb
  omega

/-- The same estimate expressed through the entire component commutant. -/
theorem finrank_le_twice_displacement_of_not_centralizesCommutant
    (t : H) (ht : ¬ CentralizesCommutant σ N t) :
    Module.finrank E W ≤ 2 * Module.finrank E (LinearMap.range (σ t - LinearMap.id)) := by
  classical
  simp only [CentralizesCommutant, not_forall] at ht
  obtain ⟨f, v, hv⟩ := ht
  exact finrank_le_twice_displacement_of_not_commuting σ N t f ⟨v, hv⟩

end Representation
