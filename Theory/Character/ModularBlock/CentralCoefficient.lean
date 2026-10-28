module

public import Theory.Character.Orthogonality
public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Central coefficients from irreducible scalar actions

For a finite group, a central complex group-algebra element is recovered
from its scalar actions on a complete family of irreducible representations.
The coefficient-at-inverse function is a class function. Its inner product
with an irreducible character is the normalized trace of the central
element, so expansion in the character basis gives the coefficient formula.

This is the character-theoretic input to Feit IV.7.1 and to the principal
block selector's idempotence. Ported from
`public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BlockOrthogonality.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock.BlockOrthogonality

attribute [local instance] Fintype.ofFinite

universe u v

/-- A central group-algebra element gives a class function by taking the
coefficient of the inverse element. -/
private noncomputable def coeffInvClassFunction
    {G : Type u} [Group G] [Finite G]
    (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a) :
    ConjClassFunction G :=
  conjClassFunctionOfInvariant (fun g : G => z.coeff g⁻¹) (by
    intro g h
    have heq := congrArg (fun q : MonoidAlgebra ℂ G => q.coeff (h * g⁻¹))
      (hz (MonoidAlgebra.single h (1 : ℂ)))
    simpa [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
      mul_assoc] using heq.symm)

@[simp] private theorem coeffInvClassFunction_mk
    {G : Type u} [Group G] [Finite G]
    (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a)
    (g : G) :
    coeffInvClassFunction z hz (ConjClasses.mk g) = z.coeff g⁻¹ := rfl

/-- The trace of a group-algebra action is the coefficient-weighted
sum of its representation character. -/
theorem groupAlgebra_trace
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (z : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom z) =
      ∑ g : G, z.coeff g * ρ.character g := by
  classical
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      change (∑ g : G, x.coeff g * ρ.character g) +
          (∑ g : G, y.coeff g * ρ.character g) =
        ∑ g : G, (x.coeff g + y.coeff g) * ρ.character g
      simp only [add_mul, Finset.sum_add_distrib]
  | single g r =>
      have hmap :
          ρ.asAlgebraHom (MonoidAlgebra.single g r) = r • ρ g := by
        rw [show (MonoidAlgebra.single g r : MonoidAlgebra ℂ G) =
          r • MonoidAlgebra.single g 1 by simp, map_smul,
          Representation.asAlgebraHom_single_one]
      rw [hmap, map_smul]
      change r * ρ.character g =
        ∑ x : G, (MonoidAlgebra.single g r).coeff x * ρ.character x
      rw [Finset.sum_eq_single g]
      · change r * ρ.character g = (Finsupp.single g r) g * ρ.character g
        simp
      · intro x _hx hxg
        change (Finsupp.single g r) x * ρ.character x = 0
        simp [hxg]
      · simp

private theorem inner_coeffInv_eq
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a)
    (lambda : ℂ)
    (haction : ρ.asAlgebraHom z = lambda • (1 : Module.End ℂ V)) :
    classFunctionInner (coeffInvClassFunction z hz)
        (characterClassFunction ρ) =
      (Nat.card G : ℂ)⁻¹ *
        (lambda * ρ.character 1) := by
  classical
  have hinvsum :
      (∑ g : G, z.coeff g⁻¹ * star (ρ.character g)) =
        ∑ g : G, z.coeff g * ρ.character g := by
    let f : G → ℂ := fun g => z.coeff g * ρ.character g
    calc
      (∑ g : G, z.coeff g⁻¹ * star (ρ.character g)) =
          ∑ g : G, f g⁻¹ := by
            apply Finset.sum_congr rfl
            intro g _hg
            simp only [f]
            rw [Representation.representation_character_inv_eq_star_character]
      _ = ∑ g : G, f g := Equiv.sum_comp (Equiv.inv G) f
      _ = ∑ g : G, z.coeff g * ρ.character g := rfl
  rw [classFunctionInner]
  change (Nat.card G : ℂ)⁻¹ *
      (∑ g : G, z.coeff g⁻¹ * star (ρ.character g)) = _
  rw [hinvsum, ← groupAlgebra_trace ρ z, haction, map_smul]
  simp [Representation.character]

/-- Recover the coefficient of a central group-algebra element from the
scalars by which it acts on a complete family of irreducibles.  This is the
abstract coefficient formula behind Feit IV.7.1. -/
theorem coeff_eq_inv_card_mul_sum_scalar_degree_character
    {G : Type u} [Group G] [Finite G]
    {I : Type v} [Fintype I] [DecidableEq I]
    (chi : I → ConjClassFunction G)
    (hchi : IsCompleteIrreducibleCharacterFamily chi)
    (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a)
    (lambda : I → ℂ)
    (haction : ∀ i : I, ∀ {n : ℕ}
      (ρ : Representation ℂ G (Fin n → ℂ)),
      chi i = (characterClassFunction ρ) →
      ρ.asAlgebraHom z = lambda i • (1 : Module.End ℂ (Fin n → ℂ)))
    (g : G) :
    z.coeff g = (Nat.card G : ℂ)⁻¹ *
      ∑ i : I, lambda i * chi i (ConjClasses.mk (1 : G)) *
        chi i (ConjClasses.mk g⁻¹) := by
  classical
  let phi : ConjClassFunction G := coeffInvClassFunction z hz
  have hinner (i : I) :
      classFunctionInner phi (chi i) =
        (Nat.card G : ℂ)⁻¹ *
          (lambda i * chi i (ConjClasses.mk (1 : G))) := by
    rcases (hchi.1 i).1 with ⟨n, ρ, hρ⟩
    rw [hρ]
    exact inner_coeffInv_eq ρ z hz (lambda i) (haction i ρ hρ)
  have hexpand :=
    completeFamily_apply_eq_sum_inner hchi phi
      (ConjClasses.mk g⁻¹)
  change z.coeff (g⁻¹)⁻¹ =
      ∑ i : I, classFunctionInner phi (chi i) *
        chi i (ConjClasses.mk g⁻¹) at hexpand
  rw [inv_inv] at hexpand
  rw [hexpand]
  simp_rw [hinner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

end ModularBlock.BlockOrthogonality
