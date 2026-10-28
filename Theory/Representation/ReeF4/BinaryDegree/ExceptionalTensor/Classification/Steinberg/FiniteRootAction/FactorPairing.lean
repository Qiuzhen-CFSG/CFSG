module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.BasicSpaces
import all Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity

/-!
# The invariant pairing needed by finite Ree irreducibility

Actual algebraic highest-weight uniqueness identifies each basic factor with
its rational dual. This gives an invariant nondegenerate pairing. Composing
with the actual opposition action yields the contravariant short-root pairing;
negative cyclicity forces its value on the highest vector to be nonzero.
The zero weight is handled through the genuine rational trivial factor.

These are the source factor inputs for the finite tensor annihilator argument.
Source: Steinberg (1963), 11.1 and 12.2, with the contravariant pairing of §§2,4.
-/

public section

open Theory.AlgebraicGroup StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open AlgebraicTensor
noncomputable local instance factorPairingRootNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

private theorem zero_action {B : AlgebraicFactor F}
    (hB : Classification.HasBasicHighestWeight B (0,0)) (g : PointGroup F) (x : B.Space) :
    (B.action.action g : Module.End F B.Space) x = x := by
  obtain ⟨e,he⟩ := SourceHighestWeight.equivalent_of_same_basicHighestWeight B trivialFactor (0,0)
    hB trivialFactor_highestWeight
  apply e.injective
  exact he g x

private theorem dual_highest (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    {B : AlgebraicFactor F} (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) :
    HasHighestWeight (ContravariantForm.dualFactor B) (basicCoefficient b) := by
  by_cases hb : b = (0,0)
  · subst b
    obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_eq_one F hv.1
    refine ⟨ℓ, ?_, ?_, ?_⟩
    · intro h
      have he := congrArg (fun f : Module.Dual F B.Space => f v) h
      simp only [hℓ] at he
      exact one_ne_zero he
    · intro r hr t
      apply LinearMap.ext
      intro x
      erw [ContravariantForm.dualFactor_spec B]
      rw [zero_action ⟨v,hv⟩]
    · intro i t
      apply LinearMap.ext
      intro x
      erw [ContravariantForm.dualFactor_spec B]
      rw [zero_action ⟨v,hv⟩]
      change ℓ x = ((t : F) ^ basicCoefficient (0,0) i) * ℓ x
      simp [basicCoefficient]
  · exact ContravariantForm.dualFactor_hasHighestWeight B b p hb hv
      (BasicSpaces.shortNegativeSpan_eq_top hU p hv)

theorem exists_factor_pairing (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    {B : AlgebraicFactor F} (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) :
    ∃ e : B.Space ≃ₗ[F] Module.Dual F B.Space,
      (∀ g x y, e ((B.action.action g : Module.End F B.Space) x)
        ((B.action.action g : Module.End F B.Space) y) = e x y) ∧
      e v ((B.action.action ContravariantForm.oppositionElement : Module.End F B.Space) v) ≠ 0 := by
  obtain ⟨e,he⟩ := SourceHighestWeight.equivalent_of_same_highestWeight
    B (ContravariantForm.dualFactor B) (basicCoefficient b) ⟨v,hv⟩ (dual_highest hU p hv)
  let E₀ : B.Space ≃ₗ[F] Module.Dual F B.Space := e
  change Intertwines B.action (ContravariantForm.dualFactor B).action E₀.toLinearMap at he
  have hinv (g : PointGroup F) (x y : B.Space) :
      E₀ ((B.action.action g : Module.End F B.Space) x)
        ((B.action.action g : Module.End F B.Space) y) = E₀ x y := by
    have hh := he g x
    change E₀ ((B.action.action g : Module.End F B.Space) x) = _ at hh
    rw [hh]
    erw [ContravariantForm.dualFactor_spec B]
    congr 1
    simp only [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, inv_mul_cancel,
      map_one, Units.val_one, Module.End.one_apply]
  refine ⟨E₀,hinv,?_⟩
  let n : PointGroup F := ContravariantForm.oppositionElement
  let N := LinearMap.GeneralLinearGroup.generalLinearEquiv F B.Space (B.action.action n)
  let E : B.Space ≃ₗ[F] Module.Dual F B.Space := E₀.trans N.dualMap
  have hcontra : ∀ (r : ShortPositiveRoot) (x y : B.Space),
      E (p.coeff r.val 1 x) y = E x (p.coeff (-r.val) 1 y) := by
    intro r x y
    apply p.coeff_one_adjoint_of_root_adjoint E.toLinearMap r.val (-r.val) _ x y
    intro t a d
    change E₀ ((B.action.action (algebraicRootElement r.val t) : Module.End F B.Space) a)
      (N d) = E₀ a (N ((B.action.action (algebraicRootElement (-r.val) t) : Module.End F B.Space) d))
    have hh := he (algebraicRootElement r.val t) a
    change E₀ ((B.action.action (algebraicRootElement r.val t) : Module.End F B.Space) a) = _ at hh
    rw [hh]
    erw [ContravariantForm.dualFactor_spec B]
    rw [ContravariantForm.algebraicRootElement_inv]
    congr 1
    change (B.action.action (algebraicRootElement r.val t) : Module.End F B.Space)
      ((B.action.action n : Module.End F B.Space) d) =
      (B.action.action n : Module.End F B.Space)
        ((B.action.action (algebraicRootElement (-r.val) t) : Module.End F B.Space) d)
    have hc := congrArg (fun g => (B.action.action g : Module.End F B.Space) d)
      (ContravariantForm.root_opposition_commute r.val t)
    simpa only [map_mul, Units.val_mul, Module.End.mul_apply] using hc
  intro hz
  exact hv.1 (p.primitive_eq_zero_of_pairing_highest_eq_zero v
    (BasicSpaces.shortNegativeSpan_eq_top hU p hv) E.toLinearMap E.injective hcontra
    (p.highest_mem_shortPositiveKernel hv) hz)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
