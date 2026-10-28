module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.TensorStep.PolynomialExpansion

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.HighestLine.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Cartan

/-!
# Cartan stability on the actual simple differential quotient

The Cartan/root identity for the original rational factor passes through its
root algebra and the actual quotient algebra action. It implies stability of
the sum of all negative-root images, independently of a highest-weight choice.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §2, equation 2.4; DOI 10.1017/S0027763000011016.
-/


public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

namespace SimpleCyclicQuotient
variable {B : AlgebraicFactor F} {v : B.Space} (Q : SimpleCyclicQuotient B v)

private def cartanGenerator (i : Fin 4) : rootAlgebra B :=
  rootGenerator B (typeF4SimpleRootIndex i) * rootGenerator B (-typeF4SimpleRootIndex i) -
    rootGenerator B (-typeF4SimpleRootIndex i) * rootGenerator B (typeF4SimpleRootIndex i)

private theorem rootAction_cartanGenerator (i : Fin 4) :
    Q.rootAction (cartanGenerator (B := B) i) = Q.cartanOperator i := by
  simp only [cartanGenerator, map_sub, map_mul, Q.rootAction_rootGenerator, cartanOperator]

/-- The simple Cartan commutator acts on every quotient root operator by its
integral coroot pairing. This is an identity on the entire quotient. -/
theorem cartan_operator_commutator (i : Fin 4) (s : F4Chevalley.Root) :
    Q.cartanOperator i * Q.operator s - Q.operator s * Q.cartanOperator i =
      (typeF4RootPairing.pairingIn ℤ s (typeF4SimpleRootIndex i) : F) • Q.operator s := by
  obtain ⟨p⟩ := rootExpansion_nonempty B.action B.irreducible.1
  have h : cartanGenerator (B := B) i * rootGenerator B s -
      rootGenerator B s * cartanGenerator (B := B) i =
      (typeF4RootPairing.pairingIn ℤ s (typeF4SimpleRootIndex i) : F) • rootGenerator B s := by
    apply Subtype.ext
    simpa only [cartanGenerator, rootGenerator, Subalgebra.coe_sub, Subalgebra.coe_mul,
      Subalgebra.coe_smul, SpanInvariance.cartanOperator, p.coeff_one_eq_rootOperator] using
      SpanInvariance.cartan_commutator_eq_pairing p i s
  have he := congrArg Q.rootAction h
  simpa only [map_sub, map_mul, map_smul, Q.rootAction_cartanGenerator,
    Q.rootAction_rootGenerator] using he

/-- The sum of the images of all negative-root operators is Cartan stable. -/
theorem cartanOperator_mem_negativeImage (i : Fin 4) (w : Q.Space)
    (hw : w ∈ Q.negativeImage) : Q.cartanOperator i w ∈ Q.negativeImage := by
  have hle : Q.negativeImage ≤ Q.negativeImage.comap (Q.cartanOperator i) := by
    apply iSup_le
    intro s x hx
    obtain ⟨z, rfl⟩ := hx
    change Q.cartanOperator i (Q.operator s.val z) ∈ Q.negativeImage
    have he := congrArg (fun a : Module.End F Q.Space => a z)
      (Q.cartan_operator_commutator i s.val)
    have hc : (Q.cartanOperator i * Q.operator s.val -
        Q.operator s.val * Q.cartanOperator i) z ∈ Q.negativeImage := by
      rw [he]
      exact Q.negativeImage.smul_mem _ (Q.operator_mem_negativeImage s z)
    have hs := Q.negativeImage.add_mem hc
      (Q.operator_mem_negativeImage s (Q.cartanOperator i z))
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, sub_add_cancel] using hs
  exact hle hw

end SimpleCyclicQuotient
end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
