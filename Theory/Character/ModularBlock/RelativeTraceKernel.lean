module
public import Theory.Character.ModularBlock.InvolutionPairing
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Relative traces from the order-two Brauer kernel

Let an element of square one act on a finite group algebra by conjugation.
An invariant group-algebra element whose coefficients at the fixed group
elements lie in an ideal is a relative trace modulo that ideal. Neither
characteristic two nor a nonidentity assumption on the acting element is
required. This is the coefficient step used before the exact relative-trace
correction in the modular Z-star argument.

Conjugation induces an involution on the group basis. The invariant
coefficient function satisfies `InvolutionPairing.exists_pairing_mod_ideal`;
interpreting the resulting finite-support function in the group algebra
gives the sum of an element and its conjugate, with error in the ideal.

Ported from `Submission/ZStar/BrauerKernelRelativeTrace.lean` at revision
`c3503435` of `public/lean-eval/glauberman_zStar`, preserving its hypotheses
and conclusion through the current `MonoidAlgebra.coeff` interface.
-/

namespace ModularBlock.BrauerKernelRelativeTrace

universe u v

/-- The group-algebra automorphism induced by conjugation by a group element. -/
public noncomputable def conjugation
    (R : Type u) {G : Type v} [Semiring R] [Group G] (z : G) :
    MonoidAlgebra R G ≃+* MonoidAlgebra R G :=
  MonoidAlgebra.mapDomainRingEquiv R (MulAut.conj z)

/-- Conjugation permutes coefficients by the inverse conjugation on the basis. -/
@[simp] public theorem conjugation_apply
    {R : Type u} {G : Type v} [Semiring R] [Group G]
    (z : G) (a : MonoidAlgebra R G) (x : G) :
    (conjugation R z a).coeff x = a.coeff (z⁻¹ * x * z) := by
  simp [conjugation, MonoidAlgebra.coeff_mapDomainRingEquiv]

/-- Vanishing of the fixed coefficients modulo an ideal makes an invariant
element a relative trace modulo that ideal. -/
public theorem exists_relativeTrace_mod_ideal_of_conjugation_fixed
    {R : Type u} {G : Type v} [Ring R] [Group G] [Finite G]
    (z : G) (hz : z * z = 1)
    (I : Ideal R) (f : MonoidAlgebra R G)
    (hfinv : conjugation R z f = f)
    (hfixed : ∀ x : G, z⁻¹ * x * z = x → f.coeff x ∈ I) :
    ∃ b : MonoidAlgebra R G, ∀ x : G,
      (f - (b + conjugation R z b)).coeff x ∈ I := by
  let tau : G → G := fun x => z⁻¹ * x * z
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have htau : Function.Involutive tau := by
    intro x
    dsimp [tau]
    rw [hzinv]
    calc
      z * (z * x * z) * z = (z * z) * x * (z * z) := by
        simp only [mul_assoc]
      _ = x := by rw [hz, one_mul, mul_one]
  have hinv : ∀ x, f.coeff (tau x) = f.coeff x := by
    intro x
    have h := congrArg (fun a : MonoidAlgebra R G => a.coeff x) hfinv
    simpa [tau, conjugation_apply] using h
  obtain ⟨b, hb⟩ := InvolutionPairing.exists_pairing_mod_ideal
    tau htau I f.coeff hinv (fun x hx => hfixed x hx)
  refine ⟨MonoidAlgebra.ofCoeff b, fun x => ?_⟩
  change f.coeff x - (b x + (conjugation R z (MonoidAlgebra.ofCoeff b)).coeff x) ∈ I
  rw [conjugation_apply]
  exact hb x

end ModularBlock.BrauerKernelRelativeTrace
