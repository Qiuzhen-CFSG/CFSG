import Submission.ZStar.InvolutionPairing
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
The coefficient-pairing part of the order-two Brauer-kernel argument.

For an involution `z`, a conjugation-invariant group-algebra element whose
coefficients at the `z`-fixed group elements lie in an ideal is a relative
trace modulo that ideal.
-/

noncomputable section

namespace Submission.ZStar
namespace BrauerKernelRelativeTrace

universe u v

attribute [local instance] Fintype.ofFinite

def conjugation
    (R : Type u) {G : Type v} [Semiring R] [Group G] (z : G) :
    MonoidAlgebra R G ≃+* MonoidAlgebra R G :=
  MonoidAlgebra.mapDomainRingEquiv R (MulAut.conj z)

@[simp] theorem conjugation_apply
    {R : Type u} {G : Type v} [Semiring R] [Group G]
    (z : G) (a : MonoidAlgebra R G) (x : G) :
    conjugation R z a x = a (z⁻¹ * x * z) := by
  exact MonoidAlgebra.mapDomainRingEquiv_apply (MulAut.conj z) a x

theorem exists_relativeTrace_mod_ideal_of_conjugation_fixed
    {R : Type u} {G : Type v} [Ring R] [Group G] [Finite G]
    (z : G) (hz : z * z = 1)
    (I : Ideal R) (f : MonoidAlgebra R G)
    (hfinv : conjugation R z f = f)
    (hfixed : ∀ x : G, z⁻¹ * x * z = x → f x ∈ I) :
    ∃ b : MonoidAlgebra R G, ∀ x : G,
      (f - (b + conjugation R z b)) x ∈ I := by
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
  have hinv : ∀ x, f (tau x) = f x := by
    intro x
    have h := congrArg (fun a : MonoidAlgebra R G => a x) hfinv
    simpa [tau, conjugation_apply] using h
  obtain ⟨b, hb⟩ := InvolutionPairing.exists_pairing_mod_ideal
    tau htau I f hinv (fun x hx => hfixed x hx)
  refine ⟨b, fun x => ?_⟩
  change f x - (b x + conjugation R z b x) ∈ I
  rw [conjugation_apply]
  exact hb x

end BrauerKernelRelativeTrace
end Submission.ZStar
