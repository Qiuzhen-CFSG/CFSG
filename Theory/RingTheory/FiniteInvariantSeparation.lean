module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
/-!
# Invariant functions separate finite orbits in every characteristic

Two scalar-valued algebra homomorphisms agreeing on the invariant subalgebra
have prime kernels above the same prime. Transitivity of the finite group on
those kernels gives an element carrying one evaluation to the other; scalar
constants recover the evaluations themselves. No division by the group order
is used. This is the orbit-separation step of Steinberg (1963), §3.9, used for
the characteristic-two Ree semisimple coordinates.
-/

open scoped Pointwise
open MulAction

public section
namespace Theory.FiniteInvariantSeparation
variable {F A G : Type*} [Field F] [CommRing A] [Algebra F A]
  [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G F A]

/-- Agreement on the invariant algebra determines algebra homomorphisms up to the finite group action. -/
theorem exists_smul_of_eq_on_invariants (f h : A →ₐ[F] F)
    (heq : ∀ a : A, (∀ g : G, g • a = a) → f a = h a) :
    ∃ g : G, ∀ a : A, h a = f (g • a) := by
  let B := FixedPoints.subalgebra F A G
  have : Algebra.IsInvariant B A G := ⟨fun a ha => ⟨⟨a, ha⟩, rfl⟩⟩
  let P : Ideal A := RingHom.ker f.toRingHom
  let Q : Ideal A := RingHom.ker h.toRingHom
  have : P.IsPrime := RingHom.ker_isPrime f.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime h.toRingHom
  have hPQ : P.under B = Q.under B := by
    ext a
    change f a.val = 0 ↔ h a.val = 0
    rw [heq a.val a.property]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B A G P Q hPQ
  refine ⟨g⁻¹, fun a => ?_⟩
  have hmem : a - algebraMap F A (h a) ∈ Q := by
    change h (a - algebraMap F A (h a)) = 0
    simp
  rw [hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hmem
  change f (g⁻¹ • (a - algebraMap F A (h a))) = 0 at hmem
  have he : f (g⁻¹ • a) - h a = 0 := by
    simpa [smul_sub, smul_algebraMap] using hmem
  exact (sub_eq_zero.mp he).symm
end Theory.FiniteInvariantSeparation
