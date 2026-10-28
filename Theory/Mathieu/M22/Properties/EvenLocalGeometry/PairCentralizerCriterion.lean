module

public import Theory.Mathieu.M22.Properties.EvenLocalGeometry

/-!
# Detecting the pair-kernel centralizer by point stabilizers

Suppose a family of elements of the actual pair kernel distinguishes the
marked pair and each of the five hexads by which elements fix a point.
A permutation centralizing the kernel preserves these tests. It therefore
stabilizes the pair and all five hexads, so belongs to the action kernel.
The test family need not be proved to enumerate or generate the whole kernel.

This is a finite-certificate criterion for the M₂₂ even-characteristic
calculation in Aschbacher–Smith, Theorem 0.1.2(5), printed pp.3–4.
-/

namespace Sporadic.Mathieu.M22EvenGeometry
open Subgroup M22ValueBound.Concrete
open scoped Pointwise

/-- Fixed-element tests that distinguish the six geometric regions suffice
to prove the ambient pair-kernel centralizer bound. -/
public theorem pairKernel_selfCentralizing_of_fixedPoint_tests
    {ι : Type*} (q : ι → M22) (hq : ∀ i, q i ∈ pairKernel)
    (hseparate : ∀ a b : Fin 22, (∀ i, q i • a = a ↔ q i • b = b) →
      (a ∈ m22Pair12 ↔ b ∈ m22Pair12) ∧
        ∀ j : Fin 5, a ∈ pairHexad j ↔ b ∈ pairHexad j) :
    centralizer (pairKernel : Set M22) ≤ pairKernel := by
  intro g hg
  have htests (a : Fin 22) : ∀ i, q i • a = a ↔ q i • (g • a) = g • a := by
    intro i
    have hcomm : q i * g = g * q i := hg (q i) (hq i)
    have he : q i • (g • a) = g • (q i • a) := by
      rw [← mul_smul, hcomm, mul_smul]
    constructor
    · intro h
      rw [he, h]
    · intro h
      exact (MulAction.injective g) (he.symm.trans h)
  have hfirst : g ∈ first := by
    change g ∈ MulAction.stabilizer M22 m22Pair12
    exact MulAction.mem_stabilizer_finset'.mpr fun a ha =>
      (hseparate a (g • a) (htests a)).1.mp ha
  change g ∈ pairAction.ker.map first.subtype
  refine ⟨⟨g, hfirst⟩, ?_, rfl⟩
  apply MonoidHom.mem_ker.mpr
  apply Equiv.ext
  intro j
  apply pairHexad_injective
  rw [pairAction_spec]
  change g • pairHexad j = pairHexad j
  apply MulAction.mem_stabilizer_iff.mp
  exact MulAction.mem_stabilizer_finset'.mpr fun a ha =>
    ((hseparate a (g • a) (htests a)).2 j).mp ha

end Sporadic.Mathieu.M22EvenGeometry
