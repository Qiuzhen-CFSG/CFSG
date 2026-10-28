module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.Contracts

/-!
# Idempotents and corners for the actual decomposition modules

`BlockIdempotentFrame` groups the primitive summands of the regular block
module according to their simple heads. Its elements need not be central:
they act as the identity on one simple isomorphism class and as zero on
the others. Their existence is a finite-dimensional algebra theorem, not
part of `Decomposition`.

The corner is the literal image of `x ↦ qᵢ x qⱼ` in `K[G]`. Its dimension
is to be compared with `degree i * degree j * (DᵀD) i j` by Brauer
reciprocity (Feit I.16.4 and I.17.8--9). Neither that comparison nor
indecomposability is asserted by this interface.
-/

public section
noncomputable section
open scoped BigOperators Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
open ModularBlock.PrimeBlockConstruction

variable {p : ℕ} {G : Type*} [Group G] [Finite G]
    {K : Type*} [Field K] {m n : ℕ}
    {d : PrimeCongruenceBlockData p G}
    {residue : Localization.AtPrime d.primeIdeal →+* K}
    {L : CyclicRootLift K m}

/-- A complete orthogonal family selecting the actual simple isomorphism
classes of the supplied decomposition, with every primitive copy included. -/
structure BlockIdempotentFrame (a : Decomposition d residue L n) where
  element : Fin n → MonoidAlgebra K G
  idempotent : ∀ e, IsIdempotentElem (element e)
  nonzero : ∀ e, element e ≠ 0
  orthogonal : Pairwise fun e f => element e * element f = 0
  sum_eq : ∑ e, element e = reducedPrincipal d residue
  simple_action : ∀ e f, (a.rep f).asAlgebraHom (element e) =
    if e = f then 1 else 0

namespace BlockIdempotentFrame

variable {a : Decomposition d residue L n} (q : BlockIdempotentFrame a)

/-- The actual corner subspace, with the multiplication order fixed. -/
@[expose] def corner (e f : Fin n) : Submodule K (MonoidAlgebra K G) :=
  LinearMap.range ((LinearMap.mulRight K (q.element f)).comp
    (LinearMap.mulLeft K (q.element e)))

/-- Every product with the prescribed left and right factors lies in its corner. -/
theorem mul_mem_corner (e f : Fin n) (x : MonoidAlgebra K G) :
    q.element e * x * q.element f ∈ q.corner e f :=
  ⟨x, rfl⟩

/-- Vanishing of the genuine corner dimension kills every such product. -/
theorem mul_eq_zero_of_corner_finrank_zero (e f : Fin n)
    (h : Module.finrank K (q.corner e f) = 0) (x : MonoidAlgebra K G) :
    q.element e * x * q.element f = 0 := by
  have hz : q.corner e f = ⊥ := Submodule.finrank_eq_zero.mp h
  have hx := q.mul_mem_corner e f x
  rw [hz] at hx
  exact hx

end BlockIdempotentFrame

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
