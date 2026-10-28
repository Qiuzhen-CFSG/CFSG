module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.HighestWeight
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.ShortA2
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.WeylTransport
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.Multiplicity

/-!
# Dimension counting for the exceptional F4 end-node weight

The source end-node highest weight is `(0,0,0,1)`. Its twenty-four distinct
nonzero Weyl weights supply twenty-four dimensions; two independent vectors
of full coroot weight zero supply the remaining two. Independence of the
actual simultaneous eigenspaces proves that these contributions add.

The imported normalizer words realize all twenty-four weights and transport
the highest vector to a highest vector for the short A2 subsystem. The first
coefficients of its rational root action then produce two independent
zero-weight vectors. Combining these constructions with the dimension count
proves the bound for every input factor with the specified highest weight.

Source: GLS3, Definition 2.8.1(b) and Section 1.14; the resulting bound is used
on printed p.356 (PDF p.367) of Aschbacher--Smith, Quasithin.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
namespace EndNode

/-- The original highest vector lies in the genuine last fundamental weight space. -/
theorem endHighestWeightSpace_ne_bot {B : AlgebraicFactor F}
    (h : B.HasBasicHighestWeight (0, 1)) :
    corootWeightSpace B endHighestWeight ≠ ⊥ := by
  obtain ⟨v, hv⟩ := h
  intro hbot
  have hvw : v ∈ corootWeightSpace B endHighestWeight := by
    rw [endHighestWeight_eq_basicCoefficient]
    exact basicHighestWeightVector_mem_corootWeightSpace hv
  rw [hbot] at hvw
  exact hv.1 (by simpa using hvw)

end EndNode
open EndNode

/-- The dimension count, with both representation-theoretic inputs explicit.
The independent weight spaces, rather than their number alone, account for
the zero-weight multiplicity. -/
theorem end_basicHighestWeight_finrank_ge_of_weight_spaces
    (B : AlgebraicFactor F)
    (horbit : ∀ i : Fin 24, corootWeightSpace B (endOrbitWeight i) ≠ ⊥)
    (hzero : 2 ≤ Module.finrank F (corootWeightSpace B 0)) :
    26 ≤ Module.finrank F B.Space := by
  let μ : Option (Fin 24) → Weight := fun i => i.elim 0 endOrbitWeight
  have hμ : Function.Injective μ := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact (endOrbitWeight_ne_zero j hij.symm).elim
    | some i =>
      cases j with
      | none => exact (endOrbitWeight_ne_zero i hij).elim
      | some j => exact congrArg some (endOrbitWeight_injective hij)
  have hsum := sum_corootWeightSpace_finrank_le B μ hμ
  have hpos (i : Fin 24) : 1 ≤ Module.finrank F (corootWeightSpace B (endOrbitWeight i)) := by
    have : Nontrivial (corootWeightSpace B (endOrbitWeight i)) :=
      Submodule.nontrivial_iff_ne_bot.mpr (horbit i)
    exact Module.finrank_pos
  have h24 : 24 ≤ ∑ i : Fin 24, Module.finrank F (corootWeightSpace B (endOrbitWeight i)) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpos i)
  simp only [Fintype.sum_option, μ, Option.elim_none, Option.elim_some] at hsum
  change Module.finrank F (corootWeightSpace B 0) +
    (∑ i : Fin 24, Module.finrank F (corootWeightSpace B (endOrbitWeight i))) ≤
      Module.finrank F B.Space at hsum
  omega

/-- Every exceptional basic factor with last fundamental highest weight has
dimension at least 26. The Weyl weights and zero-weight multiplicity are
constructed from its actual rational action. -/
theorem end_basicHighestWeight_finrank_ge
    {E : Type u} [Field E] [Finite E] [CharP E 2]
    (B : AlgebraicFactor (AlgebraicClosure E))
    (h : B.HasBasicHighestWeight (0, 1)) :
    26 ≤ Module.finrank (AlgebraicClosure E) B.Space :=
  end_basicHighestWeight_finrank_ge_of_weight_spaces B
    (endOrbitWeight_occurs B h)
    (Multiplicity.zero_weight_finrank_ge_two B (hasShortA2HighestVector B h))

end ReeF4.BinaryDegree.ExceptionalTensor
