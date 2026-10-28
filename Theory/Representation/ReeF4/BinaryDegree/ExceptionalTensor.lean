module

public import Theory.Representation.ReeF4.BinaryDegree.TensorDescent
public import Theory.SpecificGroups.ReeF4.Model
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.CyclicOrder
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicWeights
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.Established

/-!
# Converting actual exceptional factors to trace tensor data

The conditional assembly below starts with actual rational algebraic F4
factors and an intertwining equivalence to their exceptionally twisted tensor
product. Their dimensions are positive, and the tensor equivalence proves
the dimension product. The algebraic minimum supplies a large factor.
Reordering exceptional indices by multiplication by two turns the shift
detected by ordinary coefficient Frobenius into the required period.

The proved algebraic minimum 26 and the middle-node degree bound 52 are
re-exported here. The general conversion retains an arbitrary minimum as an
input, together with factorization and coefficient-Frobenius character
assertions. No unconditional tensor-classification theorem is asserted
here yet. This module deliberately does not import `BinaryDegree.lean`, so
the completed construction can be consumed there without an import cycle.

Source: GLS3, Definition 2.8.1(b), Theorems 2.8.2 and 2.8.5, Corollary
2.8.6(b), and Remark 2.8.8; Aschbacher--Smith, *The Classification of
Quasithin Groups*, printed p.356 (PDF p.367).
-/

public section

open Theory.AlgebraicGroup Representation.FrobeniusTensor

namespace ReeF4.BinaryDegree.ExceptionalTensor

universe u v

/-- Actual tensor factors yield the parent descent data once the separate
algebraic minimum and the character assertions have been established.
The factor-period input is stated in exceptional order, with shift `2*r`. -/
noncomputable def traceTensorData_of_algebraic_factors
    {F : Type u} [Field F] [IsAlgClosed F] {k b : ℕ}
    {W : Type v} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (σ : Representation F (Model k) W)
    (ι : SplitGroup k →* Variety.Point (F4Chevalley.Carrier (k := F)))
    (B : ZMod (2 * k + 1) → AlgebraicFactor F)
    (e : Representation.Equiv σ (exceptionalTensor ι B).ρ)
    (hbasic : ∀ i, (B i).IsExceptionalBasic)
    (hminimum : BasicFactorMinimum F b)
    (hlarge : ∃ i, (B i).IsNontrivial)
    (hfixed : ∀ g, σ.character g ^ (2 ^ (2 * k + 1)) = σ.character g)
    (hshift : ∀ r : ℕ, (∀ g, σ.character g ^ (2 ^ r) = σ.character g) →
      ∀ i, Module.finrank F (B (i + 2 * (r : ZMod (2 * k + 1)))).Space =
        Module.finrank F (B i).Space) :
    TraceTensorData (2 * k + 1) b σ where
  factorDegree i := Module.finrank F (B (2 * (i : ZMod (2 * k + 1)))).Space
  factor_pos i := (B _).finrank_pos
  large_factor := by
    obtain ⟨j, hj⟩ := hlarge
    obtain ⟨i, hi⟩ := (ordinaryIndex k).surjective j
    refine ⟨i.val, ?_⟩
    rw [ZMod.natCast_zmod_val]
    rw [ordinaryIndex_apply] at hi
    rw [hi]
    exact hminimum (B j) (hbasic j) hj
  finrank_eq := by
    rw [e.toLinearEquiv.finrank_eq, finrank_exceptionalTensor,
      prod_range_cast k (fun i => Module.finrank F (B i).Space),
      prod_ordinaryIndex k (fun i => Module.finrank F (B i).Space)]
  character_fixed := hfixed
  factor_period r hr := periodic_of_exceptional_shift k r
    (fun i => Module.finrank F (B i).Space) (hshift r hr)

end ReeF4.BinaryDegree.ExceptionalTensor
