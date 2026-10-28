module

public import Theory.SpecificGroups.Monster.Construction.NOctad.Basis
public import Theory.SpecificGroups.Monster.Construction.NOctad.ExtensionInterface

/-!
# Source-normalized coordinates of the point triality transform

For a genuine representation on `B_Z`, the coefficient `t_b(a)` is eight
times the pairing of the transformed source vector with the output basis
vector. Block stability gives its exact 64-term expansion, including the
factor one eighth. Complement independence is built into the index type;
changing the Parker-loop lift negates input and output vectors together.

This is only the coordinate interface for 30.1. The source theorem still
requires construction of the N-action, block stability, and proofs that all
these coefficients are signs and that the empty-subset column is the stated
constant. None of those assertions is included as a claimed conclusion here.

Source: Aschbacher, *Sporadic Groups*, Lemma 30.1, printed pp. 162–163.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad
open LocalC LocalC.ShortFamilies TrialitySpin
open Atlas.Codes Atlas.Fischer
open scoped BigOperators

/-- The source coefficient normalization for the literal `psi_3(alpha_x)`. -/
def transformCoefficient (ρ : Representation ℝ N Space) (x : Omega) (c : Octad)
    (a b : SubsetClass c) : ℝ :=
  8 * gamma (classVector c 0 b) (ρ (pointTriality x) (classVector c 0 a))

theorem transformCoefficient_lift (ρ : Representation ℝ N Space) (x : Omega)
    (c : Octad) (s : ParkerBit) (a b : SubsetClass c) :
    transformCoefficient ρ x c a b =
      8 * gamma (classVector c s b) (ρ (pointTriality x) (classVector c s a)) := by
  rcases bit_cases s with rfl | rfl
  · rfl
  · simp only [classVector_sign, map_neg, LinearMap.neg_apply, neg_neg]
    rfl

/-- The source sum, provided the actual generator preserves this octad block. -/
theorem transform_expansion_of_stable (ρ : Representation ℝ N Space) (x : Omega)
    (c : Octad) (hstable : (block c).map (ρ (pointTriality x)) ≤ block c)
    (s : ParkerBit) (a : SubsetClass c) :
    ρ (pointTriality x) (classVector c s a) =
      (1 / 8 : ℝ) • ∑ b : SubsetClass c, transformCoefficient ρ x c a b • classVector c s b := by
  have hzero : ρ (pointTriality x) (classVector c 0 a) =
      (1 / 8 : ℝ) • ∑ b : SubsetClass c,
        transformCoefficient ρ x c a b • classVector c 0 b := by
    have hm : ρ (pointTriality x) (classVector c 0 a) ∈ block c :=
      hstable (Submodule.mem_map_of_mem (classVector_mem_block c 0 a))
    rw [block_expansion c _ hm]
    simp only [Finset.smul_sum, smul_smul, transformCoefficient]
    norm_num [← mul_assoc]
  rcases bit_cases s with rfl | rfl
  · exact hzero
  · simpa only [classVector_sign, map_neg, smul_neg, Finset.sum_neg_distrib] using
      congrArg Neg.neg hzero

/-- The expansion uses the literal subset parameters and either signed lift. -/
theorem transform_parameters_of_stable (ρ : Representation ℝ N Space) (x : Omega)
    (c : Octad) (hstable : (block c).map (ρ (pointTriality x)) ≤ block c)
    (s : ParkerBit) (J : EvenSubset c) :
    ρ (pointTriality x) (vector (parameters c J s)) =
      (1 / 8 : ℝ) • ∑ b : SubsetClass c,
        transformCoefficient ρ x c (subsetClass c J) b • classVector c s b :=
  transform_expansion_of_stable ρ x c hstable s (subsetClass c J)

end Sporadic.Monster.Construction.NOctad
