module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.PairNormalization.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.PairNormalization.SignOrbit.FixedVector
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.MonomialConjugacy.SignResolution

/-!
# Simultaneous Golay sign normalization for the reference pair

The first reference pullback and sign are the existing marked involution.
Its proved sign-resolution theorem supplies a Golay coboundary normalizing the
first generator. Conjugation preserves the equality of the actual Λ/2Λ fixed
spaces. The separating-vector calculation then fixes the second sign up to
negation; a second explicit Golay coboundary removes that negation while fixing
the first sign. Adding the two words gives the simultaneous conjugator.

`referenceSignOrbit` discharges the exact published orbit contract, including
its literal matrix-kernel premise. `reference_pair` applies the existing group
consumer to obtain an actual simultaneous Golay sign conjugation. The third
negative-square premise is preserved in both public statements; the argument
already follows from the first two squares and equality of the kernels.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
and the root-four conventions on p.269. All code and lattice operations are
those of the existing attributed ATLAS models.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
@[expose] public noncomputable section

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.PairNormalization

private theorem referencePullA_eq_swap (i : Omega) :
    referencePullA i = coordinateSwap.val.symm i := by revert i; decide
private theorem referenceSign_eq_marked : jWord referenceHexB = signWord.val := by decide

private theorem normalize_first (a : GolayMonomialGroup)
    (hp : ∀ i, monomialPull a i = referencePullA i)
    (ha : (monomialEmbedding a) ^ 2 = negationIsometry) :
    ∃ c : golay, ∀ i,
      a.left.toAdd.val i + c.val i + c.val (referencePullA i) = jWord referenceHexB i := by
  obtain ⟨c,hc⟩ := opposite_signs_eq_marked_coboundary a.left.toAdd (by
    intro i
    have hi := (monomial_square_negation_parameters a ha).2.1 i
    change a.left.toAdd.val (monomialPull a i) = _ at hi
    rwa [hp,referencePullA_eq_swap] at hi)
  refine ⟨c,fun i => ?_⟩
  rw [referencePullA_eq_swap,referenceSign_eq_marked]
  calc
    a.left.toAdd.val i + c.val i + c.val (coordinateSwap.val.symm i) =
        (c.val i + a.left.toAdd.val i) + c.val (coordinateSwap.val.symm i) := by ac_rfl
    _ = (signWord.val i + c.val (coordinateSwap.val.symm i)) + c.val (coordinateSwap.val.symm i) := by rw [hc]
    _ = signWord.val i := by rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]

private def adjustment (e : Bit) : golay :=
  ⟨golayEncoder (e • translateWord,0,0),⟨_,rfl⟩⟩
private theorem adjustment_A (e : Bit) (i : Omega) :
    (adjustment e).val i + (adjustment e).val (referencePullA i) = 0 := by revert e i; decide
private theorem adjustment_B (e : Bit) (i : Omega) :
    (adjustment e).val i + (adjustment e).val (referencePullB i) = e := by revert e i; decide

/-- Simultaneous sign normalization on the literal binary Leech quotient. -/
theorem referenceSignOrbit : ReferenceSignOrbit := by
  intro a b hpa hpb ha hb _hab he
  obtain ⟨c,hc⟩ := normalize_first a hpa ha
  let a' := signLift c * a * (signLift c)⁻¹
  let b' := signLift c * b * (signLift c)⁻¹
  have hpa' : ∀ i, monomialPull a' i = referencePullA i := hpa
  have hpb' : ∀ i, monomialPull b' i = referencePullB i := hpb
  have hsa' : a'.left.toAdd.val = jWord referenceHexB := by
    funext i
    rw [sign_conjugate_left,hpa]
    exact hc i
  have hb' : (monomialEmbedding b') ^ 2 = negationIsometry := by
    change (monomialEmbedding (signLift c * b * (signLift c)⁻¹)) ^ 2 = _
    rw [map_mul,map_mul,map_inv]
    calc
      (monomialEmbedding (signLift c) * monomialEmbedding b * (monomialEmbedding (signLift c))⁻¹) ^ 2 =
          monomialEmbedding (signLift c) * (monomialEmbedding b) ^ 2 * (monomialEmbedding (signLift c))⁻¹ := by
        simp only [pow_two]; group
      _ = negationIsometry := by
        rw [hb,Subgroup.mem_center_iff.mp negation_mem_center (monomialEmbedding (signLift c))]
        simp [mul_assoc]
  have he' : binaryFixed (monomialEmbedding a') = binaryFixed (monomialEmbedding b') := by
    have h := binaryFixed_conjugate_eq (monomialEmbedding (signLift c))⁻¹
      (monomialEmbedding a) (monomialEmbedding b) ((same_binaryFixed_iff_kernel_eq a b).mpr he)
    simpa only [a',b',map_mul,map_inv,inv_inv] using h
  have hbSign := SignOrbit.second_sign a' b' hpa' hpb' hsa' hb' he'
  let e := b'.left.toAdd.val ((0,0),0)
  have hbSign' (i : Omega) :
      b.left.toAdd.val i + c.val i + c.val (referencePullB i) =
        jWord (referenceHexA + referenceHexB) i + e := by
    have h := hbSign i
    rw [sign_conjugate_left,hpb] at h
    exact h
  refine ⟨c + adjustment e,?_,?_⟩
  · intro i
    change a.left.toAdd.val i + (c.val i + (adjustment e).val i) +
      (c.val (referencePullA i) + (adjustment e).val (referencePullA i)) = _
    calc
      _ = (a.left.toAdd.val i + c.val i + c.val (referencePullA i)) +
          ((adjustment e).val i + (adjustment e).val (referencePullA i)) := by ring
      _ = jWord referenceHexB i := by rw [hc,adjustment_A,add_zero]
  · intro i
    change b.left.toAdd.val i + (c.val i + (adjustment e).val i) +
      (c.val (referencePullB i) + (adjustment e).val (referencePullB i)) = _
    calc
      _ = (b.left.toAdd.val i + c.val i + c.val (referencePullB i)) +
          ((adjustment e).val i + (adjustment e).val (referencePullB i)) := by ring
      _ = jWord (referenceHexA + referenceHexB) i := by
        rw [hbSign',adjustment_B,add_assoc,CharTwo.add_self_eq_zero,add_zero]

/-- The actual simultaneous Golay conjugator, with all sign-orbit premises discharged. -/
theorem reference_pair (a b : GolayMonomialGroup)
    (hpa : ∀ i, monomialPull a i = referencePullA i)
    (hpb : ∀ i, monomialPull b i = referencePullB i)
    (ha : (monomialEmbedding a) ^ 2 = negationIsometry)
    (hb : (monomialEmbedding b) ^ 2 = negationIsometry)
    (hab : (monomialEmbedding a * monomialEmbedding b) ^ 2 = negationIsometry)
    (he : binaryFixed (monomialEmbedding a) = binaryFixed (monomialEmbedding b)) :
    ∃ c : golay, ReferenceQuaternionPair
      (signLift c * a * (signLift c)⁻¹) (signLift c * b * (signLift c)⁻¹) :=
  reference_pair_of_signOrbit referenceSignOrbit a b hpa hpb ha hb hab he

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.PairNormalization
