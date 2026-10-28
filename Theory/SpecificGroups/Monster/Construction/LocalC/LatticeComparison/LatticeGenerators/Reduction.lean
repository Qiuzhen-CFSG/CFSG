module
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.Additivity
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.Forms
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.GeneratorCoordinates
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechPermutations
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechModTwoAction

/-!
# The actual Leech generators on all source coordinates

A sign change sends `f_v` to `f_v - f(v ∩ Y) - (|v ∩ Y|/2) f_X`.
On `f(J)` it adds `|J| f_Y - 2 f(Y ∩ J) - |Y ∩ J| f_X`.
These are identities of integral lattice vectors. Reduction modulo `2Λ`
and the twisted code addition give exactly the parity-dependent intersection
and half-overlap terms of the source action on every coordinate pair.
Coordinate permutations preserve the same representatives by reindexing.

Source: Aschbacher, *Sporadic Groups*, Lemma 23.10(4), printed pp. 120–121,
and the generator comparison on p. 148. The integral lattice and its
isometries are the attributed ATLAS constructions imported above.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped BigOperators
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

private theorem weight_intersection (a b : BinaryWord) :
    hammingNorm (fun i => a i * b i) = overlap a b := by
  simp only [hammingNorm_eq_sum, overlap_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases bit_cases (a i) with ha | ha <;> rcases bit_cases (b i) with hb | hb <;>
    simp [ha, hb]

/-- The integral sign identity on a code vector, before reduction. -/
theorem sourceCodeVector_sign (Y v : golay) :
    (signIsometry Y).val (sourceCodeVector v) =
      sourceCodeVector v - sourceCocodeVector (fun i => v.val i * Y.val i) -
        ((overlap v.val Y.val / 2 : ℕ) : ℤ) • sourceCodeVector golayOne := by
  have hd := golay_overlap_two_dvd v Y
  have he : (overlap v.val Y.val : ℤ) = 2 * (overlap v.val Y.val / 2 : ℕ) := by
    exact_mod_cast (show overlap v.val Y.val = 2 * (overlap v.val Y.val / 2) by omega)
  apply Subtype.ext
  ext i
  change (if Y.val i = 0 then (sourceCodeVector v).val i else
      -(sourceCodeVector v).val i) =
    (sourceCodeVector v).val i - (sourceCocodeVector _).val i -
      (overlap v.val Y.val / 2 : ℕ) * (sourceCodeVector golayOne).val i
  rw [sourceCodeVector_apply, sourceCocodeVector_apply, sourceCodeVector_one_apply,
    weight_intersection, he]
  rcases bit_cases (v.val i) with hv | hv <;> rcases bit_cases (Y.val i) with hY | hY <;>
    simp [golayIntegerLift, hv, hY] <;> ring

/-- The integral sign identity on a cocode representative, including its even-lattice term. -/
theorem sourceCocodeVector_sign (Y : golay) (J : BinaryWord) :
    (signIsometry Y).val (sourceCocodeVector J) =
      sourceCocodeVector J + (hammingNorm J : ℤ) • sourceCodeVector Y -
        (2 : ℤ) • sourceCocodeVector (fun i => Y.val i * J i) -
        (overlap Y.val J : ℤ) • sourceCodeVector golayOne := by
  apply Subtype.ext
  ext i
  change (if Y.val i = 0 then (sourceCocodeVector J).val i else
      -(sourceCocodeVector J).val i) =
    (sourceCocodeVector J).val i + (hammingNorm J : ℤ) * (sourceCodeVector Y).val i -
      2 * (sourceCocodeVector _).val i - (overlap Y.val J : ℤ) *
        (sourceCodeVector golayOne).val i
  rw [sourceCocodeVector_apply, sourceCocodeVector_apply, sourceCodeVector_apply,
    sourceCodeVector_one_apply, weight_intersection]
  rcases bit_cases (J i) with hJ | hJ <;> rcases bit_cases (Y.val i) with hY | hY <;>
    simp [golayIntegerLift, hJ, hY] <;> ring

private theorem reduce_zsmul (n : ℤ) (x : leech) :
    leechReduction (n • x) = (n : Bit) • leechReduction x := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

private theorem class_neg (a : LeechModTwo) : -a = a := by
  apply neg_eq_of_add_eq_zero_left
  rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul Bit]
  exact zero_smul Bit a

/-- The intersection and half-overlap corrections on a code class. -/
theorem sourceCodeClass_sign (Y v : golay) :
    leechModTwoRepresentation (signIsometry Y) (leechReduction (sourceCodeVector v)) =
      leechReduction (sourceCodeVector v) + sourceCocodeClass (intersectionCocode v Y) +
        golayHalfOverlap v Y • leechReduction (sourceCodeVector golayOne) := by
  rw [leechModTwoRepresentation_reduce, sourceCodeVector_sign,
    map_sub, map_sub, reduce_zsmul]
  simp only [intersectionCocode, sourceCocodeClass_mk, sub_eq_add_neg, class_neg, Int.cast_natCast]
  rfl

/-- On the cocode image the corrections are parity and the code–cocode pairing. -/
theorem sourceCocodeClass_sign (Y : golay) (c : Cocode) :
    leechModTwoRepresentation (signIsometry Y) (sourceCocodeClass c) =
      sourceCocodeClass c + cocodeParity c • leechReduction (sourceCodeVector Y) +
        cocodePairing Y c • leechReduction (sourceCodeVector golayOne) := by
  obtain ⟨J, rfl⟩ := Submodule.Quotient.mk_surjective golay c
  rw [sourceCocodeClass_mk, leechModTwoRepresentation_reduce, sourceCocodeVector_sign]
  rw [map_sub, map_sub, map_add, reduce_zsmul, reduce_zsmul, reduce_zsmul,
    sourceCocodeParity_mk, sourceCocodePairing_mk]
  simp only [Int.cast_natCast, Int.cast_ofNat, show (2 : Bit) = 0 from rfl,
    zero_smul, add_zero, sub_eq_add_neg, class_neg]

private theorem sourceCodeClass_sum (v w : golay) :
    leechReduction (sourceCodeVector (v + w)) =
      leechReduction (sourceCodeVector v) + leechReduction (sourceCodeVector w) +
        (golayHalfOverlap v w • leechReduction (sourceCodeVector golayOne) +
          sourceCocodeClass (intersectionCocode v w)) := by
  have h := sourceCodeClass_twisted_sum v w
  rw [sourceCodeClass_add_smul_one, add_assoc] at h
  simpa only [sub_eq_add_neg, class_neg] using eq_sub_of_add_eq h

/-- Source 23.10(4): sign equivariance on the entire twisted coordinate space. -/
theorem sourceCoordinateMap_sign (Y : golay) (x : QuadraticCoordinates) :
    sourceCoordinateMap (sourceSignCoordinates Y x) =
      leechModTwoRepresentation (signIsometry Y) (sourceCoordinateMap x) := by
  simp only [sourceCoordinateMap, sourceSignCoordinates, map_add,
    sourceCodeClass_sign, sourceCocodeClass_sign, map_smul]
  rw [sourceCodeClass_add_smul_one]
  rcases bit_cases (cocodeParity x.cocode) with hp | hp
  · simp only [hp, zero_smul, add_zero, one_mul, one_smul, add_smul]
    abel
  · simp only [hp, one_smul, CharTwo.add_self_eq_zero, zero_mul, zero_add, zero_smul,
      add_zero, sourceCodeClass_sum]
    abel

/-- Reindexing the actual integral code vector. -/
theorem sourceCodeVector_permutation (σ : Mathieu24CodeModel) (v : golay) :
    (permutationEmbedding σ).val (sourceCodeVector v) =
      sourceCodeVector (parkerCodeEquiv σ v) := by
  apply Subtype.ext
  rfl

/-- Reindexing the actual integral cocode representative preserves its weight correction. -/
theorem sourceCocodeVector_permutation (σ : Mathieu24CodeModel) (J : BinaryWord) :
    (permutationEmbedding σ).val (sourceCocodeVector J) =
      sourceCocodeVector (coordinatePermutation σ.val J) := by
  apply Subtype.ext
  ext i
  change (sourceCocodeVector J).val (σ.val.symm i) = _
  rw [sourceCocodeVector_apply, sourceCocodeVector_apply, coordinatePermutation_weight]
  rfl

/-- Source 23.10(4): permutation equivariance with the fixed inverse-coordinate convention. -/
theorem sourceCoordinateMap_permutation (σ : Mathieu24CodeModel) (x : QuadraticCoordinates) :
    sourceCoordinateMap (sourcePermutationCoordinates σ x) =
      leechModTwoRepresentation (permutationEmbedding σ) (sourceCoordinateMap x) := by
  obtain ⟨v, c⟩ := x
  obtain ⟨J, rfl⟩ := Submodule.Quotient.mk_surjective golay c
  change sourceCoordinateMap ⟨parkerCodeEquiv σ v,
      sourceCocodePermutation σ (Submodule.Quotient.mk J)⟩ = _
  rw [sourceCocodePermutation_mk, sourceCoordinateMap_mk, sourceCoordinateMap_mk,
    leechModTwoRepresentation_reduce, map_add (permutationEmbedding σ).val,
    sourceCodeVector_permutation, sourceCocodeVector_permutation]

end Sporadic.Monster.Construction.LocalC
