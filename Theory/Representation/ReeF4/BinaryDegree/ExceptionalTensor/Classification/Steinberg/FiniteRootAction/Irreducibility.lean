module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.SourceSupport
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.PrefixPairing
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.OrdinaryComparison
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading

/-!
# Irreducibility of the actual finite Ree exceptional tensors

The native positive root curves give the distinct finite Frobenius coefficients
on the unweighted tensor filtration. Minimal filtration degree puts the actual
highest tensor in every nonzero invariant subspace. Its nonzero pairing with
the native opposition translate then excludes a proper invariant subspace.
The checked ordinary-to-exceptional tensor equivalence retains the original
finite Ree action and all four basic factors, including the trivial factor.

This discharges the finite irreducibility clause of Steinberg (1963), 12.2.
Only universality of the literal algebraic F4 carrier remains an independent
geometric input; no finite restriction or classification premise is used.
-/

public section

open Theory.AlgebraicGroup
open scoped BigOperators
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open AlgebraicTensor
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
variable (m : ℕ) (B : ZMod (2*m+1) → AlgebraicFactor F)

/-- Every nonzero invariant subspace contains the actual source highest tensor. -/
theorem ordinary_highest_mem
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (p : ∀i, RootExpansion (basicFactor m B i).action)
    (b : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (f : CoefficientField m →+* F)
    (W : Subrepresentation (ordinaryAction m B f (2*m+1))) (hne : W ≠ ⊥) :
    highestTensor m B v (2*m+1) ∈ W := by
  classical
  let C := tensorFiltration m B (sourceTensorWeights b) (2*m+1)
  let P (r : ShortPositiveRoot) (i : Fin (2*m+1)) :=
    coordinateMap m B (2*m+1) i.val ((p i.val).coeff r.val 1)
  let d (r : ShortPositiveRoot) : ℕ := (weightDegree (rootWeight r.val)).toNat
  have hd (r : ShortPositiveRoot) : 0 < d r := by
    have h := weightDegree_rootWeight_pos r.property.2
    dsimp [d]
    omega
  have hcast (r : ShortPositiveRoot) : (d r : ℤ) = weightDegree (rootWeight r.val) :=
    Int.toNat_of_nonneg (le_of_lt (weightDegree_rootWeight_pos r.property.2))
  choose g hg using fun (r : ShortPositiveRoot) (t : CoefficientField m) =>
    exists_positive_ordinary_remainder m B (2*m+1) p (sourceTensorWeights b) f r.val
      r.property.2 r.property.1 t
  obtain ⟨N,hN⟩ := source_tensorFiltration_exists_top m B hU p b v hv (2*m+1)
  have happly := Representation.FrobeniusFiltered.highest_mem (p := 2) (I := ShortPositiveRoot) f
    (ordinaryAction m B f (2*m+1)) C (tensorFiltration_mono m B _ _) N hN
    (highestTensor m B v (2*m+1)) (source_tensorFiltration_zero m B hU p b v hv _)
  rw [GaloisField.finrank 2 (by omega : 2*m+1 ≠ 0)] at happly
  apply happly P d hd g _ _ _ W hne
  · intro r k x hx i
    have h := coordinateCoefficient_filtration m B (2*m+1) i.val i.isLt
      (p i.val) r.val 1 (sourceTensorWeights b) k (Submodule.mem_map_of_mem hx)
    simpa only [Nat.cast_one, one_mul, hcast, P, C] using h
  · intro r k x hx t
    have h := hg r t k x hx
    rw [hcast]
    have he : ((((List.range (2*m+1)).map fun i => f t ^ (2^i) •
        coordinateMap m B (2*m+1) i ((p i).coeff r.val 1)).sum) x) =
        ∑ i : Fin (2*m+1), f (t ^ (2 ^ i.val)) • P r i x := by
      simp only [P, map_pow]
      have hsum (n : ℕ) :
          ((List.range n).map (fun i => f t ^ (2^i) •
            coordinateMap m B (2*m+1) i ((p i).coeff r.val 1))).sum x =
          ∑ i ∈ Finset.range n, f t ^ (2^i) • coordinateMap m B (2*m+1) i ((p i).coeff r.val 1) x := by
        induction n with
        | zero => simp
        | succ n ih => simp only [List.range_succ, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton, LinearMap.add_apply, LinearMap.smul_apply,
            Finset.sum_range_succ, ih]
      rw [hsum]
      exact (Fin.sum_univ_eq_sum_range (fun i => f t ^ (2^i) •
        coordinateMap m B (2*m+1) i ((p i).coeff r.val 1) x) (2*m+1)).symm
    rw [he] at h
    exact h
  · intro k hk x hx hpx
    apply source_tensorFiltration_primitive m B hU p b v hv (2*m+1) k (by exact_mod_cast hk) x hx
    intro i hi r
    simpa only [hcast, P] using hpx r ⟨i,hi⟩

/-- The complete exceptional tensor is irreducible on the original finite carrier. -/
theorem exceptionalTensor_irreducible
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (hB : ∀i, (B i).IsExceptionalBasic) (f : CoefficientField m →+* F) :
    Representation.IsIrreducible (exceptionalTensor (splitEmbedding f) B).ρ := by
  classical
  choose b v hv using fun i : ℕ => hB (ordinaryIndex m (i : ZMod (2*m+1)))
  let p : ∀i, RootExpansion (basicFactor m B i).action := fun i =>
    Classical.choice (rootExpansion_nonempty (basicFactor m B i).action
      (basicFactor m B i).irreducible.1)
  have hi := ordinary_isIrreducible_of_highest_mem m B hU p b v hv f (2*m+1)
    (ordinary_highest_mem m B hU p b v hv f)
  exact exceptionalTensor_isIrreducible_of_ordinary m B f hi

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
