module
public import Theory.Representation.TensorPrimitiveLine
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.CoordinateMaps
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.BasicSpaces

/-!
# The primitive line of the actual basic tensor prefix

Insert the genuine first positive short-root coefficient in one tensor factor
at a time. Basis separation shows that their common kernel is exactly the
line through the tensor of the source highest vectors. The source application
covers all four basic weights, retains the canonical tensor space and actual
coordinate maps, and discharges factor primitive-line assumptions.

This is Steinberg (1963), 5.1(1), as used in finite Ree restriction 12.2.
Universality remains with the actual F4 geometric producer.
-/

public section

open Theory.AlgebraicGroup
open scoped TensorProduct
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open AlgebraicTensor
variable {F : Type*} [Field F] [IsAlgClosed F]
variable (m : ℕ) (B : ZMod (2*m+1) → AlgebraicFactor F)

@[expose] noncomputable def highestTensor (v : ∀ i, (basicFactor m B i).Space) :
    (n : ℕ) → basicTensorSpace m B n
  | 0 => (1 : F)
  | n+1 => highestTensor v n ⊗ₜ[F] v n

set_option backward.isDefEq.respectTransparency false in
theorem highestTensor_ne_zero
    (v : ∀ i, (basicFactor m B i).Space) (hv : ∀i, v i ≠ 0) (n : ℕ) :
    highestTensor m B v n ≠ 0 := by
  induction n with
  | zero => exact (one_ne_zero : (1 : F) ≠ 0)
  | succ n ih =>
    obtain ⟨a,ha⟩ := Module.Projective.exists_dual_eq_one F ih
    obtain ⟨b,hb⟩ := Module.Projective.exists_dual_eq_one F (hv n)
    intro h
    have hh := congrArg (fun z : basicTensorSpace m B (n+1) =>
      TensorProduct.lid F F (TensorProduct.map a b z)) h
    change TensorProduct.lid F F (TensorProduct.map a b
      (highestTensor m B v n ⊗ₜ[F] v n)) = TensorProduct.lid F F (TensorProduct.map a b 0) at hh
    simp only [TensorProduct.map_tmul, ha, hb, map_zero,
      TensorProduct.lid_tmul, smul_eq_mul, one_mul] at hh
    exact one_ne_zero hh

set_option backward.isDefEq.respectTransparency false in
theorem prefix_primitive_iff
    (v : ∀i, (basicFactor m B i).Space) (hv : ∀i, v i ≠ 0)
    (P : ∀i, ShortPositiveRoot → Module.End F (basicFactor m B i).Space)
    (hP : ∀i x, (∀r, P i r x = 0) ↔ x ∈ Submodule.span F {v i})
    (n : ℕ) (z : basicTensorSpace m B n) :
    (∀i<n, ∀r, coordinateMap m B n i (P i r) z = 0) ↔
      z ∈ Submodule.span F {highestTensor m B v n} := by
  induction n with
  | zero =>
    change (∀ i<0, _) ↔ (z : F) ∈ Submodule.span F {(1 : F)}
    constructor
    · intro _
      exact Submodule.mem_span_singleton.mpr ⟨(show F from z), by simp⟩
    · intro _ i hi
      exact (Nat.not_lt_zero i hi).elim
  | succ n ih =>
    have he := TensorProduct.PrimitiveLine.primitive_iff
      (fun i : Fin n × ShortPositiveRoot =>
        coordinateMap m B n i.1.val (P i.1.val i.2))
      (P n) (highestTensor m B v n) (v n) (hv n)
      (fun x => by simpa only [Prod.forall, Fin.forall_iff] using ih x) (hP n) z
    change _ ↔ z ∈ Submodule.span F {highestTensor m B v n ⊗ₜ[F] v n}
    rw [← he]
    constructor
    · intro h
      constructor
      · rintro ⟨i,r⟩
        simpa only [coordinateMap_cast m B n i.val i.isLt] using! h i.val (by omega) r
      · intro r
        simpa only [coordinateMap_last] using! h n (by omega) r
    · rintro ⟨hleft,hright⟩ i hi r
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
      · simpa only [coordinateMap_cast m B n i h] using! hleft (⟨i,h⟩,r)
      · simpa only [coordinateMap_last] using! hright r

/-- All actual positive short-root coordinate coefficients have the single
source highest line as their common kernel, including trivial factors. -/
theorem source_prefix_primitive_iff [CharP F 2]
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (p : ∀i, RootExpansion (basicFactor m B i).action)
    (b : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (n : ℕ) (z : basicTensorSpace m B n) :
    (∀i<n, ∀r : ShortPositiveRoot,
      coordinateMap m B n i ((p i).coeff r.val 1) z = 0) ↔
      z ∈ Submodule.span F {highestTensor m B v n} := by
  apply prefix_primitive_iff m B v (fun i => (hv i).1)
    (fun i r => (p i).coeff r.val 1) _ n z
  intro i x
  have h := BasicSpaces.shortPositiveKernel_eq_span hU (p i) (hv i)
  rw [← h]
  simp only [RootExpansion.shortPositiveKernel, Submodule.mem_iInf, LinearMap.mem_ker]

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
