module

public import Theory.Representation.Suzuki.SmallDegree.Classification.SpecialSupport

/-!
# Highest vectors in the concrete Suzuki tensors

The first coordinate vector is fixed by the actual upper root subgroup. Its
split-torus character is `x^(1+2^m)`. Entrywise Frobenius raises that character
to `2^i`, and tensoring adds the exponents. The specified pure tensor is
nonzero, as witnessed by the tensor of first-coordinate functionals.

These are the literal matrix and scalar-extension conventions needed for the
simplicity and distinctness argument. Uniqueness of the fixed line and
cyclicity are not asserted here. Sources: GLS3, 2.8.2--2.8.8; Guralnick--Malle,
*Classification of 2F-modules, II*, §3.1, equation (3.2).
-/

open scoped TensorProduct
@[expose] public noncomputable section
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural
set_option backward.isDefEq.respectTransparency false

/-- The first coordinate in the upper-root convention. -/
def naturalHighestVector (m : ℕ) : W m := Pi.single 0 1

/-- The pure tensor of first coordinates, with tensor unit `1`. -/
def wordHighestVector (m : ℕ) : (l : List ℕ) → WordSpace m l
  | [] => (1 : F m)
  | _ :: l => naturalHighestVector m ⊗ₜ[F m] wordHighestVector m l

/-- The specified highest tensor after scalar extension. -/
def tensorHighestVector (m : ℕ) (K : Type*) [Field K] [Algebra (F m) K]
    (I : Support m) : TensorSpace m K I :=
  (1 : K) ⊗ₜ[F m] wordHighestVector m (exponents I)

/-- The binary integer encoding the selected ordinary Frobenius positions. -/
def supportWeight {m : ℕ} (I : Support m) : ℕ := ∑ i ∈ I, 2 ^ i.val

/-- The literal split-torus matrix, as an element of the Suzuki group. -/
def highestTorus (m : ℕ) (t : (F m)ˣ) : SuzukiMatrixGroup m :=
  ⟨SuzukiTorusGL m t, Subgroup.subset_closure (Or.inr (Or.inl ⟨t, rfl⟩))⟩

theorem naturalHighestVector_ne_zero (m : ℕ) : naturalHighestVector m ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [naturalHighestVector] at this

/-- Tensor of first-coordinate functionals. -/
def wordHighestCoefficient (m : ℕ) : (l : List ℕ) → WordSpace m l →ₗ[F m] F m
  | [] => LinearMap.id
  | _ :: l => (_root_.TensorProduct.lid (F m) (F m)).toLinearMap.comp
      (TensorProduct.map (LinearMap.proj 0) (wordHighestCoefficient m l))

@[simp] theorem wordHighestCoefficient_highestVector (m : ℕ) (l : List ℕ) :
    wordHighestCoefficient m l (wordHighestVector m l) = 1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (_root_.TensorProduct.lid (F m) (F m))
      (TensorProduct.map (LinearMap.proj 0) (wordHighestCoefficient m l)
        (naturalHighestVector m ⊗ₜ[F m] wordHighestVector m l)) = 1
    simp [TensorProduct.map_tmul, ih, naturalHighestVector]

theorem wordHighestVector_ne_zero (m : ℕ) (l : List ℕ) :
    wordHighestVector m l ≠ 0 := by
  intro h
  have hc := wordHighestCoefficient_highestVector m l
  rw [h, map_zero] at hc
  exact zero_ne_one hc

theorem tensorHighestVector_ne_zero (m : ℕ) (K : Type*) [Field K]
    [Algebra (F m) K] (I : Support m) : tensorHighestVector m K I ≠ 0 := by
  intro h
  change (1 : K) ⊗ₜ[F m] wordHighestVector m (exponents I) = 0 at h
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h
  exact wordHighestVector_ne_zero m _ h

theorem fieldAutomorphism_pow_entry (m i : ℕ) (g : SuzukiMatrixGroup m) (r c : Fin 4) :
    (((suzukiFieldAutomorphism m ^ i) g).val.val r c) = g.val.val r c ^ (2 ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', MulAut.mul_apply, suzukiFieldAutomorphism_entry, ih, ← pow_mul, pow_succ]

theorem factorRep_apply (m i : ℕ) (g : SuzukiMatrixGroup m) (v : W m) (r : Fin 4) :
    factorRep m i g v r = ∑ c : Fin 4, g.val.val r c ^ (2 ^ i) * v c := by
  change ∑ c : Fin 4, (((suzukiFieldAutomorphism m ^ i) g).val.val r c) * v c = _
  simp only [fieldAutomorphism_pow_entry]

theorem factorHighestVector_fixed_root (m i : ℕ) (g : SuzukiMatrixGroup m)
    (hg : g ∈ SuzukiRootSubgroup m) : factorRep m i g (naturalHighestVector m) =
      naturalHighestVector m := by
  obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff m g).mp hg
  ext r
  rw [factorRep_apply]
  fin_cases r <;> simp [naturalHighestVector, hab, SuzukiRootGL, SuzukiRootMatrix,
    Fin.sum_univ_four]

theorem factorHighestVector_torus (m i : ℕ) (t : (F m)ˣ) :
    factorRep m i (highestTorus m t) (naturalHighestVector m) =
      (t.val ^ ((1 + 2 ^ m) * 2 ^ i)) • naturalHighestVector m := by
  ext r
  rw [factorRep_apply]
  fin_cases r <;> simp [naturalHighestVector, highestTorus, SuzukiTorusGL, SuzukiTorusMatrix,
    Fin.sum_univ_four, pow_mul]

theorem wordHighestVector_fixed_root (m : ℕ) (l : List ℕ) (g : SuzukiMatrixGroup m)
    (hg : g ∈ SuzukiRootSubgroup m) : wordRep m l g (wordHighestVector m l) =
      wordHighestVector m l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change factorRep m i g (naturalHighestVector m) ⊗ₜ[F m]
      wordRep m l g (wordHighestVector m l) = _
    rw [factorHighestVector_fixed_root m i g hg, ih]
    rfl

theorem wordHighestVector_torus (m : ℕ) (l : List ℕ) (t : (F m)ˣ) :
    wordRep m l (highestTorus m t) (wordHighestVector m l) =
      t.val ^ ((1 + 2 ^ m) * (l.map (2 ^ ·)).sum) • wordHighestVector m l := by
  induction l with
  | nil => change (1 : F m) = t.val ^ ((1 + 2 ^ m) * 0) • 1; simp
  | cons i l ih =>
    change factorRep m i _ (naturalHighestVector m) ⊗ₜ[F m]
      wordRep m l _ (wordHighestVector m l) = _
    rw [factorHighestVector_torus, ih]
    simp only [List.map_cons, List.sum_cons, mul_add, pow_add, wordHighestVector,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul, mul_comm]

theorem tensorHighestVector_fixed_root (m : ℕ) (K : Type*) [Field K]
    [Algebra (F m) K] (I : Support m) (g : SuzukiMatrixGroup m)
    (hg : g ∈ SuzukiRootSubgroup m) : tensorRep m K I g (tensorHighestVector m K I) =
      tensorHighestVector m K I := by
  change (1 : K) ⊗ₜ[F m] wordRep m (exponents I) g (wordHighestVector m (exponents I)) = _
  rw [wordHighestVector_fixed_root m _ g hg]
  rfl

theorem sum_exponents (m : ℕ) (I : Support m) :
    ((exponents I).map (2 ^ ·)).sum = supportWeight I := by
  simp only [exponents, List.map_map]
  rw [← List.sum_toFinset _ (Finset.sort_nodup I (· ≤ ·)), Finset.sort_toFinset]
  rfl

theorem tensorHighestVector_torus (m : ℕ) (K : Type*) [Field K]
    [Algebra (F m) K] (I : Support m) (t : (F m)ˣ) :
    tensorRep m K I (highestTorus m t) (tensorHighestVector m K I) =
      (algebraMap (F m) K t.val) ^ ((1 + 2 ^ m) * supportWeight I) •
        tensorHighestVector m K I := by
  change (1 : K) ⊗ₜ[F m] wordRep m (exponents I) _ (wordHighestVector m _) = _
  rw [wordHighestVector_torus, sum_exponents]
  simp [tensorHighestVector, Algebra.smul_def,
    TensorProduct.smul_tmul']
end Representation.SuzukiSmallDegree
