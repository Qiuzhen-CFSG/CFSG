module
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.CharP.Two
public import Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv
import all Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# The nine-point ternary Ree model as PSL₂(8)

Choose a root `z` of `X³ + X + 1` in GF(8), and mark the projective line by
`[0, 1, z²+z+1, z+1, ∞, z², z²+z, z²+1, z]`. The matrices
`[[0,1],[1,1]]` and `[[1,z],[0,1]]` induce exactly the two specified permutations.
Their orders and the order of their commutator give a subgroup of order divisible
by 126. Its index in PSL₂(8) is at most four, hence it is the whole perfect group.

The finite coordinate checks are proved over an abstract characteristic-two
field before specialization; reducing the concrete splitting field during these
checks is unnecessary. The private cardinality and perfectness lemmas from the
parent comparison module are deliberately reused through `import all`.

Source: GLS III §2.2, the exceptional isomorphism A₁(8) ≅ ²G₂(3)′;
Aschbacher–Smith B.1.13, printed pp. 73–74.
-/

open scoped CharTwo
open Polynomial
namespace Atlas.ReeG2.TernaryDerived.B2Projective
abbrev F := GaloisField 2 3

private theorem exists_cubic_root : ∃ z : F, z ^ 3 + z + 1 = 0 := by
  let q : (ZMod 2)[X] := X ^ 8 - X
  let f : (ZMod 2)[X] := X ^ 3 + X + 1
  have hd : f ∣ q := by
    refine ⟨X ^ 5 + X ^ 3 + X ^ 2 + X, ?_⟩
    dsimp [q, f]
    ring_nf
    simp
  have hq : q.natDegree = 8 := by dsimp [q]; compute_degree; norm_num
  have hf : f.natDegree = 3 := by dsimp [f]; compute_degree; norm_num
  have hsplit : (q.map (algebraMap (ZMod 2) F)).Splits :=
    SplittingField.splits (X ^ 8 - X : (ZMod 2)[X])
  have hqn : q.map (algebraMap (ZMod 2) F) ≠ 0 := by
    intro h
    have := Polynomial.natDegree_map (p := q) (algebraMap (ZMod 2) F)
    rw [h, Polynomial.natDegree_zero, hq] at this
    omega
  obtain ⟨z, hz⟩ := (hsplit.of_dvd hqn (Polynomial.map_dvd _ hd)).exists_eval_eq_zero
    (Polynomial.degree_ne_of_natDegree_ne (by
      rw [Polynomial.natDegree_map, hf]
      decide))
  exact ⟨z, by simpa [f] using hz⟩

noncomputable def z : F := Classical.choose exists_cubic_root
lemma z_cubic : z ^ 3 + z + 1 = 0 := Classical.choose_spec exists_cubic_root
lemma z_ne_zero : z ≠ 0 := by
  intro h
  have := z_cubic
  simp [h] at this
lemma z_add_one_ne_zero : z + 1 ≠ 0 := by
  intro h
  have hz : z = 1 := by simpa only [CharTwo.add_eq_zero] using h
  have := z_cubic
  simp [hz] at this
lemma z_sq_ne_zero : z ^ 2 ≠ 0 := pow_ne_zero _ z_ne_zero
lemma z_sq_add_one_ne_zero : z ^ 2 + 1 ≠ 0 := by
  have h : (z + 1) ^ 2 ≠ 0 := pow_ne_zero _ z_add_one_ne_zero
  simpa only [CharTwo.add_sq, one_pow] using h
lemma z_sq_add_z_ne_zero : z ^ 2 + z ≠ 0 := by
  have h := mul_ne_zero z_ne_zero z_add_one_ne_zero
  convert h using 1
  ring
lemma z_sq_add_z_add_one_ne_zero : z ^ 2 + z + 1 ≠ 0 := by
  intro h
  have he : z = 0 := by
    calc
      z = (z ^ 3 + z + 1) + (z + 1) * (z ^ 2 + z + 1) := by
        ring_nf
        simp
      _ = 0 := by rw [z_cubic, h]; simp
  exact z_ne_zero he

open scoped MatrixGroups LinearAlgebra.Projectivization
open Matrix
abbrev L := ℙ F (Fin 2 → F)
section
variable {K : Type*} [Field K] [CharP K 2]

def vector (a : K) : Fin 9 → Fin 2 → K :=
  ![![0,1], ![1,1], ![a ^ 2 + a + 1,1], ![a+1,1], ![1,0],
    ![a ^ 2,1], ![a ^ 2+a,1], ![a ^ 2+1,1], ![a,1]]

private lemma determinant_row_0 (a : K)
    (h0 : a ≠ 0) (h1 : a + 1 ≠ 0) (h2 : a ^ 2 ≠ 0)
    (h3 : a ^ 2 + 1 ≠ 0) (h4 : a ^ 2 + a ≠ 0)
    (h5 : a ^ 2 + a + 1 ≠ 0) (j : Fin 9)
    (h : vector a 0 0 * vector a j 1 = vector a j 0 * vector a 0 1) : (0 : Fin 9) = j := by
  ring_nf at h0 h1 h2 h3 h4 h5
  fin_cases j
  · rfl
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h5 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h1 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h2 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h4 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h3 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h0 (by simpa using he)

private lemma determinant_row_1 (a : K)
    (h0 : a ≠ 0) (h1 : a + 1 ≠ 0) (h2 : a ^ 2 ≠ 0)
    (h3 : a ^ 2 + 1 ≠ 0) (h4 : a ^ 2 + a ≠ 0)
    (h5 : a ^ 2 + a + 1 ≠ 0) (j : Fin 9)
    (h : vector a 1 0 * vector a j 1 = vector a j 0 * vector a 1 1) : (1 : Fin 9) = j := by
  ring_nf at h0 h1 h2 h3 h4 h5
  fin_cases j
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · rfl
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h4 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h0 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h3 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h5 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h2 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h1 (by simpa using he)

private lemma determinant_row_2 (a : K)
    (h0 : a ≠ 0) (h1 : a + 1 ≠ 0) (h2 : a ^ 2 ≠ 0)
    (h3 : a ^ 2 + 1 ≠ 0) (h4 : a ^ 2 + a ≠ 0)
    (h5 : a ^ 2 + a + 1 ≠ 0) (j : Fin 9)
    (h : vector a 2 0 * vector a j 1 = vector a j 0 * vector a 2 1) : (2 : Fin 9) = j := by
  ring_nf at h0 h1 h2 h3 h4 h5
  fin_cases j
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h5 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h4 (by simpa using he)
  · rfl
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h2 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h1 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    simp at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h0 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h3 (by simpa using he)

private lemma determinant_row_3 (a : K)
    (h0 : a ≠ 0) (h1 : a + 1 ≠ 0) (h2 : a ^ 2 ≠ 0)
    (h3 : a ^ 2 + 1 ≠ 0) (h4 : a ^ 2 + a ≠ 0)
    (h5 : a ^ 2 + a + 1 ≠ 0) (j : Fin 9)
    (h : vector a 3 0 * vector a j 1 = vector a j 0 * vector a 3 1) : (3 : Fin 9) = j := by
  ring_nf at h0 h1 h2 h3 h4 h5
  fin_cases j
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h1 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h0 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h2 (by simpa using he)
  · rfl
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h5 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h3 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h4 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    simp at he

private lemma determinant_row_4 (a : K) (j : Fin 9)
    (h : vector a 4 0 * vector a j 1 = vector a j 0 * vector a 4 1) : (4 : Fin 9) = j := by
  fin_cases j
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · rfl
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he

private lemma determinant_row_5 (a : K)
    (h0 : a ≠ 0) (h1 : a + 1 ≠ 0) (h2 : a ^ 2 ≠ 0)
    (h3 : a ^ 2 + 1 ≠ 0) (h4 : a ^ 2 + a ≠ 0)
    (h5 : a ^ 2 + a + 1 ≠ 0) (j : Fin 9)
    (h : vector a 5 0 * vector a j 1 = vector a j 0 * vector a 5 1) : (5 : Fin 9) = j := by
  ring_nf at h0 h1 h2 h3 h4 h5
  fin_cases j
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h2 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h3 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h1 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h5 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · rfl
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h0 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h4 (by simpa using he)

private lemma determinant_row_6 (a : K)
    (h0 : a ≠ 0) (h1 : a + 1 ≠ 0) (h2 : a ^ 2 ≠ 0)
    (h3 : a ^ 2 + 1 ≠ 0) (h4 : a ^ 2 + a ≠ 0)
    (h5 : a ^ 2 + a + 1 ≠ 0) (j : Fin 9)
    (h : vector a 6 0 * vector a j 1 = vector a j 0 * vector a 6 1) : (6 : Fin 9) = j := by
  ring_nf at h0 h1 h2 h3 h4 h5
  fin_cases j
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h4 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h5 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h3 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h0 (by simpa using he)
  · rfl
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h1 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h2 (by simpa using he)

private lemma determinant_row_7 (a : K)
    (h0 : a ≠ 0) (h1 : a + 1 ≠ 0) (h2 : a ^ 2 ≠ 0)
    (h3 : a ^ 2 + 1 ≠ 0) (h4 : a ^ 2 + a ≠ 0)
    (h5 : a ^ 2 + a + 1 ≠ 0) (j : Fin 9)
    (h : vector a 7 0 * vector a j 1 = vector a j 0 * vector a 7 1) : (7 : Fin 9) = j := by
  ring_nf at h0 h1 h2 h3 h4 h5
  fin_cases j
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h3 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h2 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h0 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h4 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    simp at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h1 (by simpa using he)
  · rfl
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h5 (by simpa using he)

private lemma determinant_row_8 (a : K)
    (h0 : a ≠ 0) (h1 : a + 1 ≠ 0) (h2 : a ^ 2 ≠ 0)
    (h3 : a ^ 2 + 1 ≠ 0) (h4 : a ^ 2 + a ≠ 0)
    (h5 : a ^ 2 + a + 1 ≠ 0) (j : Fin 9)
    (h : vector a 8 0 * vector a j 1 = vector a j 0 * vector a 8 1) : (8 : Fin 9) = j := by
  ring_nf at h0 h1 h2 h3 h4 h5
  fin_cases j
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h0 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h1 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h3 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h4 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h2 (by simpa using he)
  · exfalso
    have he := CharTwo.add_eq_zero.mpr h
    simp [vector] at he
    ring_nf at he
    exact h5 (by simpa using he)
  · rfl

private lemma determinant_separates_generic (a : K)
    (h0 : a ≠ 0) (h1 : a + 1 ≠ 0) (h2 : a ^ 2 ≠ 0)
    (h3 : a ^ 2 + 1 ≠ 0) (h4 : a ^ 2 + a ≠ 0)
    (h5 : a ^ 2 + a + 1 ≠ 0) (i j : Fin 9)
    (h : vector a i 0 * vector a j 1 = vector a j 0 * vector a i 1) : i = j := by
  fin_cases i
  · exact determinant_row_0 a h0 h1 h2 h3 h4 h5 j h
  · exact determinant_row_1 a h0 h1 h2 h3 h4 h5 j h
  · exact determinant_row_2 a h0 h1 h2 h3 h4 h5 j h
  · exact determinant_row_3 a h0 h1 h2 h3 h4 h5 j h
  · exact determinant_row_4 a j h
  · exact determinant_row_5 a h0 h1 h2 h3 h4 h5 j h
  · exact determinant_row_6 a h0 h1 h2 h3 h4 h5 j h
  · exact determinant_row_7 a h0 h1 h2 h3 h4 h5 j h
  · exact determinant_row_8 a h0 h1 h2 h3 h4 h5 j h

end

noncomputable def pointVector : Fin 9 → Fin 2 → F := vector z
lemma pointVector_ne (i : Fin 9) : pointVector i ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases i <;> simp [pointVector, vector] at h0 h1


private lemma determinant_separates (i j : Fin 9)
    (h : pointVector i 0 * pointVector j 1 = pointVector j 0 * pointVector i 1) : i = j :=
  determinant_separates_generic z z_ne_zero z_add_one_ne_zero z_sq_ne_zero
    z_sq_add_one_ne_zero z_sq_add_z_ne_zero z_sq_add_z_add_one_ne_zero i j h

noncomputable def point (i : Fin 9) : L :=
  Projectivization.mk F (pointVector i) (pointVector_ne i)
lemma point_injective : Function.Injective point := by
  intro i j h
  apply determinant_separates i j
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at h0 h1
  rw [← h0, ← h1]
  ring

noncomputable def marking : Fin 9 ≃ L := Equiv.ofBijective point
  ((Nat.bijective_iff_injective_and_card point).mpr ⟨point_injective, by
    rw [Nat.card_fin, Atlas.card_projectiveSpace]
    have hc : Nat.card F = 8 := by simpa using GaloisField.card 2 3 (by decide)
    rw [hc]
    norm_num⟩)

lemma z_cube : z ^ 3 = z + 1 := by
  apply CharTwo.add_eq_zero.mp
  simpa only [add_assoc] using z_cubic
lemma z_four : z ^ 4 = z ^ 2 + z := by
  calc z ^ 4 = z ^ 3 * z := by ring
       _ = (z+1) * z := by rw [z_cube]
       _ = z ^ 2 + z := by ring

noncomputable def gammaMatrix : SL(2,F) := ⟨!![0,1;1,1], by simp [Matrix.det_fin_two]⟩
noncomputable def weylMatrix : SL(2,F) := ⟨!![1,z;0,1], by simp [Matrix.det_fin_two]⟩
noncomputable def gammaScale : Fin 9 → F :=
  ![1,1,z ^ 2+z,z,1,z ^ 2+1,z ^ 2+z+1,z ^ 2,z+1]

lemma gamma_vector (i : Fin 9) :
    gammaMatrix.val *ᵥ pointVector i = gammaScale i • pointVector (gammaPerm i) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [gammaMatrix, pointVector, vector, gammaScale, gammaPerm, Matrix.mulVec]
  all_goals ring_nf
  all_goals simp only [z_cube, z_four]
  all_goals ring_nf
  all_goals simp

lemma weyl_vector (i : Fin 9) :
    weylMatrix.val *ᵥ pointVector i = pointVector (weylPerm i) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [weylMatrix, pointVector, vector, weylPerm, Matrix.mulVec]
  all_goals ring_nf
  all_goals simp

noncomputable def permutation : PSL(2,F) →* Equiv.Perm (Fin 9) :=
  marking.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom (PSL(2,F)) L)
lemma permutation_injective : Function.Injective permutation := by
  intro g h he
  apply (MulAction.toPerm_injective (β := L))
  exact marking.symm.permCongrHom.injective he

private lemma permutation_of_vector (g : SL(2,F)) (p : Equiv.Perm (Fin 9))
    (c : Fin 9 → F) (h : ∀ i, g.val *ᵥ pointVector i = c i • pointVector (p i)) :
    permutation (g : PSL(2,F)) = p := by
  apply Equiv.ext
  intro i
  apply marking.injective
  change marking (marking.symm ((g : PSL(2,F)) • marking i)) = _
  rw [marking.apply_symm_apply]
  change (g : PSL(2,F)) • point i = point (p i)
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, point, Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact ⟨c i, by simpa only [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
    using (h i).symm⟩

lemma permutation_gamma : permutation (gammaMatrix : PSL(2,F)) = gammaPerm :=
  permutation_of_vector gammaMatrix gammaPerm gammaScale gamma_vector
lemma permutation_weyl : permutation (weylMatrix : PSL(2,F)) = weylPerm :=
  permutation_of_vector weylMatrix weylPerm (fun _ => 1) (by simpa using weyl_vector)

open Subgroup
open scoped commutatorElement
private lemma card_permutationModel_multiple : 126 ∣ Nat.card PermutationModel := by
  have hg : gammaPerm ∈ permutationSubgroup := subset_closure (by simp)
  have hw : weylPerm ∈ permutationSubgroup := subset_closure (by simp)
  have h2 := permutationSubgroup.orderOf_dvd_natCard hw
  have h7 := permutationSubgroup.orderOf_dvd_natCard (permutationSubgroup.mul_mem hg hw)
  have h9 := permutationSubgroup.orderOf_dvd_natCard
    (permutationSubgroup.mul_mem (permutationSubgroup.mul_mem
      (permutationSubgroup.mul_mem hg hw) (permutationSubgroup.inv_mem hg))
      (permutationSubgroup.inv_mem hw))
  change orderOf ⁅gammaPerm, weylPerm⁆ ∣ Nat.card PermutationModel at h9
  rw [weylPerm_order] at h2
  rw [product_order] at h7
  rw [commutator_order] at h9
  exact (show Nat.Coprime 14 9 by decide).mul_dvd_of_dvd_of_dvd
    ((show Nat.Coprime 2 7 by decide).mul_dvd_of_dvd_of_dvd h2 h7) h9

private lemma permutation_range : permutation.range = permutationSubgroup := by
  have hle : permutationSubgroup ≤ permutation.range := by
    apply (closure_le _).mpr
    intro x hx
    rcases (show x = gammaPerm ∨ x = weylPerm by simpa using hx) with rfl | rfl
    · exact ⟨(gammaMatrix : PSL(2,F)), permutation_gamma⟩
    · exact ⟨(weylMatrix : PSL(2,F)), permutation_weyl⟩
  let U := permutationSubgroup.comap permutation
  have hmap : U.map permutation = permutationSubgroup := map_comap_eq_self hle
  have hcard : Nat.card U = Nat.card PermutationModel := by
    rw [← card_map_of_injective (K := U) permutation_injective, hmap]
  have hlo : 126 ≤ Nat.card U := by
    rw [hcard]
    exact Nat.le_of_dvd Nat.card_pos card_permutationModel_multiple
  have he := U.card_mul_index
  change Nat.card U * U.index = Nat.card PSL(2,F) at he
  rw [psl_card] at he
  have hi : U.index ≤ 4 := by
    have hh := Nat.mul_le_mul_right U.index hlo
    rw [he] at hh
    omega
  let : Group.IsPerfect PSL(2,F) := psl_perfect
  have htop : U = ⊤ := top_le_iff.mp (le_of_isPerfect_of_index_le_four ⊤ U hi)
  rw [htop, ← MonoidHom.range_eq_map] at hmap
  exact hmap

end Atlas.ReeG2.TernaryDerived.B2Projective

namespace Atlas.ReeG2.TernaryDerived
/-- The literal nine-point model is the projective special linear group over GF(8). -/
public noncomputable def b2ProjectiveEquiv : PermutationModel ≃* Theory.PSL2.BinaryGroup 3 :=
  (MulEquiv.subgroupCongr B2Projective.permutation_range.symm).trans
    (MonoidHom.ofInjective B2Projective.permutation_injective).symm
end Atlas.ReeG2.TernaryDerived
