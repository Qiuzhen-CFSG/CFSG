module

public import Theory.SpecificGroups.SU3.CentralCubeLocalRelocation.Geometry
public import Theory.SpecificGroups.SU3.CentralCubeLocalRelocation.NormRoot

/-!
# Relocating a central SU₃ cube into a genuine two-local subgroup

A determinant-one matrix whose cube is a nonidentity central scalar forces
a cube root of that scalar in the matrix field. At odd binary degree this
root has norm one and order nine. In an orthonormal frame the diagonal
subgroup at this root centralizes the coordinate-swap involution. Its cube
is the prescribed central element, so it supplies the required cyclic-nine
subgroup in the normalizer of an actual nontrivial two-subgroup.

The final theorem transports both literal subgroups through an arbitrary
multiplicative equivalence, preserving the specified central element.
No numerical local-rank or pre-existing local-placement conclusion is an input.
Source: Aschbacher--Smith A.2.12(II), printed p.37.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.EvenInner
namespace BenderSuzuki.MatrixGroups.HermitianForm.CentralCubeLocalRelocation
open UnitaryThree.OddTorusNormalizer
variable {F : Type*} [Field F] [Finite F]

/-- A central cube in the original SU₃ gives an actual cyclic-nine two-local
witness containing that very central element. -/
theorem exists_local_cyclic_nine (J : HermitianForm 3 F) {n : ℕ}
    (hn : 3 ≤ n) (ho : Odd n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ a, J.conj a = a ^ (2 ^ n)) (z : J.specialSubgroup)
    (hz : z ∈ center J.specialSubgroup) (hz1 : z ≠ 1)
    (x : J.specialSubgroup) (hx : x ^ 3 = z) :
    ∃ Q C : Subgroup J.specialSubgroup, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
      IsCyclic C ∧ Nat.card C = 9 ∧ z ∈ C ∧ C ≤ normalizer (Q : Set J.specialSubgroup) := by
  let := frame_char_two (E := F) n hcard
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  obtain ⟨P, hP⟩ := External.huppert_II_10_4_a_orthonormal_basis 3 J
    (2 ^ n) hcard hfixed
  obtain ⟨a, ha, hscalar⟩ := exists_norm_one_cube_root J hn ho hcard hconj z hz hz1 x hx
  exact local_witness_of_norm_root J ⟨P, hP⟩ a ha z hscalar

/-- Both local subgroups transport to the original factor carrier through
the specified equivalence. The same central element lies in the order-nine
subgroup, and normalization is transported by the same map. -/
theorem exists_local_cyclic_nine_of_equiv {A : Type*} [Group A]
    (J : HermitianForm 3 F) {n : ℕ}
    (hn : 3 ≤ n) (ho : Odd n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ a, J.conj a = a ^ (2 ^ n)) (e : A ≃* J.specialSubgroup)
    (z : A) (hz : z ∈ center A) (hz1 : z ≠ 1) (x : A) (hx : x ^ 3 = z) :
    ∃ Q C : Subgroup A, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ IsCyclic C ∧
      Nat.card C = 9 ∧ z ∈ C ∧ C ≤ normalizer (Q : Set A) := by
  obtain ⟨Q, C, hQ, hp, hc, hcardC, hzC, hN⟩ := exists_local_cyclic_nine
    J hn ho hcard hconj (e z) (centerCongr e ⟨z, hz⟩).property
    (fun he => hz1 (e.map_eq_one_iff.mp he)) (e x) (by rw [← map_pow, hx])
  refine ⟨Q.map e.symm.toMonoidHom, C.map e.symm.toMonoidHom, ?_, hp.map _, ?_, ?_, ?_, ?_⟩
  · intro he
    apply hQ
    exact (map_eq_bot_iff_of_injective Q e.symm.injective).mp he
  · let := hc
    exact isCyclic_of_surjective (e.symm.toMonoidHom.subgroupMap C)
      (e.symm.toMonoidHom.subgroupMap_surjective C)
  · exact (Nat.card_congr (e.symm.subgroupMap C).toEquiv).symm.trans hcardC
  · exact ⟨e z, hzC, e.symm_apply_apply z⟩
  · exact (map_mono hN).trans (le_normalizer_map _)

end BenderSuzuki.MatrixGroups.HermitianForm.CentralCubeLocalRelocation
