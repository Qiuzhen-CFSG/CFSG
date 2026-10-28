module

public import Theory.SpecificGroups.PSL3.ExtensionBorel
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Removing the graph contribution of cubic standard automorphisms

The square of a linear–field–graph expression is linear–field, because
inverse transpose normalizes the linear subgroup and commutes with field
transport. If the actor has cube one, its inverse square is itself, so it
already lies in the linear–field subgroup. The existing coefficient
faithfulness calculation then gives a nontrivial field automorphism of
order three whenever the actor is not inner-diagonal.

For a field of order four the field automorphism group has exponent two,
so this non-diagonal cubic case cannot occur. Only membership in the
concrete standard subgroup is used; there is no arbitrary-automorphism
coverage assumption.

Source: GLS3, Theorem 2.5.12 and §2.7, `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith, `refs/quasithin.pdf`, A.3.16–18, printed pp.51–53.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
namespace Matrix.PSL3.StandardCubicFixedNine
variable {F : Type*} [Field F]

private theorem linear_field_graph_square (m : GL (Fin 3) F) (σ : F ≃+* F) :
    (linearConj F m * fieldAction F σ * graph F) ^ 2 =
      linearConj F (m * GeneralLinearGroup.map σ.toRingHom (inverseTransposeGL F m)) *
        fieldAction F (σ ^ 2) := by
  have hcomm := (field_commute_graph σ).eq.symm
  rw [pow_two]
  calc
    _ = linearConj F m * fieldAction F σ * (graph F * linearConj F m) *
        fieldAction F σ * graph F := by group
    _ = linearConj F m *
        (fieldAction F σ * linearConj F (inverseTransposeGL F m)) *
        (graph F * fieldAction F σ) * graph F := by rw [graph_linearConj]; group
    _ = linearConj F m *
        (linearConj F (GeneralLinearGroup.map σ.toRingHom (inverseTransposeGL F m)) *
          fieldAction F σ) * (fieldAction F σ * graph F) * graph F := by
      rw [field_linearConj, hcomm]
    _ = (linearConj F m *
        linearConj F (GeneralLinearGroup.map σ.toRingHom (inverseTransposeGL F m))) *
        (fieldAction F σ * fieldAction F σ) * (graph F ^ 2) := by rw [pow_two]; group
    _ = _ := by rw [graph_sq, mul_one, ← map_mul, ← pow_two, ← map_pow]

/-- An order-three standard actor lies in the linear-field subgroup. -/
theorem cubic_mem_linearField (a : MulAut PSL(3,F)) (ha : a ∈ standard F)
    (ha3 : a ^ 3 = 1) : a ∈ linearField F := by
  obtain ⟨m, σ, h | h⟩ := CartanActions.NormalizerForm.standard_factorization F
    field_linearConj graph_linearConj_exists field_commute_graph a ha
  · rw [h]
    exact (linearField F).mul_mem (Subgroup.mem_sup_left ⟨m, rfl⟩)
      (Subgroup.mem_sup_right ⟨σ, rfl⟩)
  · have hsq : a ^ 2 ∈ linearField F := by
      rw [h, linear_field_graph_square]
      exact (linearField F).mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩)
        (Subgroup.mem_sup_right ⟨_, rfl⟩)
    have hi : a = (a ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right (by
      simpa only [pow_succ] using ha3)
    rw [hi]
    exact (linearField F).inv_mem hsq

/-- A non-diagonal cubic standard actor has a nontrivial cubic field factor. -/
theorem cubic_factorization [CharP F 2] (a : MulAut PSL(3,F))
    (ha : a ∈ standard F) (ha3 : a ^ 3 = 1) (hdiag : a ∉ innerDiagonal F) :
    ∃ (m : GL (Fin 3) F) (σ : F ≃+* F),
      a = linearConj F m * fieldAction F σ ∧ orderOf σ = 3 := by
  obtain ⟨m, σ, h⟩ := linearField_factorization F a (cubic_mem_linearField a ha ha3)
  refine ⟨m, σ, h, orderOf_eq_prime ?_ ?_⟩
  · exact CartanActions.ResidualLinear.coefficient_pow_eq_one m σ (h ▸ ha3)
  · intro hs
    apply hdiag
    rw [h, hs, map_one, mul_one]
    exact ⟨m, rfl⟩

/-- In degree two no non-diagonal cubic standard actor occurs. -/
theorem cubic_innerDiagonal_of_card_four [Finite F]
    (hF : Nat.card F = 2 ^ 2) (a : MulAut PSL(3,F))
    (ha : a ∈ standard F) (ha3 : a ^ 3 = 1) : a ∈ innerDiagonal F := by
  classical
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  by_contra hdiag
  obtain ⟨m, σ, _, hs⟩ := cubic_factorization a ha ha3 hdiag
  have hs2 := FiniteField.ringAut_sq_of_card_prime_pow Nat.prime_two (by decide : 2 ≤ 2) hF σ
  have h := orderOf_dvd_of_pow_eq_one hs2
  rw [hs] at h
  norm_num at h

end Matrix.PSL3.StandardCubicFixedNine
