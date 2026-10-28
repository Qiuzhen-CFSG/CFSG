module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage

/-!
# Elements of order five inverted by M₂₄ involutions

For the two marked involution classes, short commutator words in the standard
permutations have order five. Involution fusion transports these witnesses to
every involution of the actual Witt-design group.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, author manuscript p.17.
-/

public section
namespace Sporadic.Mathieu.M24Degree44Displacement
open M24InvolutionCentralizers

private theorem inverts_commutator {G : Type*} [Group G] (t g : G)
    (ht : t ^ 2 = 1) :
    t * (t * g * t⁻¹ * g⁻¹) * t⁻¹ = (t * g * t⁻¹ * g⁻¹)⁻¹ := by
  have hi : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht)
  simp only [mul_inv_rev, inv_inv, hi, ← mul_assoc, ← pow_two, ht, one_mul]

private noncomputable def secondConjugator : M24 :=
  ⟨m24GeneratorB * m24GeneratorA * m24GeneratorB,
    M24.mul_mem (M24.mul_mem m24GeneratorB_mem m24GeneratorA_mem) m24GeneratorB_mem⟩

private theorem first_five_order :
    orderOf (involution2A * involution2B * involution2A⁻¹ * involution2B⁻¹) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [← Subgroup.orderOf_coe]
  apply orderOf_eq_prime
  · change (m24Involution2A * m24Involution2B * m24Involution2A⁻¹ *
      m24Involution2B⁻¹) ^ 5 = 1
    decide +kernel
  · change m24Involution2A * m24Involution2B * m24Involution2A⁻¹ *
      m24Involution2B⁻¹ ≠ 1
    decide +kernel

private theorem second_five_order :
    orderOf (involution2B * secondConjugator * involution2B⁻¹ * secondConjugator⁻¹) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [← Subgroup.orderOf_coe]
  apply orderOf_eq_prime
  · change (m24Involution2B * (m24GeneratorB * m24GeneratorA * m24GeneratorB) *
      m24Involution2B⁻¹ * (m24GeneratorB * m24GeneratorA * m24GeneratorB)⁻¹) ^ 5 = 1
    decide +kernel
  · change m24Involution2B * (m24GeneratorB * m24GeneratorA * m24GeneratorB) *
      m24Involution2B⁻¹ * (m24GeneratorB * m24GeneratorA * m24GeneratorB)⁻¹ ≠ 1
    decide +kernel

private theorem exists_five_of_conjugate (s t : M24) (hc : IsConj s t)
    (h : ∃ x : M24, orderOf x = 5 ∧ s * x * s⁻¹ = x⁻¹) :
    ∃ x : M24, orderOf x = 5 ∧ t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hc
  obtain ⟨x, hx, hi⟩ := h
  refine ⟨(MulAut.conj g) x, ?_, ?_⟩
  · exact (MulEquiv.orderOf_eq (MulAut.conj g) x).trans hx
  · have hm := congrArg (MulAut.conj g) hi
    simpa only [map_mul, map_inv, MulAut.conj_apply] using hm

/-- Every involution in the actual M₂₄ carrier inverts an element of order five. -/
theorem exists_inverted_five (t : M24) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ x : M24, orderOf x = 5 ∧ t * x * t⁻¹ = x⁻¹ := by
  rcases involution_classes t (orderOf_eq_prime ht2 ht) with h | h
  · apply exists_five_of_conjugate involution2A t h
    exact ⟨_, first_five_order,
      inverts_commutator _ _ ((orderOf_eq_prime_iff.mp involution2A_order).1)⟩
  · apply exists_five_of_conjugate involution2B t h
    exact ⟨_, second_five_order,
      inverts_commutator _ _ ((orderOf_eq_prime_iff.mp involution2B_order).1)⟩

end Sporadic.Mathieu.M24Degree44Displacement
