module

public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes.Certificates0
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes.Certificates1
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes.Certificates2
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes.Certificates3
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes.Certificates4
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes.Certificates5
public import Theory.SpecificGroups.Janko1.Model.Certification.Order

/-!
# No involution centralizes the standard elements of orders 7, 11 or 19

The finite matrix family contains the standard involution and is closed under
conjugation by both generators. Generation and the certified involution fusion
therefore place every involution in this family. The checked matrix products
exclude commutation with each of the three standard prime-order representatives.
This supplies the centralizer input for the corresponding normalizer bounds in
GLS3 Table 5.3f (Aschbacher–Smith, printed p.510).

The family and arithmetic are adapted from the existing J₁ outer certificate;
see `Source/README.md`. All certificates concern the actual ATLAS matrix model.
-/

namespace Janko1.LocalStructure.LargePrimes
open OrderCertificate Packed

private theorem certified (i : Fin 1463) : Certified i := by
  refine forall_of_blocks Certified ?_ i
  intro b r
  fin_cases b
  · exact certificateBlock0 r
  · exact certificateBlock1 r
  · exact certificateBlock2 r
  · exact certificateBlock3 r
  · exact certificateBlock4 r
  · exact certificateBlock5 r
  · exact certificateBlock6 r
  · exact certificateBlock7 r
  · exact certificateBlock8 r
  · exact certificateBlock9 r
  · exact certificateBlock10 r
  · exact certificateBlock11 r
  · exact certificateBlock12 r
  · exact certificateBlock13 r
  · exact certificateBlock14 r
  · exact certificateBlock15 r
  · exact certificateBlock16 r
  · exact certificateBlock17 r
  · exact certificateBlock18 r
  · exact certificateBlock19 r
  · exact certificateBlock20 r
  · exact certificateBlock21 r
  · exact certificateBlock22 r
  · exact certificateBlock23 r
  · exact certificateBlock24 r
  · exact certificateBlock25 r
  · exact certificateBlock26 r
  · exact certificateBlock27 r
  · exact certificateBlock28 r
  · exact certificateBlock29 r
  · exact certificateBlock30 r
  · exact certificateBlock31 r
  · exact certificateBlock32 r
  · exact certificateBlock33 r
  · exact certificateBlock34 r
  · exact certificateBlock35 r
  · exact certificateBlock36 r
  · exact certificateBlock37 r
  · exact certificateBlock38 r
  · exact certificateBlock39 r
  · exact certificateBlock40 r
  · exact certificateBlock41 r
  · exact certificateBlock42 r
  · exact certificateBlock43 r
  · exact certificateBlock44 r
  · exact certificateBlock45 r

private theorem a_inv_eq : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using a_pow_two)

private theorem b_inv_eq : b⁻¹ = b ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  exact (pow_succ' b 2).symm.trans b_pow_three

private theorem image_a : matrixValue a = matrixA := rfl
private theorem image_b : matrixValue b = matrixB := rfl

private theorem closed_a (i : Fin 1463) :
    matrixA * decode (code i) * matrixA = decode (code (targetA i)) := by
  have h := check_sound _ _ _ _ (certified i).1
  rw [decode_generatorA] at h
  rw [h, mul_assoc, show matrixA * matrixA = 1 by decide +kernel, mul_one]

private theorem closed_b (i : Fin 1463) :
    matrixB * decode (code i) * (matrixB * matrixB) = decode (code (targetB i)) := by
  have h := check_sound _ _ _ _ (certified i).2.1
  rw [decode_generatorB] at h
  rw [h, mul_assoc, show matrixB * (matrixB * matrixB) = 1 by decide +kernel, mul_one]

/-- Every involution of the actual J₁ model occurs in the checked matrix family. -/
public theorem involution_mem_family (t : Model) (ht : orderOf t = 2) :
    ∃ i : Fin 1463, matrixValue t = decode (code i) := by
  let T : Set Model := {y | ∃ i : Fin 1463, matrixValue y = decode (code i)}
  have ha : a ∈ T := ⟨0, image_a.trans decode_zero.symm⟩
  have hna : a ∈ Subgroup.normalizer T := by
    apply Subgroup.mem_normalizer_fintype
    rintro y ⟨i, hi⟩
    refine ⟨targetA i, ?_⟩
    simpa only [map_mul, a_inv_eq, hi, image_a] using closed_a i
  have hnb : b ∈ Subgroup.normalizer T := by
    apply Subgroup.mem_normalizer_fintype
    rintro y ⟨i, hi⟩
    refine ⟨targetB i, ?_⟩
    simpa only [map_mul, b_inv_eq, map_pow, hi, pow_two, image_b] using closed_b i
  have hn : Subgroup.normalizer T = ⊤ := by
    apply top_unique
    rw [← closure_pair_eq_top]
    apply (Subgroup.closure_le _).mpr
    rintro y (rfl | hy)
    · exact hna
    · exact Set.mem_singleton_iff.mp hy ▸ hnb
  obtain ⟨g, hg⟩ := involution_fusion_of_card card_model t ht
  have hgN : g ∈ Subgroup.normalizer T := by rw [hn]; trivial
  apply (Subgroup.mem_set_normalizer_iff.mp hgN t).mpr
  simpa only [hg] using ha

/-- The order-seven representative has no commuting involution. -/
public theorem no_involution_commutes_seven (t : Model) (ht : orderOf t = 2) :
    ¬ Commute t (a * b) := by
  obtain ⟨i, hi⟩ := involution_mem_family t ht
  intro hc
  have h := (hc.map matrixValue).eq
  rw [hi, ← decode_r7] at h
  exact check_false _ _ (certified i).2.2.1 h

/-- The order-eleven representative has no commuting involution. -/
public theorem no_involution_commutes_eleven (t : Model) (ht : orderOf t = 2) :
    ¬ Commute t (x * y ^ 2) := by
  obtain ⟨i, hi⟩ := involution_mem_family t ht
  intro hc
  have h := (hc.map matrixValue).eq
  rw [hi, ← decode_r11] at h
  exact check_false _ _ (certified i).2.2.2.1 h

/-- The order-nineteen representative has no commuting involution. -/
public theorem no_involution_commutes_nineteen (t : Model) (ht : orderOf t = 2) :
    ¬ Commute t (a * b * a * b ^ 2) := by
  obtain ⟨i, hi⟩ := involution_mem_family t ht
  intro hc
  have h := (hc.map matrixValue).eq
  rw [hi, ← decode_r19] at h
  exact check_false _ _ (certified i).2.2.2.2 h

end Janko1.LocalStructure.LargePrimes
