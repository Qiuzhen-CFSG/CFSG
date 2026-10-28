module
public import Theory.GroupTheory.SemidihedralStandardModel
public import Theory.GroupTheory.SemidihedralCenter

/-!
# The two involution classes in a semidihedral group of order sixteen

The bounded normal forms are a^i and a^i b, with 0 ≤ i < 8. An
involutory rotation is a^4. An involution a^i b has even i = 2k, and
conjugation by a^k sends it to b. This uses the public presentation
relations, without reducing hidden coordinates of the standard model.
The center equation and involution classes are also specialized to that model.

Source: the semidihedral presentation in Alperin–Brauer–Gorenstein,
Chapter II, §1; Aschbacher–Smith, J.2.7, printed p.435 (PDF p.446).
-/

public section
namespace Semidihedral
variable {G : Type*} [Group G]

/-- The two involution classes of SD16, with the given presentation generators. -/
theorem involution_classes_sixteen (a b x : G) (ha : orderOf a = 8)
    (hb : orderOf b = 2) (hab : b * a * b⁻¹ = a ^ 3)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (hx : orderOf x = 2) :
    x = a ^ 4 ∨ IsConj x b := by
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  obtain ⟨i, hi, rfl | rfl⟩ := normal_form a b 8 3 (by decide) ha hb2 hab hgen x
  · have hd : 8 ∣ i*2 := by
      have h := orderOf_dvd_of_pow_eq_one (show a^(i*2) = 1 by rw [pow_mul]; exact hx2)
      rwa [ha] at h
    have hi4 : i = 4 := by
      have hn : i ≠ 0 := by intro he; simp [he] at hx
      omega
    exact Or.inl (by rw [hi4])
  · have hs : (a ^ i * b) ^ 2 = a ^ (4*i) := by
      calc
        _ = a^i * (b*a^i) * b := by simp only [pow_two, mul_assoc]
        _ = a^i * (a^(3*i)*b) * b := by rw [move_pow a b 3 hab i]
        _ = a^(i+3*i) := by rw [mul_assoc, mul_assoc, ← pow_two, hb2, mul_one, ← pow_add]
        _ = _ := by congr 1; omega
    have hd : 8 ∣ 4*i := by
      rw [hs] at hx2
      simpa only [ha] using orderOf_dvd_of_pow_eq_one hx2
    have htwo : 2 ∣ i := by omega
    obtain ⟨k, rfl⟩ := htwo
    apply Or.inr
    apply isConj_iff.mpr
    refine ⟨a^k, mul_inv_eq_iff_eq_mul.mpr ?_⟩
    rw [← mul_assoc, ← pow_add, move_pow a b 3 hab k]
    congr 2
    omega

/-- The center equation for the fixed standard model of order sixteen. -/
theorem center_standard_sixteen : Subgroup.center (StandardModel 4 (by decide)) =
    Subgroup.zpowers (standardRotation 4 (by decide) ^ 4) :=
  center_eq (by decide : 4 ≤ 4) _ _ (standardRotation_order 4 (by decide))
    (standardReflection_order 4 (by decide)) (standard_conjugation 4 (by decide))
    (standard_generators 4 (by decide))

/-- An involution in the standard SD16 is central or conjugate to its reflection. -/
theorem involution_standard_sixteen (x : StandardModel 4 (by decide)) (hx : orderOf x = 2) :
    x = standardRotation 4 (by decide) ^ 4 ∨ IsConj x (standardReflection 4 (by decide)) :=
  involution_classes_sixteen _ _ x (standardRotation_order 4 (by decide))
    (standardReflection_order 4 (by decide)) (standard_conjugation 4 (by decide))
    (standard_generators 4 (by decide)) hx
end Semidihedral
