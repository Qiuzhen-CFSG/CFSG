module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Coverage.Steps

/-!
# Interpretation of the overlap coverage certificate

Word induction transports the checked Cayley edges to arbitrary products.
Consequently the numerical power tests and conjugator witnesses concern the
literal overlap, including its original marked square. The ten tests are
invariant under each actual automorphism and hold on the original generators.

Source context: Aschbacher--Smith F.1.12(I)(13), pp.262–263, and 14.2.21,
p.988. The ATLAS coordinates and nonsplit first endpoint are inherited from
`Basic`; no automorphism coverage or endpoint extension is assumed here.
-/
@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions.Coverage

theorem element_multiply (i j : Fin 128) :
    Overlap.element (multiply i j) = Overlap.element i * Overlap.element j := by
  have aux (n : ℕ) : ∀ k : Fin 128, k.val ≤ n →
      Overlap.element (multiply i k) = Overlap.element i * Overlap.element k := by
    induction n with
    | zero =>
      intro k hk
      have hz : k = 0 := Fin.ext (by omega)
      subst k
      rw [multiply_zero, Overlap.element_zero, mul_one]
    | succ n ih =>
      intro k hk
      by_cases hz : k = 0
      · subst k
        rw [multiply_zero, Overlap.element_zero, mul_one]
      · have hp : (parent k).val ≤ n := by
          have := parent_lt k hz
          omega
        rw [multiply_recurrence i k hz, element_step, ih (parent k) hp,
          mul_assoc, ← element_step, parent_step k hz]
  exact aux j.val j le_rfl

theorem element_inverse (i : Fin 128) :
    Overlap.element (Data.inverse i) = (Overlap.element i)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← element_multiply, inverse_check, Overlap.element_zero]

theorem element_power (i : Fin 128) (n : ℕ) :
    Overlap.element (power i n) = Overlap.element i ^ n := by
  induction n with
  | zero => exact Overlap.element_zero
  | succ n ih => rw [power, element_multiply, ih, pow_succ]

private theorem element_eq_one (i : Fin 128) : Overlap.element i = 1 ↔ i = 0 := by
  rw [← Overlap.element_zero, Overlap.element_injective.eq_iff]

/-- For powers of two greater than one, these two tests specify exact order. -/
def groupPowerTest (x : overlap) (n : ℕ) : Prop := x ^ n = 1 ∧ x ^ (n / 2) ≠ 1

private theorem orderNumber_two (i : Fin 128) :
    orderNumber i = 2 ↔ groupPowerTest (Overlap.element i) 2 := by
  simpa only [groupPowerTest, ne_eq, ← element_power, element_eq_one]
    using order_check_two i

private theorem orderNumber_four (i : Fin 128) :
    orderNumber i = 4 ↔ groupPowerTest (Overlap.element i) 4 := by
  simpa only [groupPowerTest, ne_eq, ← element_power, element_eq_one]
    using order_check_four i

private theorem orderNumber_eight (i : Fin 128) :
    orderNumber i = 8 ↔ groupPowerTest (Overlap.element i) 8 := by
  simpa only [groupPowerTest, ne_eq, ← element_power, element_eq_one]
    using order_check_eight i

/-- The ten intrinsic tests used to restrict generator images. -/
def groupAdmissible (a b c : overlap) : Prop :=
  groupPowerTest a 4 ∧ groupPowerTest b 2 ∧ groupPowerTest c 2 ∧
  groupPowerTest (a * b) 4 ∧ groupPowerTest (a * c) 8 ∧
  groupPowerTest (b * c) 4 ∧ groupPowerTest (a * a * b) 2 ∧
  groupPowerTest (a * a * c) 2 ∧ groupPowerTest (a * b * c) 4 ∧
  groupPowerTest (a * b * c * b * c) 4

theorem admissible_iff (a b c : Fin 128) : admissible a b c ↔
    groupAdmissible (Overlap.element a) (Overlap.element b) (Overlap.element c) := by
  simp only [admissible, groupAdmissible, orderNumber_two, orderNumber_four,
    orderNumber_eight, element_multiply]

private theorem groupPowerTest_map (d : MulAut overlap) (x : overlap) (n : ℕ) :
    groupPowerTest (d x) n ↔ groupPowerTest x n := by
  simp only [groupPowerTest, ne_eq, ← map_pow, EmbeddingLike.map_eq_one_iff]

theorem groupAdmissible_map (d : MulAut overlap) (a b c : overlap)
    (h : groupAdmissible a b c) : groupAdmissible (d a) (d b) (d c) := by
  simpa only [groupAdmissible, ← map_mul, groupPowerTest_map] using h

theorem generators_admissible :
    groupAdmissible (Overlap.generator 0) (Overlap.generator 1) (Overlap.generator 2) := by
  have h := (admissible_iff 1 2 3).mp (by decide +kernel)
  exact Eq.mp
    (congrArg₂ (fun (f : overlap → Prop) (x : overlap) => f x)
      (congrArg₂ groupAdmissible (Overlap.element_generator 0) (Overlap.element_generator 1))
      (Overlap.element_generator 2)) h

private theorem element_marked : Overlap.element 4 = marked := by
  have h : multiply 1 1 = 4 := by decide +kernel
  calc
    Overlap.element 4 = Overlap.element (multiply 1 1) := congrArg Overlap.element h.symm
    _ = Overlap.element 1 * Overlap.element 1 := element_multiply 1 1
    _ = Overlap.generator 0 * Overlap.generator 0 :=
      congrArg₂ (· * ·) (Overlap.element_generator 0) (Overlap.element_generator 0)
    _ = marked := (pow_two (Overlap.generator 0)).symm

theorem element_indexImage (u : Fin 128) (p q : Bool) (j : Fin 3) :
    Overlap.element (indexImage u p q j) = generatorImage (Overlap.element u) p q j := by
  simp only [indexImage, element_multiply, element_inverse, Overlap.element_generator,
    apply_ite, element_marked, Overlap.element_zero, generatorImage, centralImage]

end Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions.Coverage
