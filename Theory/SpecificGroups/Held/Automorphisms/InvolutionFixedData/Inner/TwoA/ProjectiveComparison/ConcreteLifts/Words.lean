module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.Model
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.CentralizerCertificate.Words
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic.FinCases

/-!
# The two concrete words lifting the Held projective generators

The four checked centralizer generators give two literal elements x and y.
Their relations x³ = y⁵ = (xy)⁷ = 1 are checked on the existing four-point
base of the degree-2058 action. For the longer product relation, four short
cycles keep each kernel calculation to one application of the product word.

In the abelianization, xy has order dividing both 15 and 7, hence is trivial;
x then has order dividing both 3 and 5. Thus both words belong to the actual
commutator subgroup of the centralizer. No generation or cardinality claim
is needed, and no Held simplicity hypothesis is used.

Source: the 2A row of GLS3 Table 5.3p, with the cover conventions on
pp.260–261. The candidate words and inverse GAP permutations are retained
in `TwoA/CentralizerCertificate/Source/discovery.json`. The GAP-to-Lean
conversion preserves word order; original ATLAS attribution is in
`Held/Model/Source/README.md`. Every finite assertion below is kernel checked.
-/

@[expose] public section

namespace Held.InvolutionFixedData.TwoA.ProjectiveComparison.ConcreteLifts
open CentralizerCertificate
set_option maxRecDepth 4096

/-- The selected order-three word in the literal centralizer. -/
def x : centralizer :=
  (centralizerGenerator 2 * (centralizerGenerator 1)⁻¹) ^ 2 *
  centralizerGenerator 2 ^ 2 * (centralizerGenerator 1)⁻¹ *
  (centralizerGenerator 3)⁻¹ * (centralizerGenerator 1)⁻¹ *
  centralizerGenerator 2 * centralizerGenerator 1 * ((centralizerGenerator 3) ^ 2)⁻¹

/-- The selected order-five word in the literal centralizer. -/
def y : centralizer :=
  centralizerGenerator 2 * ((centralizerGenerator 1) ^ 2)⁻¹ *
  (centralizerGenerator 2)⁻¹ * centralizerGenerator 1 *
  (centralizerGenerator 2)⁻¹ * ((centralizerGenerator 1) ^ 2)⁻¹ *
  ((centralizerGenerator 3) ^ 2)⁻¹ * (centralizerGenerator 1)⁻¹ *
  (centralizerGenerator 0)⁻¹

/-- The cube relation, checked on the four-point base. -/
theorem x_cube : x ^ 3 = 1 := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  decide +kernel

/-- The fifth-power relation, checked on the four-point base. -/
theorem y_fifth : y ^ 5 = 1 := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  decide +kernel

private theorem perm_seventh_on_cycle {T : Type*} (p : Equiv.Perm T)
    (v : Fin 7 → T) (h : ∀ j, p (v j) = v (j + 1)) : (p ^ 7) (v 0) = v 0 := by
  change p (p (p (p (p (p (p (v 0))))))) = v 0
  simp only [h]
  apply congrArg v
  decide +kernel

private def xyCycle : Fin 4 → Fin 7 → Fin 2058 :=
  ![![0, 1872, 82, 706, 566, 522, 1327], ![1, 570, 1483, 1186, 459, 838, 978], ![2, 1479, 1484, 1402, 1574, 565, 768], ![3, 134, 611, 1868, 728, 74, 1586]]

private def xyCycleSteps (i : Fin 4) : Prop := ∀ j : Fin 7,
  representation (x * y).val (xyCycle i j) = xyCycle i (j + 1)

private theorem xyCycle_step0 : xyCycleSteps 0 := by
  unfold xyCycleSteps
  decide +kernel

private theorem xyCycle_step1 : xyCycleSteps 1 := by
  unfold xyCycleSteps
  decide +kernel

private theorem xyCycle_step2 : xyCycleSteps 2 := by
  unfold xyCycleSteps
  decide +kernel

private theorem xyCycle_step3 : xyCycleSteps 3 := by
  unfold xyCycleSteps
  decide +kernel

private theorem xyCycle_step (i : Fin 4) : xyCycleSteps i := by
  fin_cases i
  · exact xyCycle_step0
  · exact xyCycle_step1
  · exact xyCycle_step2
  · exact xyCycle_step3

/-- Four checked seven-step cycles prove the product relation. -/
theorem xy_seventh : (x * y) ^ 7 = 1 := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  intro i
  have hi : xyCycle i 0 = ⟨i.val, by omega⟩ := by fin_cases i <;> rfl
  have h := perm_seventh_on_cycle (representation (x * y).val) (xyCycle i)
    (xyCycle_step i)
  rw [hi] at h
  simpa only [SubgroupClass.coe_pow, map_pow, Subgroup.coe_one, map_one,
    Equiv.Perm.one_apply] using h

private theorem triangle_abelian_trivial {A : Type*} [CommGroup A]
    (u v : A) (hu : u ^ 3 = 1) (hv : v ^ 5 = 1)
    (huv : (u * v) ^ 7 = 1) : u = 1 ∧ v = 1 := by
  have h15 : (u * v) ^ 15 = 1 := by
    rw [mul_pow]
    have hu15 : u ^ 15 = 1 := by
      rw [show 15 = 3 * 5 from rfl, pow_mul, hu, one_pow]
    have hv15 : v ^ 15 = 1 := by
      rw [show 15 = 5 * 3 from rfl, pow_mul, hv, one_pow]
    rw [hu15, hv15, one_mul]
  have hprod : u * v = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_one
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h15)
      (orderOf_dvd_of_pow_eq_one huv)
  have hu5 : u ^ 5 = 1 := by
    calc
      u ^ 5 = (u * v) ^ 5 := by rw [mul_pow, hv, mul_one]
      _ = 1 := by rw [hprod, one_pow]
  have hu1 : u = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_one
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu)
      (orderOf_dvd_of_pow_eq_one hu5)
  exact ⟨hu1, by simpa only [hu1, one_mul] using hprod⟩

/-- The coprime triangle relations put both words in the literal derived subgroup. -/
theorem words_mem_derived : x ∈ derived ∧ y ∈ derived := by
  change x ∈ commutator centralizer ∧ y ∈ commutator centralizer
  rw [← Abelianization.ker_of centralizer]
  exact triangle_abelian_trivial (Abelianization.of x) (Abelianization.of y)
    (by simpa using congrArg Abelianization.of x_cube)
    (by simpa using congrArg Abelianization.of y_fifth)
    (by simpa using congrArg Abelianization.of xy_seventh)

end Held.InvolutionFixedData.TwoA.ProjectiveComparison.ConcreteLifts
