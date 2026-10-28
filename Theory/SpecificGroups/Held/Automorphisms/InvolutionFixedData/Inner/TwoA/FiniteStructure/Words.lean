module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.CentralizerCertificate.Words
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.ProjectiveComparison.Coordinates
import Mathlib.Tactic.FinCases

/-!
# Checked words for the perfect Held 2A subgroup

The two retained centralizer words satisfy the (3,5,7) relations and act
on the 21 labelled points as the two projective comparison matrices.
Two words in them give the distinguished involution and a second involution
q. The latter is written as a short ambient conjugate for the commutation
checks. Seven-step action traces avoid deeply nested kernel reductions.

Every equality is checked in the original degree-2058 action, using its
proved four-point base. Candidate discovery is not a proof input.
Source: GLS3 Table 5.3p, printed p.277; the unchanged ATLAS data and
word provenance in `../CentralizerCertificate/Source/README.md`.
-/

@[expose] public section
namespace Held.InvolutionFixedData.TwoA.FiniteStructure
open CentralizerCertificate ProjectiveComparison
set_option maxRecDepth 4096

local notation "c" => centralizerGenerator

/-- First retained derived word, viewed initially in the fixed subgroup. -/
def x : centralizer := c 2 * c 1 ^ (-1 : ℤ) * c 2 * c 1 ^ (-1 : ℤ) * c 2 ^ (2 : ℤ) * c 1 ^ (-1 : ℤ) * c 3 ^ (-1 : ℤ) * c 1 ^ (-1 : ℤ) * c 2 * c 1 * c 3 ^ (-2 : ℤ)

/-- Second retained derived word, viewed initially in the fixed subgroup. -/
def y : centralizer := c 2 * c 1 ^ (-2 : ℤ) * c 2 ^ (-1 : ℤ) * c 1 * c 2 ^ (-1 : ℤ) * c 1 ^ (-2 : ℤ) * c 3 ^ (-2 : ℤ) * c 1 ^ (-1 : ℤ) * c 0 ^ (-1 : ℤ)

/-- Conjugating word for the second central involution. -/
def conjugator : He := b * b * a * b * b * a * b * b * a * b⁻¹ * b⁻¹ * a * b * a * b * b * a * b

/-- An ambient conjugate of the distinguished involution. -/
def q : He := conjugator * a * conjugator⁻¹

private theorem q_commute_a : q * a = a * q := by
  apply Held.eq_of_four_point_images
  decide +kernel

theorem q_mem : q ∈ centralizer := by
  rw [centralizer_eq, Subgroup.mem_centralizer_singleton_iff]
  exact q_commute_a

def qC : centralizer := ⟨q, q_mem⟩

private theorem pow_smul_trace {G X : Type*} [Group G] [MulAction G X]
    (g : G) (t : ℕ → X) (n : ℕ) (hs : ∀ i < n, g • t i = t (i + 1)) :
    g ^ n • t 0 = t n := by
  have h : ∀ k ≤ n, g ^ k • t 0 = t k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_smul, ih (by omega), hs k (by omega)]
  exact h n le_rfl

theorem x_cube : x ^ 3 = 1 := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  intro i
  fin_cases i <;> decide +kernel

theorem y_fifth : y ^ 5 = 1 := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  intro i
  fin_cases i <;> decide +kernel

private def xyTrace (i : Fin 4) (j : ℕ) : Fin 2058 :=
  ![![0, 1872, 82, 706, 566, 522, 1327, 0], ![1, 570, 1483, 1186, 459, 838, 978, 1], ![2, 1479, 1484, 1402, 1574, 565, 768, 2], ![3, 134, 611, 1868, 728, 74, 1586, 3]] i ⟨j % 8, Nat.mod_lt _ (by decide)⟩

private theorem xyStep0 : ∀ j : Fin 7,
    (x * y) • xyTrace 0 j.val = xyTrace 0 (j.val + 1) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem xyStep1 : ∀ j : Fin 7,
    (x * y) • xyTrace 1 j.val = xyTrace 1 (j.val + 1) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem xyStep2 : ∀ j : Fin 7,
    (x * y) • xyTrace 2 j.val = xyTrace 2 (j.val + 1) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem xyStep3 : ∀ j : Fin 7,
    (x * y) • xyTrace 3 j.val = xyTrace 3 (j.val + 1) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem xyStep (i : Fin 4) (j : ℕ) (hj : j < 7) :
    (x * y) • xyTrace i j = xyTrace i (j + 1) := by
  have h : ∀ i : Fin 4, ∀ j : Fin 7,
      (x * y) • xyTrace i j.val = xyTrace i (j.val + 1) :=
    Fin.cases xyStep0 (Fin.cases xyStep1
      (Fin.cases xyStep2 (Fin.cases xyStep3 (fun i => Fin.elim0 i))))
  exact h i ⟨j, hj⟩

theorem xy_seventh : (x * y) ^ 7 = 1 := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  intro i
  have h := pow_smul_trace (x * y) (xyTrace i) 7 (xyStep i)
  have hstart : xyTrace i 0 = (⟨i.val, by omega⟩ : Fin 2058) := by
    fin_cases i <;> decide +kernel
  rw [hstart] at h
  exact h.trans (by fin_cases i <;> decide +kernel)

private def xy2Trace (i : Fin 4) (j : ℕ) : Fin 2058 :=
  ![![0, 1718, 1795, 1221, 1396, 1583, 115, 1332], ![1, 1313, 506, 962, 1888, 463, 1254, 812], ![2, 1539, 98, 1121, 952, 679, 806, 1149], ![3, 1773, 1228, 1026, 1518, 1470, 598, 2026]] i ⟨j % 8, Nat.mod_lt _ (by decide)⟩

private theorem xy2Step0 : ∀ j : Fin 7,
    (x * y ^ 2) • xy2Trace 0 j.val = xy2Trace 0 (j.val + 1) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem xy2Step1 : ∀ j : Fin 7,
    (x * y ^ 2) • xy2Trace 1 j.val = xy2Trace 1 (j.val + 1) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem xy2Step2 : ∀ j : Fin 7,
    (x * y ^ 2) • xy2Trace 2 j.val = xy2Trace 2 (j.val + 1) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem xy2Step3 : ∀ j : Fin 7,
    (x * y ^ 2) • xy2Trace 3 j.val = xy2Trace 3 (j.val + 1) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem xy2Step (i : Fin 4) (j : ℕ) (hj : j < 7) :
    (x * y ^ 2) • xy2Trace i j = xy2Trace i (j + 1) := by
  have h : ∀ i : Fin 4, ∀ j : Fin 7,
      (x * y ^ 2) • xy2Trace i j.val = xy2Trace i (j.val + 1) :=
    Fin.cases xy2Step0 (Fin.cases xy2Step1
      (Fin.cases xy2Step2 (Fin.cases xy2Step3 (fun i => Fin.elim0 i))))
  exact h i ⟨j, hj⟩

theorem second_central_word : (x * y ^ 2) ^ 7 = qC := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  intro i
  have h := pow_smul_trace (x * y ^ 2) (xy2Trace i) 7 (xy2Step i)
  have hstart : xy2Trace i 0 = (⟨i.val, by omega⟩ : Fin 2058) := by
    fin_cases i <;> decide +kernel
  rw [hstart] at h
  exact h.trans (by fin_cases i <;> decide +kernel)

theorem first_central_word : (x * y⁻¹) ^ 3 = centralizerGenerator 0 := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  intro i
  fin_cases i <;> decide +kernel

theorem qC_commute_x : qC * x = x * qC := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  intro i
  fin_cases i <;> decide +kernel

theorem qC_commute_y : qC * y = y * qC := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  intro i
  fin_cases i <;> decide +kernel

theorem qC_not_commute : centralizerGenerator 1 * qC ≠ qC * centralizerGenerator 1 := by
  intro h
  have h0 := congrArg (fun g : centralizer => representation g.val 0) h
  have hn : representation (centralizerGenerator 1 * qC).val 0 ≠
      representation (qC * centralizerGenerator 1).val 0 := by decide +kernel
  exact hn h0

theorem q_fixed : representation q 25 = 25 := by decide +kernel

theorem four_distinct : Function.Injective
    (fun i : Fin 4 => representation ((![1, centralizerGenerator 0, qC,
      centralizerGenerator 0 * qC] : Fin 4 → centralizer) i).val 0) := by
  decide +kernel

theorem x_labels : ∀ i : Fin 21,
    representation x.val (pointLabel i) = pointLabel (permA i) := by
  intro i
  fin_cases i <;> decide +kernel

theorem y_labels : ∀ i : Fin 21,
    representation y.val (pointLabel i) = pointLabel (permB i) := by
  intro i
  fin_cases i <;> decide +kernel

end Held.InvolutionFixedData.TwoA.FiniteStructure
