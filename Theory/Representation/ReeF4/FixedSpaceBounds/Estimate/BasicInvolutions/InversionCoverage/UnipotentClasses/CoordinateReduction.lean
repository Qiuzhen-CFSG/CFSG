module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.Branches
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.WordCalculations
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.ElementaryTail
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter

/-!
# Concrete reductions for positive Ree involutions

The central case is the actual long-root curve. The existing square
calculation in D₂ removes both middle main parameters and leaves the five
literal curves x₆ x₄ y₅ y₇ y₃. We give this word in the actual fixed model,
prove its parameterization is injective and its square is one, and identify
precisely its central subfamily. Thus the D₂ involution branch reduces to
conjugacy on five independent field parameters, with no square premise left.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.8,
internal p.57; GLS3 Table 2.4, 2.4.5(d), and Lemma 3.3.9 for the coordinate
and square calculations. This module does not assert involution exhaustion.
-/

@[expose] public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses
open Parabolics EvenInvolutionGeometry ElementaryTwoBound
open ElementaryTwoBound.RootCalculations NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.RadicalCoordinates.FixedCoordinates

/-- The five free coordinates of x₆ x₄ y₅ y₇ y₃, in the established layout. -/
def tailParameters (m : ℕ) (v : Fin 5 → CoefficientField m) : PositiveParameters m :=
  ⟨![0, 0, v 0, v 1], 0, ![0, v 2, v 3, v 4]⟩

/-- The actual fixed-group element specified by those five parameters. -/
def tailElement (m : ℕ) (v : Fin 5 → CoefficientField m) : Model m :=
  wordElement m (tailParameters m v)

theorem tailElement_eq_product (m : ℕ) (v : Fin 5 → CoefficientField m) :
    tailElement m v = mainElement m 5 (v 0) * mainElement m 3 (v 1) *
      centralElement m 4 (v 2) * centralElement m 6 (v 3) *
      centralElement m 2 (v 4) := by
  simp [tailElement, tailParameters, wordElement, positive_pair_indices,
    positive_quartet_indices, pairCount, quartetCount, List.ofFn_succ, mul_assoc]

theorem tailElement_injective (m : ℕ) : Function.Injective (tailElement m) := by
  intro v w h
  have hp := wordElement_injective m h
  funext i
  fin_cases i
  · exact congrArg (fun p : PositiveParameters m => p.pair 2) hp
  · exact congrArg (fun p : PositiveParameters m => p.pair 3) hp
  · exact congrArg (fun p : PositiveParameters m => p.central 1) hp
  · exact congrArg (fun p : PositiveParameters m => p.central 2) hp
  · exact congrArg (fun p : PositiveParameters m => p.central 3) hp

@[simp] theorem tailElement_zero (m : ℕ) : tailElement m 0 = 1 := by
  simp [tailElement_eq_product]

@[simp] theorem tailElement_eq_one_iff (m : ℕ) (v : Fin 5 → CoefficientField m) :
    tailElement m v = 1 ↔ v = 0 := by
  rw [← tailElement_zero m, (tailElement_injective m).eq_iff]

theorem tailElement_mem_unipotent (m : ℕ) (v : Fin 5 → CoefficientField m) :
    tailElement m v ∈ unipotent m := by
  rw [tailElement_eq_product]
  exact (unipotent m).mul_mem ((unipotent m).mul_mem ((unipotent m).mul_mem
    ((unipotent m).mul_mem (mainElement_mem_unipotent m 5 _)
      (mainElement_mem_unipotent m 3 _)) (Y_le_unipotent m 4 (centralElement_mem_Y m 4 _)))
    (Y_le_unipotent m 6 (centralElement_mem_Y m 6 _)))
    (Y_le_unipotent m 2 (centralElement_mem_Y m 2 _))

theorem tailElement_sq (m : ℕ) (v : Fin 5 → CoefficientField m) :
    tailElement m v ^ 2 = 1 := by
  apply toSplitGroup_injective m
  simp only [map_pow, map_one, tailElement, wordElement_coe]
  apply positiveWord_sq_of_coordinate_vanishing
  · intro j hj
    change Fin 4 at j
    rw [positive_pair_indices] at hj
    fin_cases j <;> norm_num [tailParameters] at hj ⊢ <;> omega
  · intro j
    rfl
  · intro j hj
    change Fin 4 at j
    rw [positive_quartet_indices] at hj
    fin_cases j <;> norm_num [tailParameters] at hj ⊢ <;> omega

/-- The square calculation in D₂ gives this explicit five-parameter word. -/
theorem wordElement_eq_tail_of_D₂Support_sq (m : ℕ) (p : PositiveParameters m)
    (hp : D₂Support p) (hsq : wordElement m p ^ 2 = 1) :
    wordElement m p = tailElement m ![p.pair 2, p.pair 3,
      p.central 1, p.central 2, p.central 3] := by
  obtain ⟨⟨⟨hp0, hm0, hm2⟩, hp1, hc0⟩, hm1, hm3⟩ :=
    square_right_support m p hp hsq
  have he : p = tailParameters m ![p.pair 2, p.pair 3,
      p.central 1, p.central 2, p.central 3] := by
    cases p with
    | mk pair main central =>
      congr 1 <;> funext j <;> fin_cases j <;>
        simp_all
  exact congrArg (wordElement m) he

/-- A conjugacy calculation on the five-parameter tail supplies the entire
D₂-supported involution branch. Its square premise is discharged by the
proved coordinate calculation, not included in the tail input. -/
theorem root_classes_of_D₂Support_of_tail (m : ℕ)
    (htail : ∀ v : Fin 5 → CoefficientField m, v ≠ 0 →
      IsLongRootInvolution (tailElement m v) ∨ IsShortRootInvolution (tailElement m v))
    (p : PositiveParameters m) (hp : D₂Support p)
    (hne : wordElement m p ≠ 1) (hsq : wordElement m p ^ 2 = 1) :
    IsLongRootInvolution (wordElement m p) ∨ IsShortRootInvolution (wordElement m p) := by
  have he := wordElement_eq_tail_of_D₂Support_sq m p hp hsq
  rw [he] at hne ⊢
  exact htail _ (fun hz => hne (by rw [hz, tailElement_zero]))

/-- The central branch of the requested coverage, without a square premise. -/
theorem isLongRootInvolution_of_central (m : ℕ) (hm : 1 ≤ m)
    (x : Model m) (hx : x ∈ unipotent m) (hne : x ≠ 1)
    (hc : ∀ u ∈ unipotent m, Commute x u) : IsLongRootInvolution x := by
  obtain ⟨a, rfl⟩ := eq_longRootElement_of_central_unipotent m hm x hx hc
  refine ⟨a, ?_, IsConj.refl _⟩
  intro ha
  exact hne (by simp [ha])

theorem tailElement_longRoot (m : ℕ) (a : CoefficientField m) :
    tailElement m ![0, 0, a, 0, 0] = longRootElement m a := by
  rw [tailElement_eq_product]
  simp only [Matrix.cons_val_zero, Matrix.cons_val, mainElement_zero,
    centralElement_zero, one_mul, mul_one]
  apply toSplitGroup_injective m
  rw [centralElement_coe, longRootElement_coe]

/-- Exactly the y₅ axis of the five-parameter word centralizes the whole U. -/
theorem tailElement_central_iff (m : ℕ) (hm : 1 ≤ m)
    (v : Fin 5 → CoefficientField m) :
    (∀ u ∈ unipotent m, Commute (tailElement m v) u) ↔
      v 0 = 0 ∧ v 1 = 0 ∧ v 3 = 0 ∧ v 4 = 0 := by
  constructor
  · intro hc
    obtain ⟨a, ha⟩ := eq_longRootElement_of_central_unipotent m hm
      (tailElement m v) (tailElement_mem_unipotent m v) hc
    rw [← tailElement_longRoot] at ha
    have hv := tailElement_injective m ha
    exact ⟨congrFun hv 0, congrFun hv 1, congrFun hv 3, congrFun hv 4⟩
  · rintro ⟨h0, h1, h3, h4⟩
    have hv : v = ![0, 0, v 2, 0, 0] := by
      funext i
      fin_cases i <;> simp_all
    rw [hv, tailElement_longRoot]
    exact longRootElement_commute_unipotent m (v 2)

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses
