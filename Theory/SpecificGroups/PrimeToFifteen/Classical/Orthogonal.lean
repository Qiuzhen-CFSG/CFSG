module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.A02ParabolicSections.SourceGeometry.Minus
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Three-divisibility for the full orthogonal families

Cubic elements in the elementary split and odd carriers survive their scalar
quotients, whose kernels have exponent two. For minus type, the actual four-space
comparison with PSL₂ over the quadratic extension supplies a cubic element in
its commutator cover. Successively adjoining hyperbolic planes preserves it,
and the same scalar-kernel argument passes to the projective carrier.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1.1.5(3) and 15.3.34, with all orthogonal ranks in the known-simple catalogue.
-/

public noncomputable section
namespace Theory.SpecificGroups.PrimeToFifteen.Classical
open ClassicalOrthogonal ClassicalOrthogonal.Fundamental

private theorem three_dvd_of_square_kernel {A G : Type*} [Group A] [Group G]
    (f : A →* G) (hker : ∀ x, f x = 1 → x ^ 2 = 1)
    (a : A) (ha : orderOf a = 3) : 3 ∣ Nat.card G := by
  have hc : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have ho : orderOf (f a) = 3 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hc, map_one]
    · intro he
      have h2 := hker a he
      have h1 : a = 1 := by simpa only [pow_succ, h2, one_mul] using hc
      simp [h1] at ha
  simpa only [ho] using orderOf_dvd_natCard (f a)

/-- The split orthogonal scalar quotient retains an element of order three. -/
theorem orthogonalPlus_three_dvd (F : Type*) [Field F] {r : ℕ} (hr : 2 ≤ r) :
    3 ∣ Nat.card (POmegaPlus r F) := by
  obtain ⟨a, ha⟩ := SplitOddBlocks.plus_exists_cubic (F := F) hr
  exact three_dvd_of_square_kernel (projectiveElementaryMap (formD r F))
    (fun x hx => elementaryScalar_square _ x
      ((projectiveElementaryMap_eq_one_iff _ x).mp hx)) a ha

/-- Every positive-rank odd orthogonal scalar quotient has a cubic element. -/
theorem orthogonalOdd_three_dvd (F : Type*) [Field F] {r : ℕ} (hr : 1 ≤ r) :
    3 ∣ Nat.card (POmegaOdd r F) := by
  obtain ⟨a, ha⟩ := SplitOddBlocks.odd_exists_cubic (F := F) hr
  exact three_dvd_of_square_kernel (projectiveElementaryMap (formB r F))
    (fun x hx => elementaryScalar_square _ x
      ((projectiveElementaryMap_eq_one_iff _ x).mp hx)) a ha

private theorem minusCover_exists_cubic (F : Type*) [Field F] [Finite F] (k : ℕ) :
    ∃ a : Minus.Omega F (Minus.Space F (k+1))
      (Minus.form F (k+1) (Minus.parameter F)), orderOf a = 3 := by
  induction k with
  | zero =>
    obtain ⟨E, hE, hfin, _, ⟨e⟩⟩ := Minus.OddFourComparison.exists_projectiveEquivPSL F
    have h : 3 ∣ Nat.card (ClassicalGroup.POmegaMinus 2 F) := by
      rw [Nat.card_congr e.toEquiv]
      exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card E 2 le_rfl
    have hd := h.trans (Minus.scalarSubgroup F (Minus.Space F 1)
      (Minus.form F 1 (Minus.parameter F))).card_quotient_dvd_card
    exact exists_prime_orderOf_dvd_card' 3 hd
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih
    let f := A02ParabolicSections.MinusTail.tailHom (k+1) (Minus.parameter F)
    exact ⟨f a, (orderOf_injective f
      (A02ParabolicSections.MinusTail.tailHom_injective _ _) a).trans ha⟩

/-- Every admissible minus orthogonal carrier has order divisible by three. -/
theorem orthogonalMinus_three_dvd (F : Type*) [Field F] [Finite F]
    {r : ℕ} (hr : 2 ≤ r) : 3 ∣ Nat.card (ClassicalGroup.POmegaMinus r F) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r-2, by omega⟩
  obtain ⟨a, ha⟩ := minusCover_exists_cubic F k
  have hQ : ∃ v, Minus.form F (k+1) (Minus.parameter F) v ≠ 0 := by
    refine ⟨(0, (1, 0)), ?_⟩
    simp [Minus.form, Minus.plane_apply]
  exact three_dvd_of_square_kernel
    (QuotientGroup.mk' (Minus.scalarSubgroup F (Minus.Space F (k+1))
      (Minus.form F (k+1) (Minus.parameter F))))
    (fun x hx => omegaScalar_square _ hQ x ((QuotientGroup.eq_one_iff _).mp hx)) a ha

end Theory.SpecificGroups.PrimeToFifteen.Classical
