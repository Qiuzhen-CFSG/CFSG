module

public import Theory.Character.Orthogonality

/-!
# Saturated character columns

A family of distinct irreducible characters whose squared values sum to the
centralizer order exhausts a column. Every irreducible outside the family
vanishes there, by second orthogonality and positivity of squared norms.

Source: the second orthogonality relation for finite complex characters.
-/

open scoped BigOperators
noncomputable section

/-- A saturated partial character column forces all remaining entries to vanish. -/
public theorem irreducible_eq_zero_of_column_saturated
    {G α : Type*} [Group G] [Finite G] [Fintype α]
    (χ : α → ClassFunction G) (hirr : ∀ i, IsIrreducibleCharacter (χ i))
    (hinj : Function.Injective χ) (g : G)
    (hsat : ∑ i, Complex.normSq (χ i g) =
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℝ))
    {ψ : ClassFunction G} (hψ : IsIrreducibleCharacter ψ)
    (hne : ∀ i, ψ ≠ χ i) : ψ g = 0 := by
  classical
  obtain ⟨ι, hι, θ, hθ, hcol⟩ := second_orthogonality (G := G)
  let : Fintype ι := hι
  have hrep {φ : ClassFunction G} (hφ : IsIrreducibleCharacter φ) :
      ∃ j, ∀ x, θ j (ConjClasses.mk x) = φ x := by
    obtain ⟨n, ρ, hρ, rfl⟩ := hφ
    let := hρ
    obtain ⟨j, hj⟩ := hθ.2.1 (characterClassFunction ρ)
      ⟨⟨n, ρ, rfl⟩, (irreducible_iff_character_norm_one ρ).mp hρ⟩
    exact ⟨j, fun x => by rw [hj]; rfl⟩
  choose e he using fun i => hrep (hirr i)
  have hei : Function.Injective e := by
    intro i j hij
    apply hinj
    funext x
    rw [← he i x, ← he j x, hij]
  obtain ⟨k, hk⟩ := hrep hψ
  have hknot : k ∉ Finset.univ.image e := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i hi
    apply hne i
    funext x
    rw [← hk x, ← he i x, hi]
  let f : ι → ℝ := fun j => Complex.normSq (θ j (ConjClasses.mk g))
  have hsum : ∑ j, f j = (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℝ) := by
    have h := congrArg Complex.re ((hcol g g).1 rfl)
    have hc : Nat.card {x : G // x * g = g * x} =
        Nat.card (Subgroup.centralizer ({g} : Set G)) :=
      Nat.card_congr (Equiv.subtypeEquivRight
        (fun _ => Subgroup.mem_centralizer_singleton_iff.symm))
    simpa only [f, hc, Complex.re_sum, Complex.star_def, Complex.mul_conj,
      Complex.ofReal_re, Complex.natCast_re] using h
  have hpartial : ∑ j ∈ Finset.univ.image e, f j =
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℝ) := by
    rw [Finset.sum_image (fun i _ j _ hij => hei hij)]
    simpa [f, he] using hsat
  have hle := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (insert k (Finset.univ.image e)))
    (fun j _ _ => Complex.normSq_nonneg (θ j (ConjClasses.mk g)))
  change (∑ j ∈ insert k (Finset.univ.image e), f j) ≤ ∑ j, f j at hle
  rw [Finset.sum_insert hknot, hpartial, hsum] at hle
  have hz : Complex.normSq (ψ g) = 0 := by
    have hf : f k = Complex.normSq (ψ g) := by dsimp [f]; rw [hk]
    rw [hf] at hle
    exact le_antisymm (by linarith) (Complex.normSq_nonneg _)
  exact Complex.normSq_eq_zero.mp hz
