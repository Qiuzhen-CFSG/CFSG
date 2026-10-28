module
public import Theory.Character.Orthogonality

/-!
# The column bound for an irreducible character

Second orthogonality expresses the centralizer order as a sum of nonnegative
squared absolute character values. Keeping a single summand bounds that value.
This is the usual column orthogonality estimate for finite complex characters.
-/

open scoped BigOperators
noncomputable section

/-- A squared irreducible character value is at most the centralizer order. -/
public theorem IsIrreducibleCharacter.normSq_le_centralizer_card
    {G : Type*} [Group G] [Finite G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (g : G) :
    Complex.normSq (χ g) ≤ (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℝ) := by
  classical
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  let : Representation.IsIrreducible ρ := hρ
  obtain ⟨ι, hι, θ, hθ, hcol⟩ := second_orthogonality (G := G)
  let : Fintype ι := hι
  have hirr : IsIrreducibleConjCharacter (characterClassFunction ρ) :=
    ⟨⟨n, ρ, rfl⟩, (irreducible_iff_character_norm_one (ρ := ρ)).mp hρ⟩
  obtain ⟨i, hi⟩ := hθ.2.1 _ hirr
  have hsum := (hcol g g).1 rfl
  have he : Nat.card {x : G // x * g = g * x} =
      Nat.card (Subgroup.centralizer ({g} : Set G)) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun _ => Subgroup.mem_centralizer_singleton_iff.symm)
  rw [he] at hsum
  have hreal := congrArg Complex.re hsum
  simp only [Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.natCast_re] at hreal
  have hle := Finset.single_le_sum (f := fun j => Complex.normSq (θ j (ConjClasses.mk g)))
    (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [hreal, hi] at hle
  exact hle
