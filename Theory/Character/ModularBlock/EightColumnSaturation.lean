module

public import Theory.Character.ModularBlock.Congruence

/-!
# Rigidity of eight entries in a principal-block column

Eight distinct members of a principal block contribute at most the whole
block's column norm. If that norm is eight, two extremal signed sums force
the entries to be `1, 1, -1, -1, z, -z, z, -z`, for any unit complex number `z`.

The elementary argument expands the sum of squared distances from this vector.
The signed sums fix the inner product at eight, so the distance sum is
nonpositive. Positivity forces every distance to vanish. The block theorem
obtains the required norm bound by injecting the eight chosen characters into
the block indices; it needs no theorem constructing those characters.

Source application: Fong (1967), equation (10), with `z = I` at `F` and
`z = -I` at `F³`. The statements here retain the signed-sum hypotheses explicitly.
-/

open scoped BigOperators
noncomputable section

namespace Complex

private theorem eq_of_sum_normSq_le_of_inner_eq {ι : Type*} [Fintype ι] (a b : ι → ℂ)
    (hbound : ∑ i, normSq (a i) ≤ ∑ i, normSq (b i))
    (hinner : ∑ i, a i * (starRingEnd ℂ) (b i) = (∑ i, normSq (b i) : ℝ)) :
    ∀ i, a i = b i := by
  have hr := congrArg Complex.re hinner
  simp only [Complex.re_sum, Complex.ofReal_re] at hr
  have hd : ∑ i, normSq (a i - b i) ≤ 0 := by
    simp only [normSq_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    linarith
  have hz : ∑ i, normSq (a i - b i) = 0 :=
    le_antisymm hd (Finset.sum_nonneg fun i _ => normSq_nonneg _)
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => normSq_nonneg (a i - b i))).mp hz i (Finset.mem_univ i)
  exact sub_eq_zero.mp (normSq_eq_zero.mp hi)

/-- Two extremal signed sums determine eight complex numbers whose total
squared norm is at most eight. -/
public theorem eight_values_eq_of_signed_sums (a : Fin 8 → ℂ) (z : ℂ)
    (hz : normSq z = 1) (hbound : ∑ i, normSq (a i) ≤ 8)
    (hfirst : a 0 + a 1 - a 2 - a 3 = 4)
    (hsecond : a 4 - a 5 + a 6 - a 7 = 4 * z) :
    ∀ i, a i = (![1, 1, -1, -1, z, -z, z, -z] : Fin 8 → ℂ) i := by
  let b : Fin 8 → ℂ := ![1, 1, -1, -1, z, -z, z, -z]
  have hb : ∑ i, normSq (b i) = 8 := by
    norm_num [b, Fin.sum_univ_succ, hz]
  apply eq_of_sum_normSq_le_of_inner_eq a b
  · simpa only [hb] using hbound
  · rw [hb]
    calc
      ∑ i, a i * (starRingEnd ℂ) (b i) =
          (a 0 + a 1 - a 2 - a 3) + (a 4 - a 5 + a 6 - a 7) * (starRingEnd ℂ) z := by
        simp [b, Fin.sum_univ_succ]
        ring
      _ = (8 : ℝ) := by
        rw [hfirst, hsecond, mul_assoc, Complex.mul_conj, hz]
        norm_num

end Complex

namespace ModularBlock.PrincipalBlockConstruction.PrincipalCongruenceBlockData

/-- The saturated principal-block column and two signed sums determine all
eight values of any injective family of block members. -/
public theorem eight_values_eq_of_column_sum {G : Type*} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (χ : Fin 8 → ClassFunction G)
    (hinj : Function.Injective χ)
    (hmem : ∀ i, ∃ j ∈ d.block, ∀ x, χ i x = d.chi j (ConjClasses.mk x))
    (g : G) (z : ℂ) (hz : Complex.normSq z = 1)
    (hcol : ∑ j ∈ d.block,
      d.chi j (ConjClasses.mk g) * star (d.chi j (ConjClasses.mk g)) = 8)
    (hfirst : χ 0 g + χ 1 g - χ 2 g - χ 3 g = 4)
    (hsecond : χ 4 g - χ 5 g + χ 6 g - χ 7 g = 4 * z) :
    ∀ i, χ i g = (![1, 1, -1, -1, z, -z, z, -z] : Fin 8 → ℂ) i := by
  classical
  choose f hf hχ using hmem
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply hinj
    ext x
    rw [hχ i x, hχ j x, hij]
  have hreal := congrArg Complex.re hcol
  simp only [Complex.re_sum, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re] at hreal
  have hbound : ∑ i, Complex.normSq (χ i g) ≤ 8 := by
    calc
      ∑ i, Complex.normSq (χ i g) =
          ∑ j ∈ Finset.univ.image f, Complex.normSq (d.chi j (ConjClasses.mk g)) := by
        rw [Finset.sum_image (fun i _ j _ h => hf_inj h)]
        exact Finset.sum_congr rfl (fun i _ => congrArg Complex.normSq (hχ i g))
      _ ≤ ∑ j ∈ d.block, Complex.normSq (d.chi j (ConjClasses.mk g)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
          exact hf i
        · intro j _ _
          exact Complex.normSq_nonneg _
      _ = 8 := hreal
  exact Complex.eight_values_eq_of_signed_sums (fun i => χ i g) z hz hbound hfirst hsecond

end ModularBlock.PrincipalBlockConstruction.PrincipalCongruenceBlockData
