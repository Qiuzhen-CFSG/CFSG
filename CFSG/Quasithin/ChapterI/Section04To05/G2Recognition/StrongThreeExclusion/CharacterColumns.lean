module

public import Theory.Character.ColumnBound
public import Theory.Character.IrreducibleDegrees
public import Theory.Character.Generalized

/-!
# Column orthogonality for the five constructed ambient characters

Keep the principal row and the five pairwise distinct nonprincipal rows in
the ordinary column sum. Their squared norms are bounded by the actual
centralizer order, without a block-exhaustion assumption.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion

private theorem family_column_bound
    {G I : Type*} [Group G] [Finite G] [Fintype I]
    (χ : I → ClassFunction G) (hχ : ∀ i, IsIrreducibleCharacter (χ i))
    (hinj : Function.Injective χ) (g : G) :
    ∑ i, Complex.normSq (χ i g) ≤
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℝ) := by
  classical
  obtain ⟨J,hJ,θ,hθ,hcol⟩ := second_orthogonality (G := G)
  let : Fintype J := hJ
  have hmem (i : I) : ∃ j : J, ofConjClassFunction (θ j) = χ i := by
    obtain ⟨n,ρ,hρ,he⟩ := hχ i
    obtain ⟨j,hj⟩ := hθ.2.1 (characterClassFunction ρ)
      ⟨⟨n,ρ,rfl⟩,(irreducible_iff_character_norm_one ρ).mp hρ⟩
    exact ⟨j, by rw [hj, ofConjClassFunction_characterClassFunction, he]⟩
  choose f hf using hmem
  have hfi : Function.Injective f := by
    intro i k hik
    apply hinj
    rw [←hf i, ←hf k, hik]
  have hsum := (hcol g g).1 rfl
  have hcard : Nat.card {x : G // x * g = g * x} =
      Nat.card (Subgroup.centralizer ({g} : Set G)) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun _ => Subgroup.mem_centralizer_singleton_iff.symm
  rw [hcard] at hsum
  have hreal := congrArg Complex.re hsum
  simp only [Complex.re_sum, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re, Complex.natCast_re] at hreal
  calc
    ∑ i, Complex.normSq (χ i g) = ∑ j ∈ Finset.univ.image f,
        Complex.normSq (θ j (ConjClasses.mk g)) := by
      rw [Finset.sum_image (fun i _ k _ h => hfi h)]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg Complex.normSq (congrFun (hf i) g).symm
    _ ≤ ∑ j, Complex.normSq (θ j (ConjClasses.mk g)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => Complex.normSq_nonneg _)
    _ = _ := hreal

/-- Column orthogonality for the five nonprincipal rows produced by the
original special-support argument, with the principal contribution retained. -/
theorem five_nonprincipal_column_bound
    {G : Type*} [Group G] [Finite G]
    (ψ : ClassFunction G) (μ : Fin 4 → ClassFunction G)
    (hψ : IsIrreducibleCharacter ψ) (hμ : ∀ i, IsIrreducibleCharacter (μ i))
    (hi : Function.Injective μ) (hd : ∀ i, ψ ≠ μ i)
    (hψ1 : ψ ≠ 1) (hμ1 : ∀ i, μ i ≠ 1) (g : G) :
    1 + Complex.normSq (ψ g) + ∑ i, Complex.normSq (μ i g) ≤
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℝ) := by
  classical
  let χ : Option (Option (Fin 4)) → ClassFunction G :=
    fun i => match i with
    | none => 1
    | some none => ψ
    | some (some j) => μ j
  have hχ : ∀ i, IsIrreducibleCharacter (χ i) := by
    intro i
    rcases i with _ | i
    · exact isIrreducibleCharacter_one
    rcases i with _ | i
    · exact hψ
    · exact hμ i
  have hχi : Function.Injective χ := by
    intro i k hik
    cases i <;> cases k
    · rfl
    · rename_i k
      cases k with
      | none => exact (hψ1 hik.symm).elim
      | some k => exact (hμ1 k hik.symm).elim
    · rename_i i
      cases i with
      | none => exact (hψ1 hik).elim
      | some i => exact (hμ1 i hik).elim
    · rename_i i k
      cases i <;> cases k
      · rfl
      · rename_i k; exact (hd k hik).elim
      · rename_i i; exact (hd i hik.symm).elim
      · rename_i i k
        exact congrArg (fun j => some (some j)) (hi hik)
  have hh := family_column_bound χ hχ hχi g
  simpa only [Fintype.sum_option, χ, Pi.one_apply, Complex.normSq_one, add_assoc] using hh

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion
