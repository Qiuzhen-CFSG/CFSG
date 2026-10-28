module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.SourceB42
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.OrderFour
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral

/-!
# Excluding the strict-ratio models for characteristic-two PSL₂

Each concrete component left by the B.4.2 strict-ratio sieve has an element
of order four. In SL₃, SL₄ and SL₅, two successive transvections have a
nonidentity transvection as their square. In Sp₄, a four-cycle matrix
preserves the defining form in characteristic two. In A₆, the even
permutation (0123)(45) has order four. Actual multiplicative equivalences
transport these elements to the proposed component.

The characteristic-two PSL₂ obstruction therefore excludes all five
models, uniformly in the field exponent, including even exponents.
This completes the model comparison; the reduction of a strong action
to the hypotheses of B.4.2 remains the responsibility of its caller.

Source: Aschbacher–Smith, B.4.2, printed pp.86–87, used in the proof of
13.8.16(1), printed p.952.
-/

open Matrix
open scoped MatrixGroups CharTwo

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong

private theorem sl_has_order_four {F I : Type*} [Field F] [CharP F 2]
    [Fintype I] [DecidableEq I]
    (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ g : SpecialLinearGroup I F, orderOf g = 4 := by
  let g := SpecialLinearGroup.transvection hij (1 : F) *
    SpecialLinearGroup.transvection hjk (1 : F)
  have hsq : g ^ 2 = SpecialLinearGroup.transvection hik (1 : F) := by
    apply Subtype.ext
    simp [g, pow_two, SpecialLinearGroup.transvection_coe, mul_add, add_mul,
      Ne.symm hij, Ne.symm hik, Ne.symm hjk]
    ext a b
    simp only [Matrix.add_apply]
    abel_nf
    simp
  have hne : g ^ 2 ≠ 1 := by
    rw [hsq]
    intro h
    have hh := congrArg (fun x : SpecialLinearGroup I F => x i k) h
    simp [SpecialLinearGroup.transvection_coe, hik] at hh
  have hfour : g ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by decide, pow_mul, hsq, pow_two,
      ← SpecialLinearGroup.transvection_add]
    rw [CharTwo.add_self_eq_zero, SpecialLinearGroup.transvection_coeff_zero]
  exact ⟨g, @orderOf_eq_prime_pow _ _ g 1 2 ⟨Nat.prime_two⟩ hne hfour⟩

private theorem alternatingSix_has_order_four :
    ∃ g : alternatingGroup (Fin 6), orderOf g = 4 := by
  refine ⟨AlternatingSix.ShadowLocal.dihedralRotation, ?_⟩
  apply @orderOf_eq_prime_pow _ _ _ 1 2 ⟨Nat.prime_two⟩
  · decide +kernel
  · decide +kernel

private def cycleMatrix (F : Type*) [Field F] :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![0, 1; 0, 0] !![0, 0; 1, 0]
    !![0, 0; 1, 0] !![0, 1; 0, 0]

private theorem cycle_mem (F : Type*) [Field F] [CharP F 2] :
    cycleMatrix F ∈ symplecticGroup (Fin 2) F := by
  rw [SymplecticGroup.mem_iff]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [cycleMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.J, Matrix.fromBlocks, Matrix.one_apply]

private theorem cycle_sq (F : Type*) [Field F] [CharP F 2] :
    cycleMatrix F ^ 2 = Matrix.J (Fin 2) F := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [cycleMatrix, pow_two, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.J, Matrix.fromBlocks]

private theorem symplecticFour_has_order_four (F : Type*) [Field F] [CharP F 2] :
    ∃ g : symplecticGroup (Fin 2) F, orderOf g = 4 := by
  let g : symplecticGroup (Fin 2) F := ⟨cycleMatrix F, cycle_mem F⟩
  have hsq : (g ^ 2).val = Matrix.J (Fin 2) F := cycle_sq F
  have hne : g ^ 2 ≠ 1 := by
    intro h
    have hh := congrArg (fun x : symplecticGroup (Fin 2) F => x.val (.inl 0) (.inr 0)) h
    change (g ^ 2).val (.inl 0) (.inr 0) = 0 at hh
    rw [hsq] at hh
    simp [Matrix.J, Matrix.fromBlocks] at hh
  have hfour : g ^ 4 = 1 := by
    apply Subtype.ext
    change cycleMatrix F ^ 4 = 1
    rw [show 4 = 2 * 2 by decide, pow_mul, cycle_sq, pow_two, Matrix.J_squared]
    ext i j
    simp
  exact ⟨g, @orderOf_eq_prime_pow _ _ g 1 2 ⟨Nat.prime_two⟩ hne hfour⟩

/-- Every actual group in the strict-ratio list contains an element of order four. -/
public theorem StrictRatioModel.exists_order_four {L : Type*} [Group L]
    (h : StrictRatioModel L) : ∃ g : L, orderOf g = 4 := by
  unfold StrictRatioModel at h
  rcases h with ⟨B, ⟨e⟩⟩ | ⟨B, _, ⟨e⟩⟩ | he | he | he
  · obtain ⟨g, hg⟩ := sl_has_order_four (F := B.Carrier)
      (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    exact ⟨e.symm g, (e.symm.orderOf_eq g).trans hg⟩
  · obtain ⟨g, hg⟩ := symplecticFour_has_order_four B.Carrier
    exact ⟨e.symm g, (e.symm.orderOf_eq g).trans hg⟩
  · obtain ⟨e⟩ := he
    obtain ⟨g, hg⟩ := alternatingSix_has_order_four
    exact ⟨e.symm g, (e.symm.orderOf_eq g).trans hg⟩
  · obtain ⟨e⟩ := he
    obtain ⟨g, hg⟩ := sl_has_order_four (F := ZMod 2)
      (0 : Fin 4) 1 2 (by decide) (by decide) (by decide)
    exact ⟨e.symm g, (e.symm.orderOf_eq g).trans hg⟩
  · obtain ⟨e⟩ := he
    obtain ⟨g, hg⟩ := sl_has_order_four (F := ZMod 2)
      (0 : Fin 5) 1 2 (by decide) (by decide) (by decide)
    exact ⟨e.symm g, (e.symm.orderOf_eq g).trans hg⟩

/-- No strict-ratio B.4.2 component is PSL₂ over a finite characteristic-two field. -/
public theorem not_strictRatioModel_psl {F : Type*} [Field F] [Finite F] [CharP F 2] :
    ¬ StrictRatioModel PSL(2,F) := by
  intro h
  obtain ⟨g, hg⟩ := h.exists_order_four
  exact psl_order_ne_four g hg

/-- The comparison applies to every two-power field size, without an odd-exponent restriction. -/
public theorem not_strictRatioModel_psl_of_card {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) : ¬ StrictRatioModel PSL(2,F) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact not_strictRatioModel_psl

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
