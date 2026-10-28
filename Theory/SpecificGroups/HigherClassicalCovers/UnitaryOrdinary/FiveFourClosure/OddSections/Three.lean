module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.Reduction
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Restriction
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourFormTransport
public import Theory.GroupTheory.PerfectCentralCoverThreeCycleNorm

/-!
# The three-primary local calculation for SU₅(4)

The actual plane Levi embeds GL₂(F₁₆) in the identity-form special unitary
group. Its two cubic diagonal factors give a subgroup of order nine.
The matrix swapping the two coordinates swaps its commuting generators,
so arbitrary lifts of those generators to a central extension commute.
If 27 does not divide the ambient order, this torus has index prime to
three. Central transfer then excludes three from a perfect covering kernel.

The trace-one basis change, Levi embedding, torus cardinality and swapping
matrix are all constructed on the literal matrix carrier. Only the ambient
three-part bound remains explicit; the final application obtains it from
the expected SU₅(4) order bound, whose proof is an independent obligation.

Source: Aschbacher--Smith I.1.4(4), printed p.408 of `refs/quasithin.pdf`,
and GLS3 Section 6.1; the plane Levi is the one in the F.1.12(7) calculation.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups PerfectCentralCovering
open Theory.SpecificGroups.UnitaryFive

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections

variable {F : Type*} [Field F]

private def diagonalTwo (C : Subgroup Fˣ) : (Fin 2 → C) →* GL (Fin 2) F where
  toFun a := ⟨diagonal (fun i => ((a i).val : F)),
    diagonal (fun i => (((a i).val)⁻¹ : Fˣ)), by
      simp only [diagonal_mul_diagonal]
      convert diagonal_one using 1
      congr 1
      funext i
      exact Units.mul_inv (a i).val, by
      simp only [diagonal_mul_diagonal]
      convert diagonal_one using 1
      congr 1
      funext i
      exact Units.inv_mul (a i).val⟩
  map_one' := by apply Units.ext; exact diagonal_one
  map_mul' a b := by apply Units.ext; exact (diagonal_mul_diagonal _ _).symm

private theorem diagonalTwo_injective (C : Subgroup Fˣ) : Function.Injective (diagonalTwo C) := by
  intro a b h
  funext i
  apply Subtype.ext
  apply Units.ext
  simpa [diagonalTwo] using congrArg (fun A : GL (Fin 2) F => A.val i i) h

private def swapTwo : GL (Fin 2) F :=
  ⟨!![0,1;1,0], !![0,1;1,0], by ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]⟩

private theorem swapTwo_diagonal (C : Subgroup Fˣ) (a : Fin 2 → C) :
    swapTwo * diagonalTwo C a * swapTwo⁻¹ = diagonalTwo C ![a 1, a 0] := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapTwo, diagonalTwo, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

private theorem pair_generates {C G : Type*} [CommGroup C] [Group G]
    (t : (Fin 2 → C) →* G) (u : C) (hu : ∀ a, a ∈ zpowers u) :
    closure ({t ![u,1], t ![1,u]} : Set G) = t.range := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    rcases hg with rfl | hg
    · exact ⟨_,rfl⟩
    · rcases hg with rfl
      exact ⟨_,rfl⟩
  · rintro g ⟨a,rfl⟩
    obtain ⟨k,hk⟩ := mem_zpowers_iff.mp (hu (a 0))
    obtain ⟨l,hl⟩ := mem_zpowers_iff.mp (hu (a 1))
    have he : a = (![u,1] : Fin 2 → C)^k * (![1,u] : Fin 2 → C)^l := by
      funext i
      fin_cases i <;> simp [hk, hl]
    rw [he, map_mul, map_zpow, map_zpow]
    exact mul_mem (zpow_mem (subset_closure (by simp)) _)
      (zpow_mem (subset_closure (by simp)) _)

private theorem kernel_exclusion_of_glTwo
    {G : Type*} [Group G] [Finite G] [Finite F]
    (j : GL (Fin 2) F →* G) (hj : Function.Injective j)
    (hF : Nat.card F = 16) (hG : ¬ 27 ∣ Nat.card G)
    {E : Type*} [Group E] [Finite E] (d : Cover E G) :
    ¬ 3 ∣ Nat.card d.toMonoidHom.ker := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C := rootsOfUnity 3 F
  have hC : Nat.card C = 3 := FiniteField.card_rootsOfUnity_of_dvd F 3 (by
    rw [hF]; norm_num)
  let t : (Fin 2 → C) →* G := j.comp (diagonalTwo C)
  have ht : Function.Injective t := hj.comp (diagonalTwo_injective C)
  have hT : Nat.card t.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective ht).toEquiv,
      Nat.card_fun, Nat.card_fin, hC]
    norm_num
  have hi : ¬ 3 ∣ t.range.index := by
    intro h
    apply hG
    have he := t.range.card_mul_index
    rw [hT] at he
    rw [← he]
    exact Nat.mul_dvd_mul_left 9 h
  obtain ⟨u,hu⟩ := IsCyclic.exists_generator (α := C)
  apply d.not_dvd_kernel_of_swapped_pair_at_prime_index t.range
    (t ![u,1]) (t ![1,u]) (j swapTwo)
    (pair_generates t u hu) ((Commute.all _ _).map t) ?_ ?_
    (by decide : Nat.Coprime 3 2) ?_ hi
  · simpa only [t, MonoidHom.comp_apply, ← map_inv, ← map_mul, Matrix.cons_val_zero, Matrix.cons_val_one] using
      congrArg j (swapTwo_diagonal C ![u,1])
  · simpa only [t, MonoidHom.comp_apply, ← map_inv, ← map_mul, Matrix.cons_val_zero, Matrix.cons_val_one] using
      congrArg j (swapTwo_diagonal C ![1,u])
  · rw [← map_pow]
    have hu3 : u^3 = 1 := by
      apply Subtype.ext
      exact (mem_rootsOfUnity 3 _).mp u.property
    have he : (![u,1] : Fin 2 → C)^3 = 1 := by
      funext i; fin_cases i <;> simp [hu3]
    rw [he, map_one]

/-- The literal plane Levi supplies the three-primary commuting-lifts calculation.
Only the independent three-part bound on the ambient SU group remains explicit. -/
theorem not_three_dvd_kernel_of_cube_not_dvd [Finite F]
    (J : HermitianForm 5 F) (hF : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x^4) (hJ : J.form = 1)
    (hG : ¬ 27 ∣ Nat.card J.specialSubgroup)
    {E : Type*} [Group E] [Finite E] (d : Cover E J.specialSubgroup) :
    ¬ 3 ∣ Nat.card d.toMonoidHom.ker := by
  let : CharP F 2 := charP_two_of_card_sixteen hF
  obtain ⟨c,hc⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective
    J 4 hF (fixed_card_four J hF hconj) 1 (map_one _)
  let j := PlaneCore.planeLeviSU J c hc hJ
  have hj : Function.Injective j := by
    intro a b h
    apply PlaneCore.planeLeviStabilizer_injective J c hc hJ
    exact Subtype.ext h
  exact kernel_exclusion_of_glTwo j hj hF hG d

/-- The ambient order bound makes the order-nine torus a Sylow subgroup,
so no prime-degree three-cover exists. -/
theorem three_primeLocalSections_of_card_dvd [Finite F]
    (J : HermitianForm 5 F) (hF : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x^4) (hJ : J.form = 1)
    (hG : Nat.card J.specialSubgroup ∣ 2^20 * 3^2 * 5^5 * 13 * 17 * 41) :
    PrimeLocalSections J 3 := by
  intro E _ _ d hd
  have hn := not_three_dvd_kernel_of_cube_not_dvd J hF hconj hJ
    (fun h => (by norm_num : ¬ 27 ∣ 2^20 * 3^2 * 5^5 * 13 * 17 * 41) (h.trans hG)) d
  exact False.elim (hn (hd ▸ dvd_rfl))

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections
