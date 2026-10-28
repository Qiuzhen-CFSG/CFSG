module

public import Theory.Character.ModularBlock.SectionOrthogonality

/-!
# Principal-block section kernels

The principal-block character kernel based at a two-element is supported on
its two-section. Its average is one, so a function constant on that section
pairs with the kernel to that constant. Ordinary character orthogonality
computes the Gram matrix of these kernels and detects their constituents.

Source: Brauer, *Some applications of the theory of blocks of characters II*
(1964), §IV, Proposition 4, together with ordinary character orthogonality.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace ModularBlock.SectionKernel
open PrincipalBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- The principal-block kernel, viewed as a function of the second element. -/
@[expose] def kernel (d : PrincipalCongruenceBlockData G) (u : G) : ClassFunction G :=
  fun g => ∑ i ∈ d.block, star (d.chi i (ConjClasses.mk u)) *
    d.chi i (ConjClasses.mk g)

omit [Group G] in
private theorem scalar_sum_left {I : Type*} (s : Finset I)
    (f : I → ClassFunction G) (h : ClassFunction G) :
    scalarProduct G (fun g => ∑ i ∈ s, f i g) h =
      ∑ i ∈ s, scalarProduct G (f i) h := by
  classical
  simp only [scalarProduct, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

omit [Group G] in
private theorem scalar_sum_right {I : Type*} (s : Finset I)
    (f : I → ClassFunction G) (h : ClassFunction G) :
    scalarProduct G h (fun g => ∑ i ∈ s, f i g) =
      ∑ i ∈ s, scalarProduct G h (f i) := by
  rw [← scalarProduct_conj, scalar_sum_left, star_sum]
  simp only [scalarProduct_conj]

/-- The coefficient of each ordinary row in a principal-block kernel. -/
theorem kernel_scalar_row (d : PrincipalCongruenceBlockData G) (u : G) (j : d.I) :
    scalarProduct G (kernel d u) (fun g => d.chi j (ConjClasses.mk g)) =
      if j ∈ d.block then star (d.chi j (ConjClasses.mk u)) else 0 := by
  classical
  unfold kernel
  rw [scalar_sum_left]
  simp_rw [show ∀ i, (fun g => star (d.chi i (ConjClasses.mk u)) *
      d.chi i (ConjClasses.mk g)) =
      star (d.chi i (ConjClasses.mk u)) • ofConjClassFunction (d.chi i) from fun _ => rfl,
    scalarProduct_smul_left]
  change (∑ i ∈ d.block, star (d.chi i (ConjClasses.mk u)) *
    classFunctionInner (d.chi i) (d.chi j)) = _
  simp_rw [completeFamily_orthonormal d.complete]
  simp

/-- The Gram product of two kernels is the corresponding block column product. -/
theorem kernel_scalar_kernel (d : PrincipalCongruenceBlockData G) (u v : G) :
    scalarProduct G (kernel d u) (kernel d v) =
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk v) *
        star (d.chi i (ConjClasses.mk u)) := by
  classical
  conv_lhs => arg 3; unfold kernel
  rw [scalar_sum_right]
  apply Finset.sum_congr rfl
  intro i hi
  change scalarProduct G (kernel d u)
    (star (d.chi i (ConjClasses.mk v)) • ofConjClassFunction (d.chi i)) = _
  rw [scalarProduct_smul_right, star_star]
  change scalarProduct G (kernel d u) (fun g => d.chi i (ConjClasses.mk g)) * _ = _
  rw [kernel_scalar_row, if_pos hi]
  ring

/-- Every kernel has average one because the principal row belongs to the block. -/
theorem one_scalar_kernel (d : PrincipalCongruenceBlockData G) (u : G) :
    scalarProduct G 1 (kernel d u) = 1 := by
  have h := kernel_scalar_row d u d.principal
  simp only [d.principal_mem, if_true, d.principal_eq,
    ordinaryPrincipalCharacter_apply, star_one] at h
  change scalarProduct G (kernel d u) 1 = 1 at h
  rw [← scalarProduct_conj, h, star_one]

/-- Outside its two-section, the principal-block kernel vanishes. -/
theorem kernel_eq_zero (d : PrincipalCongruenceBlockData G) (u : G)
    (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1) (g : G)
    (hg : ¬ ∃ v : G, Odd (orderOf v) ∧ Commute u v ∧ IsConj (u * v) g) :
    kernel d u g = 0 := by
  have h := congrArg star
    (SectionOrthogonality.principalBlock_column_eq_zero_of_not_mem_twoSection d u hu g hg)
  simpa only [star_sum, star_mul, star_star, star_zero, kernel, mul_comm] using h

/-- A function constant on a two-section pairs with its kernel to that constant. -/
theorem scalar_kernel_of_constant (d : PrincipalCongruenceBlockData G) (u : G)
    (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1) (f : ClassFunction G) (c : ℂ)
    (hc : ∀ g, (∃ v : G, Odd (orderOf v) ∧ Commute u v ∧ IsConj (u * v) g) →
      f g = c) : scalarProduct G f (kernel d u) = c := by
  have he : scalarProduct G f (kernel d u) = scalarProduct G (c • 1) (kernel d u) := by
    unfold scalarProduct
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    by_cases hg : ∃ v : G, Odd (orderOf v) ∧ Commute u v ∧ IsConj (u * v) g
    · simp [hc g hg]
    · simp [kernel_eq_zero d u hu g hg]
  rw [he, scalarProduct_smul_left, one_scalar_kernel, mul_one]

/-- Equality in the two-column norm bound identifies the whole function. -/
theorem eq_two_kernels_of_norm (d : PrincipalCongruenceBlockData G)
    (u v : G) (a b : ℂ) (f : ClassFunction G)
    (hu : scalarProduct G (kernel d u) (kernel d u) = 8)
    (hv : scalarProduct G (kernel d v) (kernel d v) = 8)
    (huv : scalarProduct G (kernel d u) (kernel d v) = 0)
    (hfu : scalarProduct G f (kernel d u) = 8 * a)
    (hfv : scalarProduct G f (kernel d v) = 8 * b)
    (hf : scalarProduct G f f = 8 * (a * star a + b * star b)) :
    f = a • kernel d u + b • kernel d v := by
  have huf : scalarProduct G (kernel d u) f = star (8 * a) :=
    (scalarProduct_conj _ _).symm.trans (congrArg star hfu)
  have hvf : scalarProduct G (kernel d v) f = star (8 * b) :=
    (scalarProduct_conj _ _).symm.trans (congrArg star hfv)
  have hvu : scalarProduct G (kernel d v) (kernel d u) = 0 := by
    rw [← scalarProduct_conj, huv, star_zero]
  have hz : f + (-a) • kernel d u + (-b) • kernel d v = 0 := by
    apply (scalarProduct_self_eq_zero_iff _).mp
    simp only [scalarProduct_add_left, scalarProduct_add_right,
      scalarProduct_smul_left, scalarProduct_smul_right, hf, hu, hv, huv,
      hfu, hfv, huf, hvf, hvu, star_mul, star_neg, star_ofNat]
    ring
  simpa only [neg_smul, ← sub_eq_add_neg, sub_sub, sub_eq_zero] using hz

/-- A constituent of a linear combination of principal kernels lies in the
prescribed actual principal block. -/
theorem constituent_mem_of_eq (d : PrincipalCongruenceBlockData G)
    (u v : G) (a b : ℂ) (f χ : ClassFunction G)
    (hf : f = a • kernel d u + b • kernel d v)
    (hχ : IsIrreducibleCharacter χ) (hcoeff : scalarProduct G f χ ≠ 0) :
    ∃ i : d.I, i ∈ d.block ∧ ∀ g, χ g = d.chi i (ConjClasses.mk g) := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  obtain ⟨i, hi⟩ := d.complete.2.1 (characterClassFunction ρ)
    (isIrreducibleCharacter_characterClassFunction ρ hρ)
  have he : ρ.character = fun g => d.chi i (ConjClasses.mk g) := by
    funext g
    rw [hi]
    rfl
  refine ⟨i, ?_, congrFun he⟩
  by_contra hn
  apply hcoeff
  rw [hf, he, scalarProduct_add_left, scalarProduct_smul_left,
    scalarProduct_smul_left, kernel_scalar_row, kernel_scalar_row, if_neg hn]
  simp [hn]

end ModularBlock.SectionKernel
